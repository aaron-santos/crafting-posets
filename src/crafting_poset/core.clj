(ns crafting-poset.core
  (:require clojure.set
            [clojure.core.matrix :as m]
            [clojure.core.matrix.utils :as mu]
            [clojure.core.matrix.linear :as ml]
            [clojure.core.matrix.protocols :as mp]
            [clojure.math.combinatorics :as combo]
            [clojure.data.generators :as dg]
            [clatrix.core :as cc]
            [rockpick.core :as rp]
            [loom.graph :as lg]
            [loom.alg :as la]
            [loom.alg-generic :as lag]
            [loom.label :as ll]
            [incanter.stats :as is])
  (:import [java.lang Math]
           [mikera.matrixx.decompose Eigen IEigenResult]
           [mikera.matrixx AMatrix Matrixx Matrix]
           [mikera.arrayz Arrayz INDArray Array]
           [mikera.matrixx.impl DiagonalMatrix VectorMatrixMN]
           [com.mitchtalmadge.asciidata.graph ASCIIGraph]))

(defn sync-print [& args]
    (locking *out* (apply print args)))

(defn sync-println [& args]
    (locking *out* (apply println args)))

(defn std-dev [x]
  (case (count x)
    0 0
    1 0
    (let [mean (/ (reduce + x) (count x))]
      (Math/sqrt (/ (reduce + (map (fn [x] (* (- x mean) (- x mean))) x))
                  (dec (count x)))))))

(defn rand-weighted
  [m]
   "Randomly select a value from map of {value weight}."
   (cond
     (empty? m)
       nil
     (= 1 (count m))
       (-> m first second)
     :else
       (let [[wm a]     (reduce (fn [[m a] [v weight]]
                                  [(conj m [a v]) (+ weight a)])
                                [[] 0] m)
             n          (rand a)]
         (second (last (remove (fn [[wn _]] (> wn n)) wm))))))

(defrecord Graph [adj connections])
(defn g->loom-graph [g]
  (let [{:keys [adj connections]} g
        edges (for [[[col-min col-max] [row-min row-max]] connections
                    row (range row-min row-max)
                    col (range col-min col-max)
                    :let [e (m/mget adj row col)]
                    :when (pos? e)]
                [row col])]
    (apply lg/digraph edges)))

(defn fully-connected
  "Shape is a seq of odd-valued ints"
  [shape]
  (let [rows (count shape)
        nodes (reduce + shape)
        ; empty adjacency matrix
        adj (m/mutable (m/zero-matrix nodes nodes))
        connections (let [n (reductions + shape)
                          n-offs (map vector n (rest n))
                          m (reductions + (cons 0 shape))
                          m-offs (map vector m (rest m))
                          connections (map vector n-offs m-offs)]
                      connections)]
    (doseq [[[col-min col-max] [row-min row-max]] connections]
      (doseq [row (range row-min row-max)
              col (range col-min col-max)]
        (let [layer-len (/ (+ (- col-max col-min) (- row-max row-min)) 2)
              offset (- col row layer-len)]
          (when (<= -1 offset 1)
            (m/mset! adj row col 1)))))
    (let [g (->Graph (m/immutable adj) connections)]
      g)))
       
(defn prune-crossed-edges
  [g]
  (let [{:keys [adj connections]} g
        m-adj (m/mutable adj)]
    (doseq [[[col-min col-max] [row-min row-max]] connections]
      (doseq [row (range (inc row-min) row-max)
              col (range col-min (dec col-max))]
        (let [e (m/mget m-adj row col)
              dual (m/mget m-adj (dec row) (inc col))]
          (when (and (pos? e) (pos? dual))
            (if (= (rand-int 2) 1)
              (m/mset! m-adj row col 0)
              (m/mset! m-adj (dec row) (inc col) 0))))))
    (let [g (->Graph (m/immutable m-adj) connections)]
      g)))

(defn prior-edges-transposed [adj prev-row-max prev-row-min
                              prev-col-max prev-col-min
                              row-max row-min
                              col-max col-min]
  (if prev-row-max
    (let [prev-rows (- prev-row-max prev-row-min)
          prev-cols (- prev-col-max prev-col-min)
          rows (- row-max row-min)
          cols (- col-max col-min)]
      #_(sync-println "=======")
      #_(sync-println [prev-rows prev-cols] [rows cols])
      #_(sync-println "=======")
      (cond
        (< prev-rows cols)
          ; expand prev-rows then transpose
          (let [padding-m (m/zero-matrix (int (/ (- cols prev-rows) 2))
                                         (- prev-col-max prev-col-min))]
            (m/transpose
              (m/join padding-m
                      (m/select adj (range prev-row-min prev-row-max)
                                    (range prev-col-min prev-col-max))
                      padding-m)))
        (> prev-rows cols)
          ; contract prev-rows then transpose
          (m/transpose
            (m/select adj
                      (range
                        (+ prev-row-min (int (/ (- prev-rows cols) 2)))
                        (- prev-row-max (int (/ (- prev-rows cols) 2))))
                      (range prev-col-min prev-col-max)))
        (= prev-cols rows)
          ; transpose
          (m/transpose
            (m/select adj (range prev-row-min prev-row-max)
                          (range prev-col-min prev-col-max)))
        :else
          (sync-println "prior-edges-transposed :default" [prev-rows prev-cols] [rows cols])))
    (m/zero-matrix (- row-max row-min)
                   (- col-max col-min))))

(defn prune-random-edges
  [lambda-b0 lambda-b1 lambda-b2 bernoulli-b0 g]
  (let [{:keys [adj connections]} g
        m-adj (m/mutable adj)]
    (doseq [[[[col-min col-max]
              [row-min row-max]] 
             [[prev-col-min prev-col-max]
              [prev-row-min prev-row-max]]] (map vector connections
                                              (cons nil connections))]
      (let [prior-edges (prior-edges-transposed
                              m-adj prev-row-max prev-row-min
                              prev-col-max prev-col-min
                              row-max row-min
                              col-max col-min)
            #_ (sync-println "prior-edges")
            #_ (m/pm prior-edges)
            #_ (sync-println "--------")
            #_ (sync-println (m/shape prior-edges))
            #_ (sync-println [row-min row-max] [col-min col-max])
            conns (into {} (for [row (range row-min row-max)
                                 col (range col-min col-max)
                                 :let [prior-edge (m/mget prior-edges
                                                    (- row row-min)
                                                    (- col col-min))
                                      w (if (pos? prior-edge)
                                          bernoulli-b0
                                          (- 1 bernoulli-b0))
                                      #_ (sync-println "w" w prior-edge [(- row row-min)
                                                                        (- col col-min)])]]
                             [[row col] (min 1 (max 0.01 w))]))
            width (- row-max row-min)
            rm-num (is/sample-poisson 1
                     ; l = b0 + w * b1 + w * w * b2
                     :lambda (+ lambda-b0
                                (* width
                                   lambda-b1)
                                (* width width lambda-b2)))
            ; create a matrix using the previous layer
            prior-edges (m/mutable (m/zero-matrix (- row-max row-min)
                                                  (- col-max col-min)))
            rm-conns (take rm-num (repeatedly (fn [] (rand-weighted conns))))]
      #_(sync-println "removing" rm-num " from layer" (- row-max row-min))
      #_(sync-println "weighted-cons" conns)
      #_(sync-println "rm-cons" (vec rm-conns))
      (doseq [[row col] rm-conns]
        #_(sync-println "removing" row col "from layer"(- row-max row-min)) 
        (m/mset! m-adj row col 0))))
    (let [g (->Graph (m/immutable m-adj) connections)]
      g)))

(defn retained [g]
  (let [g (g->loom-graph g)
        g-t (lg/transpose g)
        start 0
        end (dec (count (lg/nodes g)))
        reaches-start (la/bf-traverse g start)
        reaches-end (la/bf-traverse g-t end)
        ; if a node is reachable from start and end, then retain it
        bi-reachable (clojure.set/intersection
                       (set reaches-start)
                       (set reaches-end))]
    #_(sync-println "retained from start" (set reaches-start))
    #_(sync-println "retained from end" (set reaches-end))
    bi-reachable))
        
        
(defn prune-unreachable
  [g]
  (let [{:keys [adj connections]} g
        m-adj (m/mutable adj)
        retained (retained g)]
    #_(sync-println "retained" retained)
    (doseq [n (remove retained (range (m/row-count adj)))]
      #_(sync-println "removing node" n)
      (m/set-selection! m-adj n :all 0)
      (m/set-selection! m-adj :all n 0))
    (let [g (->Graph (m/immutable m-adj) connections)]
      ;(sync-println g)
      g)))

(def db32 {
  :black {:r 0 :g 0 :b 0}
  :valhalla {:r 34 :g 32 :b 52}
  :loulou {:r 69 :g 40 :b 60}
  :oiled-cedar {:r 102 :g 57 :b 49}
  :rope {:r 143 :g 86 :b 59}

  :tahiti-gold {:r 223 :g 113 :b 38}
  :twine {:r 217 :g 160 :b 102}
  :pancho {:r 238 :g 195 :b 154}
  :golden-fizz {:r 251 :g 242 :b 54}
  :atlantis {:r 153 :g 229 :b 80}

  :christi {:r 106 :g 190 :b 48}
  :elf-green {:r 55 :g 148 :b 110}
  :dell {:r 75 :g 105 :b 47}
  :verdigris {:r 82 :g 75 :b 36}
  :opal {:r 50 :g 60 :b 57}

  :deep-koamaru {:r 63 :g 63 :b 116}
  :venice-blue {:r 48 :g 96 :b 130}
  :royal-blue {:r 91 :g 110 :b 225}
  :cornflower {:r 99 :g 155 :b 255}
  :viking {:r 95 :g 205 :b 228}

  :light-steel-blue {:r 203 :g 219 :b 252}
  :white {:r 255 :g 255 :b 255}
  :heather {:r 155 :g 173 :b 183}
  :topaz {:r 132 :g 126 :b 135}
  :dim-gray {:r 105 :g 106 :b 106}

  :smokey-ash {:r 89 :g 86 :b 82}
  :clairvoyant {:r 118 :g 66 :b 138}
  :brown {:r 172 :g 50 :b 50}
  :mandy {:r 217 :g 87 :b 99}
  :plum {:r 215 :g 123 :b 186}

  :rainforest {:r 143 :g 151 :b 74}
  :stinger {:r 138 :g 111 :b 48}})

(def question-cell-type
  ; ?
  {:ch \? :fg {:r 3 :g 5 :b 5} :bg (db32 :topaz)})

(def complication-cell-type
  ; !
  {:ch \! :fg {:r 3 :g 5 :b 5} :bg (db32 :brown)})

(def remedy-cell-type
  ; +
  {:ch \+ :fg {:r 3 :g 5 :b 5} :bg (db32 :royal-blue)})

(def material-component-cell-type
  ; &
  {:ch \& :fg {:r 3 :g 5 :b 5} :bg (db32 :tahiti-gold)})

(def enhancement-cell-type
  ; ☼
  {:ch \☼ :fg {:r 3 :g 5 :b 5} :bg (db32 :christi)})

(defn ch->cell-type [ch]
  (let [m {
            \? question-cell-type
            \! complication-cell-type
            \+ remedy-cell-type
            \& material-component-cell-type
            \☼ enhancement-cell-type}]
    (assert (contains? m ch) (str ch (int ch) "not found in " m))
    (update (get m ch)
      :ch
      (fn [ch]
        (if (= ch \☼)
          (char 0xF)
          ch)))))

(def cell-type-freqs
  [complication-cell-type
   remedy-cell-type
   remedy-cell-type
   material-component-cell-type
   enhancement-cell-type])

(defn node->row
  [layers n]
  (get
    (->> layers
      (map-indexed vector)
      (mapcat (fn [[i v]] (repeat v i)))
      (map-indexed vector)
      (into {}))
    n))

(defn node->col
  [layers n]
  (get
    (->> layers
      (mapcat range)
      (map-indexed vector)
      (into {}))
    n))

(defn node-y [layers n]
  (* 2 (node->row layers n)))

(defn node-x [layers n]
  (let [row (node->row layers n)
        col (node->col layers n)
        max-nodes (reduce max layers)
        row-num-nodes (get layers row)
        x (* 2
             (+ (/ (- max-nodes row-num-nodes) 2)
                col))]
    #_(sync-println "row" row "max-nodes" max-nodes "row-num-nodes" row-num-nodes "x" x)
    (int x)))

(defn paths-contain?
  [f g source ch n]
  (f
    (fn [path]
      (contains? (set (map (fn [n] (ll/label g n)) path)) ch))
    (lag/trace-paths
      (partial lg/predecessors g)
      n)))

(defn all-paths-contain?
  [g source ch n]
  (paths-contain? every?  g source ch n))

(defn any-paths-contain?
  [g source ch n]
  (paths-contain? some  g source ch n))

(defn not-any-paths-contain?
  [g source ch n]
  (paths-contain? not-any? g source ch n))

(defn draw
  [labeled-graph layers]
  (let [max-nodes (reduce max layers)
        width (dec (* 2 (reduce max layers)))
        height (dec (* 2 (count layers)))
        c (make-array Character/TYPE height width)]
    ;(sync-println edges)
    (sync-println labeled-graph)
    ;; fill canvas with empty chars
    (doseq [row (range height)
            col (range width)]
      (aset-char c row col \space))
    ;; fill in nodes
    (doseq [[idx n] (map-indexed vector (lg/nodes labeled-graph))
            :let [label (ll/label labeled-graph n)]]
      #_(sync-println "fill node" n label layers (int (node-y layers n)) (int (node-x layers n)))
      (aset-char c
        (int (node-y layers n))
        (int (node-x layers n))
        (or label \x)))

    ;; fill edges
    (doseq [[ni nf] (lg/edges labeled-graph)]
      (let [xi (node-x layers ni)
            yi (node-y layers ni)
            xf (node-x layers nf)
            yf (node-y layers nf)]
        ;(sync-println xi yi xf yf)
        (cond
          (= xi xf)
            (aset-char c (/ (+ yi yf) 2) xi \|)
          (< xi xf)
            (aset-char c (/ (+ yi yf) 2) (/ (+ xi xf) 2) \\)
          (> xi xf)
            (aset-char c (/ (+ yi yf) 2) (/ (+ xi xf) 2) \/))))
  [(for [row c]
     (do
     (sync-println "")
     (for [ch row]
       (if (contains? #{\x \space \\ \| \/} ch)
         {:ch ch :fg {:r 255 :g 255 :b 255} :bg {:r 3 :g 5 :b 5}}
         (ch->cell-type ch)))))]))

(defn log [layers]
  (doseq [row (get layers 0)]
    (doseq [cell row]
      (sync-print (get cell :ch \o)))
    (sync-println))
  layers)

(defn write-xp
  [layers path]
  (rp/write-xp (clojure.java.io/output-stream path) layers))

;; From https://github.com/kcanderson/promising_helper/blob/e94e6be16aeb6fcc096385f6c9997cc9fe94ca30/src/promising_helper/kernels.clj
(defn ones-matrix
  "Returns an m*n matrix of all ones."
  [m n]
  (m/matrix (repeat m (repeat n 1))))

(defn diag-mat
  [diag_vals]
  (let [m (m/mutable (m/identity-matrix (count (into [] diag_vals))))]
    (doseq [[i d] (map-indexed list diag_vals)]
      (m/mset! m i i d))
    (m/immutable m)))

(defn degree-matrix
  [mat]
  (let [[m n] (m/shape mat)]
    (diag-mat (m/get-column (m/mmul mat (ones-matrix m 1)) 0))))

(defn laplacian-matrix
  [mat]
  (->
    (degree-matrix mat)
    m/mutable
    (m/sub! mat)
    m/matrix))


;def findsubsets(S,m):
;    return set(itertools.combinations(S, m))

(defn find-subsets [S m]
  (set (combo/combinations (vec S) m)))

(defn boundary-length [g a-set]
  ; nodes in g that are connected to a-set and not in a-set
  (->> a-set
      ;; boundary nodes for each node in a-set
      (mapcat (fn [n] (clojure.set/union
                        (map first (lg/in-edges g n))
                        (map second (lg/out-edges g n)))))
      ;; unique
      set
      ;; count
      count))

(defn cheeger [g]
  (sync-println "cheeger")
  (let [nodes (lg/nodes g)
        num-nodes (count nodes)]
    (reduce min
            (Math/pow num-nodes 2)
            (for [subset-size (range (/ num-nodes 2))
                  :let [possible-a-sets (take 50 (find-subsets (lg/nodes g) (inc subset-size)))]
                  a-set possible-a-sets]
              (/ (boundary-length g a-set) (inc subset-size))))))

(defn simple-cycles [g]
  #_(sync-println "simple-cycles mst")
  (let [g (lg/graph g)
        mst (la/prim-mst g)
        extra-edges (clojure.set/difference
                      (set (lg/edges g))
                      (set (lg/edges mst)))]
    #_(sync-println "finding cycles")
    ;(sync-println mst)
    ;(sync-println (set (lg/edges mst)))
    ;(sync-println (set (lg/edges g)))
    ;(sync-println extra-edges)
    (->> extra-edges
      (take 40)
      (map (fn [[start end]] (la/shortest-path mst start end))))))

(defn circumference [simple-cycles]
  #_(sync-println "circumference")
  (->> simple-cycles
    (map count)
    (reduce max 0)))

(defn girth [simple-cycles]
  #_(sync-println "girth")
  (->> simple-cycles
    (map count)
    (reduce min 0)))

(defn diameter [g]
  #_(sync-println "diameter")
  (->> (-> g lg/nodes)
    (take 20)
    ;; foreach node, calculate longest shortest path
    (map (partial la/longest-shortest-path g))
    ;; for each path, find length
    (map count)
    ;; diameter is max length
    (reduce max 0)))

(defn expand-eigen [{:keys [e] :as row}]
  (let [freq-e (map (fn [[k v]] [(int k) v]) (frequencies e))]
    (apply assoc row
      (mapcat (fn [[i freq]] [(keyword (format "eigen_degree_%03d" i)) freq])
              freq-e))))

(defn measure [g]
  (let [{:keys [adj connections]} g
        g (g->loom-graph g)
        lm (laplacian-matrix adj)
        ccm (cc/matrix lm)
        e  (cc/eigen ccm)
        ss (simple-cycles g)]
    (expand-eigen
      {:e
        (-> e
          :values)
       :num-nodes (count (lg/nodes g))
       :num-edges (count (lg/edges g))
       :circumference (circumference ss)
       :girth (girth ss)
       :diameter (diameter g)
       #_#_:cheeger (float (cheeger g))})))
  

(defn gen-graph [layers [lambda-b0 lambda-b1 lambda-b2 bernoulli-b0] write-xp? progress i]
  (try
    #_(sync-println (float (* 100 (/ progress (count parameters)))) "%")
    (let [g (-> layers
            fully-connected
            prune-crossed-edges
            ((partial prune-random-edges lambda-b0 lambda-b1 lambda-b2 bernoulli-b0))
            #_log
            prune-unreachable)
          path (str "data/params-"
                    (format "%02.2f" (float lambda-b0))
                    "-"
                    (format "%02.2f" (float lambda-b1))
                    "-"
                    (format "%02.2f" (float lambda-b2))
                    "-"
                    (format "%02.2f" (float bernoulli-b0))
                    "-"
                    i)]
      #_(sync-println lambda-b0 lambda-b1 lambda-b2 i)
      (when write-xp?
        #_(sync-println "writing" (str path ".xp"))
        (-> g
          (draw layers)
          log
          (write-xp (str path ".xp"))))
      (-> g
        measure
        (assoc :g g
               :lambda-b0 lambda-b0
               :lambda-b1 lambda-b1
               :lambda-b2 lambda-b2
               :bernoulli-b0 bernoulli-b0
               :i i)))
      (catch Exception e (sync-println e))))

(defn color-paths-once
  ([g] (color-paths-once
         (lag/trace-paths
           (partial lg/predecessors g)
           (reduce max 0 (lg/nodes g)))
         (clojure.set/difference
           (set (lg/nodes g))
           (set (cons (reduce max (lg/nodes g))
                      (take 4 (sort (lg/nodes g))))))
         #{}))
  ([remaining-paths potential-nodes colored-nodes]
    #_(sync-println "remaining-paths" remaining-paths)
    (let [potential-nodes (shuffle (vec potential-nodes))]
      ;; any remaining paths?
      (if (seq remaining-paths)
        ; any remaining nodes?
        (if (seq potential-nodes)
          ;; pick a node
          (loop [selected-node (first potential-nodes)
                 remaining-nodes (next potential-nodes)]
                  ;; partition remining-paths into those that contain the new node
                  ;; and those that do not
            (when selected-node
              #_(sync-println "selected-node" selected-node)
              ;; partition remaining paths into paths containing selected node
              ;; and paths not containing selected node
              (let [path-groups (group-by (fn [path] (contains? (set path) selected-node))
                                          remaining-paths)
                    paths-containing-node (get path-groups true)
                    paths-without-node (get path-groups false)
                    nodes-covered-by-new-paths (set (mapcat identity paths-containing-node))
                    next-potential-nodes (set (clojure.set/difference
                                            (set potential-nodes)
                                            nodes-covered-by-new-paths))
                    #_ (sync-println "nodes-covered-by-new-paths" nodes-covered-by-new-paths)
                    #_ (sync-println "next-potential-nodes" next-potential-nodes)
                    result (color-paths-once 
                             paths-without-node
                             (shuffle (vec next-potential-nodes))
                             (conj colored-nodes selected-node))]
                    (if result
                      result
                      (recur (first remaining-nodes) (next remaining-nodes))))))
          ;; remaining paths but no potential nodes
          (do
            #_(sync-println "backtracking")
            nil))
        ;; no remaining paths. return colored nodes
        colored-nodes))))

(defn next-type
  [types g n & more]
  (let [preds (lg/predecessors g n)
        parent-types (clojure.set/union
                       (set more)
                       ; parent labels
                       (set (map (partial ll/label g)
                                 preds)))]
    #_(sync-println n "parents" preds)
    #_(sync-println n "parent-labels" parent-types)
    (when (< (count parent-types) 4)
      (loop [c (first @types)]
        (swap! types rest)
        (if (contains? parent-types c)
          (recur (first @types))
          c)))))

(defn label-graph [g] 
  (let [selected-nodes (color-paths-once g)
        min-node (reduce min (lg/nodes g))
        num-nodes (count (lg/nodes g))
        ; ? is always first.
        ; have an even mix of types after that
        types (atom (cycle (mapcat shuffle (repeat (map :ch cell-type-freqs)))))
        labeled-graph (reduce (fn [g n]
                        #_(sync-println n "selected-node?" (contains? selected-nodes n))
                        (cond
                          ; root, \?
                          (= n min-node)
                            (do
                              #_(sync-println "labeling root node ?")
                              (ll/add-label g n \?))
                          ; selected, \?
                          (contains? selected-nodes n)
                            (do
                              #_(sync-println "labeling selected-node" n)
                              (ll/add-label g n \?))
                          ; if paths to root contains \! but not \+
                          (and
                            (all-paths-contain? g min-node \! n)
                            (not-any-paths-contain? g min-node \+ n))
                            (do
                              #_(sync-println "labeling ! descendant node" n)
                              (ll/add-label g n (next-type types g n)))
                          :else
                            ; else, label, but not \+
                            (do
                              #_(sync-println "labeling" n)
                              (ll/add-label g n (next-type types g n \+)))))
                        g
                        (lg/nodes g))]
    (sync-println "label-graph selected-nodes" selected-nodes)
    labeled-graph))

(defn gen-graph-curate [layers
                        [lambda-b0 lambda-b1 lambda-b2 bernoulli-b0 :as params]
                        write-xp? progress i]
  (letfn [(gg [] (gen-graph layers params false progress i))]
    (loop [g (gg) j 0 k 0]

      ; select graph
      (if (and (< k 50)
               (< (* 1.5 (count layers)) (get g :num-nodes 0) (* 0.8 (reduce + layers)))
               ; make sure the last node has at least 2 connections
               (< 1 (reduce + (take-last 4 (get g :e))) 4)
               ; make sure there are enough decision points
               (< 3 (reduce + (filter #(< 1 %) (get g :e)))))
        (let [loom-graph (g->loom-graph (get g :g))
              labeled-graph (label-graph loom-graph)
              question-nodes (filter (fn [n] (= (ll/label labeled-graph n) \?))
                                     (lg/nodes labeled-graph))
              node-labels (map (fn [n] (ll/label labeled-graph n))
                                (sort (vec (lg/nodes labeled-graph))))
              node-freqs (frequencies
                           node-labels)]

          (sync-println "i" i "j" j "k" k)
          (sync-println "question-nodes" question-nodes)
          #_(sync-println "min-question" (reduce min question-nodes))
          #_(sync-println "max-question" (reduce max question-nodes))
          #_(sync-println "sum-question" (reduce + 0 question-nodes))
          #_(sync-println "max-nodes" (* 0.8 (reduce + layers)))
     
          #_(log (draw labeled-graph layers))

          ;; select coloring
          (if (and
                ;; no nil labels
                (not-any? nil? node-labels)
                ;; question node count and dispersion
                (or (= 1 (count question-nodes))
                    (< 1 (std-dev (map (partial node-y layers)
                                       (rest (sort question-nodes))))))
                ;; question node toward top
                (< (/ (reduce + 0 question-nodes)
                      (count question-nodes))
                   (* 0.5 (count node-labels)))
                ;; at least one of each node type present
                (< 4 (count (keys node-freqs)))
                ;; not too many siblings of same type
                (< (reduce +
                     ; count of duplicate children for each node
                     (mapcat (fn [n]
                               ; how many duplicate children for node n
                               (let [children-labels (cons (ll/label labeled-graph n)
                                                           (map (partial ll/label labeled-graph)
                                                             (lg/successors loom-graph n)))]
                                 (remove (partial = 1)
                                         (vals (frequencies children-labels)))))
                             (lg/nodes labeled-graph)))
                   (* 0.15 (count node-labels))))
            (let [path (str "data/params-"
                            (format "%02.2f" (float lambda-b0))
                            "-"
                            (format "%02.2f" (float lambda-b1))
                            "-"
                            (format "%02.2f" (float lambda-b2))
                            "-"
                            (format "%02.2f" (float bernoulli-b0))
                            "-"
                            i
                            "-"
                            j
                            "-"
                            k)]
              (-> labeled-graph
                (draw layers)
                (write-xp (str path ".xp")))
              g)
            (recur g j (inc k))))
        (recur (gg) (inc j) 0)))))

(defn descent [f xs error rate epochs]
  (let [ns (range (count xs))
        r (/ rate error 2)]        
    (letfn [(delta [ys i e] (into [] (map (fn [j y] (if (= i j) (+ y e) y))
                                          ns ys)))
            (step [ys]
              (into [] (map (fn [i y] (- y (* r (- (f (delta ys i error))
                                                   (f (delta ys i (- error)))))))
                            ns ys)))
            (norm [ys] (Math/sqrt (reduce (fn [u v] (+ u (* v v))) 0 ys)))]
      (loop [ys xs
             m 0]
        (let [zs (step ys)]
          ;; (if (= 0 (mod m 20)) (println zs))
          (if (or (> m epochs)
                  (< (norm (map - zs ys)) error))
            ys
            (recur zs (inc m))))))))

(defn logistic [x]
  (/ 1 (inc (Math/pow Math/E (- x)))))
(defn constrain-params
  [[lambda-b0 lambda-b1 lambda-b2 bernoulli-b0]]
  [lambda-b0
   lambda-b1
   lambda-b2
   (logistic bernoulli-b0)])

(defn mean [xs] (float (/ (reduce + xs) (count xs))))

(defn split-n [n xs]
  (->> xs
    (map-indexed
       (fn [i x]
        [(int (* n (/ i (count xs)))) x]))
    (partition-by first)
    (map (partial map second))))

(defn print-losses [losses]
  (let [xs (split-n 30 losses)]
    (println (.plot (.withNumRows
                        (ASCIIGraph/fromSeries
                          (double-array
                            (map mean xs)))
                      20)))))

(defn -main [& args]
  (m/set-current-implementation :vectorz)
  (let [layers #_[1 3 3 1]
               [1 3 5 5 5 3 1]
               #_[1 3 5 7 9 11 13 15 17 19 21 21 21 21 21 21 21 19 17 15 13 11 9 7 5 3 1]
        max-nodes (reduce + layers)
        max-edges (reduce + (map (fn [l0 l1] (max l0 l1) * 2 - 1) layers (cons 0 layers)))
        min-nodes (count layers)
        min-edges (count layers)]

    ; write single graph
    (doseq [i (range 100)]
      (gen-graph-curate layers [0.15 0.16 0.30 0.464] true 0 i))

    ; grid search
    #_(let [parameters (for [lambda-b0 (range -10 10 1)
                           lambda-b1 (range -10 10 1)
                           lambda-b2 (range -10 10 1)
                           bernoulli-b0 (range 0.1 0.9 0.1)
                           i (range 20)]
                       [lambda-b0 lambda-b1 lambda-b2 bernoulli-b0 i])
          ;; grid search of parameters
          measures (doall
                     (pmap (partial gen-graph layers)
                           parameters (range)))]
      (spit "data/measures.clj" (vec measures)))
    (println "max-nodes" max-nodes)
    (println "min-nodes" min-nodes)
    (println "min-edges" min-edges)

    ; SGD
    #_(let [losses (atom [])
          sq (fn [x] (* x x))
          lambda-r2 2
          loss-fn (fn [data params]
                    (let [params (constrain-params params)
                          [lambda-b0 lambda-b1 lambda-b2] params]
                    (float
                      (/ (reduce + (map (fn [{:keys [circumference
                                                     diameter
                                                     num-nodes
                                                     num-edges
                                                     eigen_degree_000
                                                     eigen_degree_001
                                                     eigen_degree_002
                                                     eigen_degree_003] :as m}]
                                   #_(sync-println "num-nodes" num-nodes)
                                   ;; this value is minimized
                                   (+ (+
                                      (reduce +
                                        (map (fn [b] (* b (sq lambda-r2)))
                                              [lambda-b0
                                               lambda-b1
                                               lambda-b2]))
                                      (- (or eigen_degree_002 0))
                                      (- diameter)
                                      (* 4 (sq (- num-nodes (/ max-nodes 2)))))))
                                   data))
                         (count data)))))
          errfn (fn [params]
                  (let [data (pmap (partial gen-graph layers params false 0)
                                   (range 500))
                          loss (loss-fn data params)]
                    (print "\033[2J")
                    (print "\033[H")
                    (sync-println "params" params)
                    (sync-println "loss" (float loss))
                    (swap! losses conj loss)
                    (sync-println "epoch" (count @losses))
                    (print-losses @losses)
                    loss))
            ;; errorfn initial-params error rate epocs
           params (descent errfn [0.2 0.4 0.5 0.7] 0.005 0.00001 100)
           _ (sync-println "final params" params)
           _ (sync-println "final constrained params" (constrain-params params))
           measures (doall (pmap (partial gen-graph layers (constrain-params params) true 0)
                                 (range 100)))]
    (println "loss components")
    (println "max-nodes" max-nodes)
    (println "diameter" (mean (map :diameter measures)))
    (println "num-nodes"
             (mean (map (fn [{:keys [num-nodes]}] (* 4 (sq (- num-nodes (/ max-nodes 2)))))
                        measures)))
    (spit "data/measures.clj" (vec measures)))))

