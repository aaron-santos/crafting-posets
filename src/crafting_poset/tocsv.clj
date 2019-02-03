(ns crafting-poset.tocsv
  (:require [clojure.data.csv :as csv]
            [clojure.java.io :as io]))

(defn expand-eigen [{:keys [e] :as row}]
  (let [freq-e (map (fn [[k v]] [(int k) v]) (frequencies e))]
    (println freq-e)
    (apply assoc row
      (mapcat (fn [[i freq]] [(keyword (format "eigen_degree_%03d" i)) freq])
              freq-e))))

(defn process [data]
  (->> data
    (map expand-eigen)))

(defn -main [& args]
  (let [data (read-string (slurp "data/measures.clj"))
        data (process data)
        ks   (vec (set (mapcat keys data)))
        headers (map name ks)]
    (println ks)
    (println headers)
    (with-open [writer (io/writer "out-file.csv")]
      (csv/write-csv writer
        (cons headers
          (map (apply juxt ks) data))))))


