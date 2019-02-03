from graphviz import Digraph
import numpy as np
import funcy
import random
from enum import Enum

# number of nodes in each layer
# must be odd
shape = [1, 3, 5, 5, 5, 5, 3, 1]
rows = len(shape)
nodes = sum(shape)

adj = np.zeros((nodes, nodes), np.bool)

n = list(funcy.sums(shape))
print(n)
n_offs = list(funcy.pairwise(n))
print(n_offs)

m = list(funcy.sums([0] + shape))
print(m)
m_offs = list(funcy.pairwise(m))
print(m_offs)

conns = list(zip(n_offs, m_offs))
print(conns)

for ((col_min, col_max), (row_min, row_max)) in conns:
    # Fully connect to next layer
    for row in range(row_min, row_max):
        for col in range(col_min, col_max):
            layer_len = ((col_max - col_min) + (row_max - row_min)) / 2
            off = col - row - layer_len

            if -1 <= off and off <= 1:
                adj[row, col] = True

    # Prune out crossed edges
    for row in range(row_min + 1, row_max):
        for col in range(col_min, col_max - 1):
            e = adj[row, col]
            dual = adj[row - 1, col + 1]
            # edges crossed?
            if e and dual:
                if random.randint(0, 1) == 0:
                    adj[row, col] = False
                else:
                    adj[row - 1, col + 1] = False
    # Prune out at least one edge from each layer
    conns = []
    for row in range(row_min + 1, row_max):
        for col in range(col_min, col_max - 1):
            if adj[row, col]:
                conns.append((row, col))
    random.shuffle(conns)
    for i in range(0, len(conns)):
        if i < 2:
            (row, col) = conns[i]
            adj[row, col] = False

def mark(visited, adj, n, end):
    print('mark', n)
    if n == end:
        visited[n] = True
        return True
    else:
        row = adj[n, :]
        reaches_end = False
        for col, e in enumerate(row):
            if e:
                reaches_end = mark(visited, adj, col, end) or reaches_end
        if reaches_end:
            visited[n] = True
        return reaches_end

def prune(adj):
    visited = {n: False for n in range(adj.shape[0])}
    mark(visited, adj, 0, adj.shape[0] - 1)
    print(visited)
    return [k for k, v in visited.items() if v == True]

retained = prune(adj)

print(adj.astype(int))

dot = Digraph(comment='poset')

for row in range(0, nodes):
    s = str(row)
    color = 'lightgrey'
    if row in retained:
        color='white'
        n = dot.node(s, s, style='filled', color=color)


for adj_row in range(0, nodes):
    for adj_col in range(0, nodes):
        s_from = str(adj_row)
        s_to = str(adj_col)
        if adj[adj_row, adj_col] and adj_row in retained and adj_col in retained:
            dot.edge(s_from, s_to)

dot.render('poset.gv', view=True)



