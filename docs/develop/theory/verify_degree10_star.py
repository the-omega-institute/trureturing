import itertools
from collections import defaultdict

n = 16
V = range(4)
edges = list(itertools.combinations(V, 2))
edge_index = {e: i for i, e in enumerate(edges)}
rows = [
(0,1,8,1,'0123'),(0,2,4,2,'0123'),(0,3,2,3,'0123'),
(1,1,9,1,'0123'),(1,2,5,2,'0123'),(1,3,3,3,'0123'),
(2,1,10,1,'0123'),(2,2,6,2,'0123'),(3,1,11,1,'0123'),
(3,2,7,2,'0123'),(4,1,12,1,'0123'),(4,3,7,3,'0123'),
(5,1,13,1,'0123'),(5,3,6,3,'0123'),(6,1,14,1,'0123'),
(7,1,15,1,'0123'),(8,2,13,2,'0123'),(8,3,11,3,'0123'),
(9,2,12,2,'0123'),(9,3,10,3,'0123'),(10,2,15,2,'0123'),
(11,2,14,2,'0123'),(12,3,14,3,'0123'),(13,3,15,3,'0123'),
(0,0,3,0,'0231'),(5,0,6,0,'0312'),(14,0,10,0,'0231'),
(13,0,12,0,'0321'),(2,0,7,0,'0231'),(9,0,8,0,'0132'),
(15,0,4,0,'0213'),(11,0,1,0,'0321')]
rows = [(t,f,u,g,tuple(map(int,p))) for t,f,u,g,p in rows]

class DSU:
    def __init__(self, m): self.p = list(range(m))
    def find(self, x):
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x
    def union(self, a, b): self.p[self.find(a)] = self.find(b)
    def classes(self):
        out = defaultdict(list)
        for x in range(len(self.p)): out[self.find(x)].append(x)
        return list(out.values())

def parity(p):
    return (-1) ** sum(p[i] > p[j] for i in V for j in V if i < j)

edge = DSU(6*n)
directed = DSU(12*n)
vertex = DSU(4*n)
tetra = DSU(n)
pair = {}
orientation = [None] * n
orientation[0] = 1
for t,f,u,g,p in rows:
    assert (t,f) not in pair and (u,g) not in pair
    assert p[f] == g
    inv = tuple(p.index(i) for i in V)
    pair[t,f] = (u,p); pair[u,g] = (t,inv)
    tetra.union(t,u)
    rel = -parity(p)
    if orientation[t] is None and orientation[u] is None: orientation[t] = 1
    if orientation[t] is None: orientation[t] = rel * orientation[u]
    if orientation[u] is None: orientation[u] = rel * orientation[t]
    assert orientation[u] == rel * orientation[t]
    for v in V:
        if v != f: vertex.union(4*t+v, 4*u+p[v])
    for i,(a,b) in enumerate(edges):
        if f not in (a,b):
            c,d = p[a],p[b]
            j = edge_index[tuple(sorted((c,d)))]
            edge.union(6*t+i, 6*u+j)
            reverse = int(c > d)
            for end in (0,1):
                directed.union(12*t+2*i+end, 12*u+2*j+(end ^ reverse))
assert len(pair) == 4*n and len(tetra.classes()) == 1
classes = edge.classes()
assert sorted(map(len,classes)) == [8,8,8,8,8,8,10,38]
low = {x for c in classes if len(c) == 8 for x in c}
assert all({i for i in range(6) if 6*t+i in low} == {0,1,2} for t in range(n))

# Every degree-ten occurrence has a degree-38 neighbour and a degree-eight opposite.
class_of = {x: c for c in classes for x in c}
for t in range(n):
    for i,(a,b) in enumerate(edges):
        if len(class_of[6*t+i]) != 10: continue
        neigh = [j for j,(c,d) in enumerate(edges)
                 if j != i and set((a,b)) & set((c,d))]
        opposite = next(j for j,(c,d) in enumerate(edges)
                        if not set((a,b)) & set((c,d)))
        assert len(class_of[6*t+opposite]) == 8
        assert any(len(class_of[6*t+j]) == 38 for j in neigh)

# Every edge link is one circle, and no local edge is identified with reversal.
for block in classes:
    assert all(directed.find(2*k) != directed.find(2*k+1) for k in block)
    t,i = divmod(min(block),6)
    ab = edges[i]; f = min(set(V)-set(ab)); start = (t,ab,f)
    state = start; cycle = []
    while True:
        t,ab,f = state
        cycle.append(6*t+edge_index[tuple(sorted(ab))])
        u,p = pair[t,f]
        cd = tuple(p[v] for v in ab)
        ff = next(v for v in V if v not in cd and v != p[f])
        state = (u,cd,ff)
        if (u,set(cd),ff) == (start[0],set(start[1]),start[2]): break
        assert len(cycle) <= len(block)
    assert sorted(cycle) == sorted(block)

links = []
for block in vertex.classes():
    link_vertices = set()
    for tv in block:
        t,v = divmod(tv,4)
        for i,(a,b) in enumerate(edges):
            if v in (a,b):
                link_vertices.add(directed.find(12*t+2*i+int(v == b)))
    F,W = len(block),len(link_vertices)
    links.append((F,W,W-F//2))
assert sorted(links) == [(16,6,-2),(48,10,-14)]
print('PASS: oriented manifold, circular edge links, degree-ten incidence')
print('degrees =', sorted(map(len,classes)))
print('vertex links (F,V,chi) =', sorted(links))
