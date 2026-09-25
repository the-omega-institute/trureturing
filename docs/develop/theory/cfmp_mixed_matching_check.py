#!/usr/bin/env python3
"""Supplementary finite checks for the CFMP mixed-matching continuation.

Python 3, standard library only. This checks an explicit face-pairing packet,
not the general analytic theorem and not full CFMP. No Lean/CI claim is made.
Edges use the theory owner's order (01,02,03,23,13,12), with zero-based vertices.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import permutations
import json
import math

EDGES = ((0, 1), (0, 2), (0, 3), (2, 3), (1, 3), (1, 2))
INDEX = {edge: i for i, edge in enumerate(EDGES)}
ROWS = (
    (0, 2, 1, 3, '0132'), (1, 2, 2, 2, '1023'),
    (2, 3, 3, 2, '0132'), (3, 3, 4, 3, '1023'),
    (4, 2, 5, 2, '1023'), (5, 3, 0, 3, '1023'),
    (0, 0, 6, 3, '3201'), (6, 2, 7, 3, '0132'),
    (7, 2, 8, 3, '0132'), (8, 2, 9, 3, '0132'),
    (9, 2, 10, 2, '1023'), (10, 3, 0, 1, '3201'),
    (1, 0, 3, 0, '0132'), (3, 1, 5, 1, '0132'),
    (5, 0, 9, 1, '1023'), (9, 0, 2, 1, '1023'),
    (2, 0, 10, 0, '0132'), (10, 1, 8, 1, '0132'),
    (8, 0, 4, 1, '1023'), (4, 0, 6, 1, '1023'),
    (6, 0, 7, 1, '1023'), (7, 0, 1, 1, '1023'),
)

class DSU:
    def __init__(self, size):
        self.parent = list(range(size))
    def find(self, x):
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x
    def union(self, x, y):
        self.parent[self.find(x)] = self.find(y)
    def groups(self):
        groups = defaultdict(list)
        for x in range(len(self.parent)):
            groups[self.find(x)].append(x)
        return sorted(groups.values(), key=lambda group: group[0])

def color(tet, edge):
    if edge == (0, 1):
        return 'R'
    if edge == (2, 3):
        return 'R' if tet == 0 else 'S'
    return 'T'

def raw_cosines(values):
    x = {edge: values[i] for i, edge in enumerate(EDGES)}
    def get(a, b):
        return x[tuple(sorted((a, b)))]
    result = []
    for i, j in EDGES:
        k, h = [v for v in range(4) if v not in (i, j)]
        r, a, b, o, c, d = (get(i,j), get(i,k), get(i,h),
                             get(k,h), get(j,h), get(j,k))
        numerator = a*b+c*d+r*a*c+r*b*d-(r*r-1)*o
        denominator = math.sqrt((2*r*a*d+r*r+a*a+d*d-1)*
                                (2*r*b*c+r*r+b*b+c*c-1))
        result.append(numerator/denominator)
    return result

def check_packet():
    face = {}
    edges, vertices, ends, dual = DSU(66), DSU(44), DSU(132), DSU(11)
    for t, f, u, g, word in ROWS:
        p = tuple(map(int, word))
        assert sorted(p) == list(range(4)) and p[f] == g
        assert sum(p[i] > p[j] for i in range(4) for j in range(i+1,4)) % 2 == 1
        assert (t,f) != (u,g) and (t,f) not in face and (u,g) not in face
        inv = tuple(p.index(i) for i in range(4))
        face[t,f] = (u,g,p)
        face[u,g] = (t,f,inv)
        dual.union(t,u)
        for a in range(4):
            if a != f:
                vertices.union(4*t+a,4*u+p[a])
        for edge in EDGES:
            a,b = edge
            if f in edge:
                continue
            target = tuple(sorted((p[a],p[b])))
            assert color(t,edge) == color(u,target)
            j,k = 6*t+INDEX[edge],6*u+INDEX[target]
            edges.union(j,k)
            for end in (0,1):
                ends.union(2*j+end,2*k+(end ^ (p[a] > p[b])))
    assert len(face) == 44 and len(dual.groups()) == 1
    groups = edges.groups()
    assert sorted(map(len,groups)) == [6,6,10,22,22]
    assert len(ends.groups()) == 2*len(groups)
    assert all(ends.find(2*j) != ends.find(2*j+1) for j in range(66))
    reports = []
    angles = {}
    for group in groups:
        colors = {color(j//6,EDGES[j%6]) for j in group}
        assert len(colors) == 1
        label = next(iter(colors))
        nc = sum(j//6 == 0 for j in group)
        nd = len(group)-nc
        assert (nc,nd) == {'R':(1,5),'T':(2,20),'S':(0,10)}[label]
        # Follow the actual face maps around a normal circle, transporting
        # the ordered endpoints; closure must occur after exactly the degree.
        t,j = divmod(group[0],6)
        a,b = EDGES[j]
        entry = min(v for v in range(4) if v not in (a,b))
        start = (t,a,b,entry)
        state, seen, circle = start, set(), []
        while state not in seen:
            seen.add(state)
            t,a,b,entry = state
            circle.append(6*t+INDEX[tuple(sorted((a,b)))])
            outgoing = next(v for v in range(4) if v not in (a,b,entry))
            u,g,p = face[t,outgoing]
            state = (u,p[a],p[b],g)
        assert state == start and len(circle) == len(group)
        assert sorted(circle) == group
        for j in group:
            angles[j] = Fraction(2,len(group))
        reports.append({'color':label,'degree':len(group),'C':nc,'D':nd,
                        'normal_circle':circle})
    # Exact normalized strict angle assignment: 2/degree on each occurrence.
    maximum_corner = Fraction(0)
    for t in range(11):
        for v in range(4):
            total = sum(angles[6*t+j] for j,e in enumerate(EDGES) if v in e)
            assert 0 < total < 1
            maximum_corner = max(maximum_corner,total)
    vgroups = vertices.groups()
    assert len(vgroups) == 1 and len(vgroups[0]) == 44
    link_vertices = set()
    for tv in vgroups[0]:
        t,a = divmod(tv,4)
        for b in range(4):
            if b != a:
                e = tuple(sorted((a,b)))
                link_vertices.add(ends.find(2*(6*t+INDEX[e])+(a>b)))
    F,E,V = 44,66,len(link_vertices)
    assert (V,E,F) == (10,66,44)
    assert V-E+F == -12
    # Link-vertex fans are exactly the oriented endpoint normal circles
    # already checked, so Euler characteristic is not the sole surface test.
    return {'tetrahedra':11,'face_pairs':22,'edges':reports,
            'vertex_links':[{'V':V,'E':E,'F':F,'chi':-12,'genus':7}],
            'max_normalized_corner':str(maximum_corner)}

def check_local_star():
    theta = math.pi/5
    q = 18.0
    flat = (2.0,3.0,3.0,37.0,3.0,3.0)
    s = q-(q+1)*math.cos(theta)
    genuine = (2.0,3.0,3.0,s,3.0,3.0)
    assert s > 1
    flat_cos, true_cos = raw_cosines(flat), raw_cosines(genuine)
    assert abs(flat_cos[0]+1) < 1e-12 and abs(flat_cos[3]+1) < 1e-12
    assert all(abs(flat_cos[i]-1) < 1e-12 for i in (1,2,4,5))
    assert all(-1 < c < 1 for c in true_cos)
    angles = [math.acos(c) for c in true_cos]
    assert abs(angles[0]-theta) < 1e-12
    assert abs(math.pi+5*angles[0]-2*math.pi) < 1e-12
    for v in range(4):
        assert sum(angles[j] for j,e in enumerate(EDGES) if v in e) < math.pi
    return {'degree':6,'flat_occurrences':1,'genuine_occurrences':5,
            's':s,'central_angle_residual':math.pi+5*angles[0]-2*math.pi}

if __name__ == '__main__':
    print(json.dumps({'packet':check_packet(),'local_star':check_local_star()},indent=2))
