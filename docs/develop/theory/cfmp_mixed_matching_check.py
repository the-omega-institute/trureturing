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

ROWS22 = (
    (0, 2, 2, 3, '1032'),
    (2, 2, 3, 2, '0123'),
    (3, 3, 4, 2, '1032'),
    (4, 3, 5, 3, '0123'),
    (5, 2, 6, 2, '0123'),
    (6, 3, 0, 3, '0123'),
    (0, 1, 7, 3, '2301'),
    (7, 2, 8, 2, '0123'),
    (8, 3, 9, 3, '0123'),
    (9, 2, 10, 2, '0123'),
    (10, 3, 11, 3, '0123'),
    (11, 2, 0, 0, '2301'),
    (1, 2, 12, 2, '0123'),
    (12, 3, 13, 2, '1032'),
    (13, 3, 14, 2, '1032'),
    (14, 3, 15, 2, '1032'),
    (15, 3, 16, 2, '1032'),
    (16, 3, 1, 3, '0123'),
    (1, 1, 17, 3, '2301'),
    (17, 2, 18, 3, '1032'),
    (18, 2, 19, 2, '0123'),
    (19, 3, 20, 3, '0123'),
    (20, 2, 21, 2, '0123'),
    (21, 3, 1, 0, '3210'),
    (19, 1, 7, 0, '1032'),
    (7, 1, 14, 1, '0123'),
    (14, 0, 11, 1, '1032'),
    (11, 0, 17, 1, '1032'),
    (17, 0, 20, 1, '1032'),
    (20, 0, 3, 1, '1032'),
    (3, 0, 18, 1, '1032'),
    (18, 0, 12, 0, '0123'),
    (12, 1, 9, 1, '0123'),
    (9, 0, 5, 1, '1032'),
    (5, 0, 6, 1, '1032'),
    (6, 0, 16, 0, '0123'),
    (16, 1, 4, 0, '1032'),
    (4, 1, 21, 1, '0123'),
    (21, 0, 2, 0, '0123'),
    (2, 1, 10, 1, '0123'),
    (10, 0, 13, 0, '0123'),
    (13, 1, 8, 0, '1032'),
    (8, 1, 15, 1, '0123'),
    (15, 0, 19, 0, '0123'),
)


# Sections 70--74: these checks supplement the written proofs.
# The inverse formula uses VERTEX triples, unlike the forward formula.
def inverse_cosh_lengths(alpha):
    def get(a, b):
        return alpha[INDEX[tuple(sorted((a,b)))]]
    result = []
    for i,j in EDGES:
        k,h = [v for v in range(4) if v not in (i,j)]
        th,a,b,g,c,d = (get(i,j),get(i,k),get(i,h),
                        get(k,h),get(j,h),get(j,k))
        z = math.cos(th)
        ca,cb,cg,cc,cd = map(math.cos,(a,b,g,c,d))
        di = z*z+ca*ca+cb*cb+2*z*ca*cb-1
        dj = z*z+cc*cc+cd*cd+2*z*cc*cd-1
        assert di > 0 and dj > 0
        numerator = (math.sin(th)**2*cg+ca*cd+cb*cc
                     +z*(ca*cc+cb*cd))
        result.append(numerator/math.sqrt(di*dj))
    return result

def check_analytic_continuation():
    import random
    r = random.Random(260926)
    max_roundtrip = 0.0
    caps = 0
    windows = 0
    b2 = Fraction(109,25)**2/(Fraction(243,125)*Fraction(117,100))
    assert b2 == Fraction(237620,28431) and 9*28431-237620 == 18259
    assert b2 < 9
    for _ in range(2000):
        angles = [r.uniform(.025,.75) for j in EDGES]
        assert all(sum(angles[j] for j,e in enumerate(EDGES) if v in e)
                   < math.pi for v in range(4))
        lengths = inverse_cosh_lengths(angles)
        forward = raw_cosines(lengths)
        for j,(i,k) in enumerate(EDGES):
            max_roundtrip = max(max_roundtrip,abs(forward[j]-math.cos(angles[j])))
            si = sum(angles[n] for n,e in enumerate(EDGES) if i in e)
            sk = sum(angles[n] for n,e in enumerate(EDGES) if k in e)
            if si <= math.pi/2 and sk <= math.pi/2:
                bound = math.cosh(math.asinh(math.tan(si/2))
                                  +math.asinh(math.tan(sk/2)))
                assert lengths[j] < bound
                caps += 1
    assert max_roundtrip < 1e-10
    for _ in range(1000):
        angles = [r.uniform(.015,math.pi/5) for j in EDGES]
        # Target 01, its neighbour 24 is the only possibly medium angle.
        angles[4] = r.uniform(.015,math.pi/3)
        # The opposite angle has no bound in the theorem; retain genuineness.
        opposite_cap = math.pi-max(angles[1]+angles[5],angles[2]+angles[4])
        angles[3] = r.uniform(.015,opposite_cap-.015)
        x = inverse_cosh_lengths(angles)
        assert x[0] < math.sqrt(float(b2))
        windows += 1
    sharp = []
    for sigma in (math.pi/3,math.pi/2):
        target = (3-math.cos(sigma))/(1+math.cos(sigma))
        errors = []
        for eps in (.01,.001,.0001):
            x = inverse_cosh_lengths([sigma-2*eps,eps,eps,eps,eps,eps])[0]
            assert x < target
            errors.append(target-x)
        assert errors[2] < errors[1] < errors[0]
        sharp.append(errors)
    # Finite arithmetic cross-check only; the unbounded divisibility proof
    # is in the theory. Do not interpret this loop as a proof of all integers.
    parity_checks = 0
    for v in range(5,80,2):
        for p in range(2,80,2):
            q = p*v//2
            if (p+q)%2 == 0:
                assert p%4 == 0
                assert Fraction(2,q) <= Fraction(1,v)
                parity_checks += 1
    return {'roundtrip_max':max_roundtrip,'endpoint_cap_tests':caps,
            'five_angle_window_tests':windows,'sharp_family_errors':sharp,
            'five_angle_bound_squared':str(b2),'parity_cases':parity_checks}

def color22(tet, edge):
    j = INDEX[edge]
    if j == 0:
        return 'R'
    if j == 3:
        return 'R' if tet < 2 else 'S'
    return 'A' if j in (1,4) else 'B'

def check_packet22():
    n = 22
    face = {}
    edge_dsu, vertex_dsu, end_dsu, dual = DSU(6*n),DSU(4*n),DSU(12*n),DSU(n)
    positive = {0,3,5,8,10,12,14,16,17,19,21}
    orientation = {t:(1 if t in positive else -1) for t in range(n)}
    fans = defaultdict(list)
    for t,f,u,g,word in ROWS22:
        p = tuple(map(int,word))
        assert sorted(p) == list(range(4)) and p[f] == g
        assert sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))%2 == 0
        assert orientation[t] == -orientation[u]
        assert (t,f) != (u,g) and (t,f) not in face and (u,g) not in face
        inv = tuple(p.index(i) for i in range(4))
        face[t,f] = (u,g,p)
        face[u,g] = (t,f,inv)
        dual.union(t,u)
        for a in range(4):
            if a != f:
                vertex_dsu.union(4*t+a,4*u+p[a])
        for a,b in EDGES:
            if f in (a,b):
                continue
            target = tuple(sorted((p[a],p[b])))
            assert color22(t,(a,b)) == color22(u,target)
            j,k = 6*t+INDEX[(a,b)],6*u+INDEX[target]
            edge_dsu.union(j,k)
            for end in (0,1):
                x,y = 2*j+end,2*k+(end ^ (p[a]>p[b]))
                end_dsu.union(x,y)
                fans[x].append(y)
                fans[y].append(x)
    assert len(face)==88 and len(dual.groups())==1
    groups = edge_dsu.groups()
    assert sorted(map(len,groups)) == [6,6,6,6,20,22,22,44]
    assert all(end_dsu.find(2*j)!=end_dsu.find(2*j+1) for j in range(6*n))
    end_groups = end_dsu.groups()
    assert len(end_groups)==16
    for group in end_groups:
        assert all(len(fans[x])==2 for x in group)
        reached = {group[0]}
        todo = [group[0]]
        while todo:
            for y in fans[todo.pop()]:
                if y not in reached:
                    reached.add(y)
                    todo.append(y)
        assert reached==set(group)
    output = []
    angles = {}
    for group in groups:
        labels = {color22(j//6,EDGES[j%6]) for j in group}
        assert len(labels)==1
        label = next(iter(labels))
        nc = sum(j//6<2 for j in group)
        nd = len(group)-nc
        assert (nc,nd)=={'R':(1,5),'A':(2,20),'B':(4,40),'S':(0,20)}[label]
        t,j = divmod(group[0],6)
        a,b = EDGES[j]
        entry = min(v for v in range(4) if v not in (a,b))
        start = (t,a,b,entry)
        state,seen,circle = start,set(),[]
        while state not in seen:
            seen.add(state)
            t,a,b,entry = state
            circle.append(6*t+INDEX[tuple(sorted((a,b)))])
            outgoing = next(v for v in range(4) if v not in (a,b,entry))
            u,g,p = face[t,outgoing]
            state = (u,p[a],p[b],g)
        assert state==start and len(circle)==len(group) and sorted(circle)==group
        for j in group:
            angles[j] = Fraction(2,len(group))
        assert sum(angles[j] for j in group)==2
        output.append({'color':label,'degree':len(group),'C':nc,'D':nd,
                       'normal_circle':circle})
    assert len(vertex_dsu.groups())==1 and len(vertex_dsu.groups()[0])==88
    maximum = Fraction(0)
    for t in range(n):
        for v in range(4):
            total = sum(angles[6*t+j] for j,e in enumerate(EDGES) if v in e)
            assert 0<total<1
            maximum = max(maximum,total)
    assert maximum==Fraction(31,66)
    V,E,F = len(end_groups),6*n,4*n
    assert (V,E,F)==(16,132,88) and V-E+F==-28
    return {'tetrahedra':n,'face_pairs':len(ROWS22),'edges':output,
            'oriented_tetrahedra_positive':sorted(positive),
            'link':{'V':V,'E':E,'F':F,'chi':-28,'genus':15},
            'max_normalized_corner':str(maximum)}

# Sections 75--80: coupled endpoint budgets and singleton-label capacity.
import random
import collections

def genuine(alpha):
 return all(a>0 for a in alpha) and all(sum(alpha[j] for j,e in enumerate(EDGES) if i in e)<math.pi for i in range(4))

def envelope(theta, sigma1,sigma2):
 return 1+2*math.sin(theta)**2/((math.cos(theta)+math.cos(sigma1-theta))*(math.cos(theta)+math.cos(sigma2-theta)))

def asym_cap(sigma1,sigma2):
 m,M=sorted((sigma1,sigma2))
 return 1+2*(1-math.cos(m))/(math.cos(m)+math.cos(M-m))

def half_formula(alpha):
 theta,a,b,g,c,d=alpha
 p=math.tan(theta/2);q=math.tan((a+b)/2);r=math.tan((c+d)/2)
 xi=math.tan((a-b)/2);eta=math.tan((d-c)/2)
 num=(1+p*p)*(1+p*p*q*r*xi*eta)+p*p*math.sqrt((1+q*q)*(1+r*r)*(1+xi*xi)*(1+eta*eta))*math.cos(g)
 den=math.sqrt((1-p*p*q*q)*(1-p*p*r*r)*(1-p*p*xi*xi)*(1-p*p*eta*eta))
 return num/den

def check_new_analytic():
 rng=random.Random(947475)
 checked=total_caps=long_edges=old_cap_missed=0
 worst=0.
 for _ in range(3500):
  angles=[rng.uniform(.02,1.3) for j in EDGES]
  max_corner=max(sum(angles[j] for j,e in enumerate(EDGES) if i in e) for i in range(4))
  scale=rng.uniform(.35,.985)*math.pi/max_corner
  angles=[a*scale for a in angles]
  assert genuine(angles)
  x=inverse_cosh_lengths(angles)
  hf=half_formula(angles)
  worst=max(worst,abs(hf-x[0])/x[0])
  for j,(i,k) in enumerate(EDGES):
   theta=angles[j]
   si=sum(angles[n] for n,e in enumerate(EDGES) if i in e)
   sk=sum(angles[n] for n,e in enumerate(EDGES) if k in e)
   assert x[j]<envelope(theta,si,sk)*(1+1e-11)
   assert x[j]<asym_cap(si,sk)*(1+1e-11)
   checked+=1
   if si+sk<=math.pi:
    assert x[j]<3
    total_caps+=1
    old_cap_missed+=max(si,sk)>math.pi/2
   if x[j]>=3:
    assert si+sk>math.pi
    long_edges+=1
 assert worst<1e-10
 sequences=[]
 for s1,s2 in [(math.pi/3,2*math.pi/3),(math.pi/5,5*math.pi/6),(2*math.pi/3,5*math.pi/6),(math.pi/2,math.pi/2)]:
  m,M=sorted((s1,s2));B=asym_cap(m,M);err=[]
  for eps in (.005,.001,.0002):
   alpha=[m-2*eps,eps,eps,eps,eps,M-m+eps]
   assert genuine(alpha)
   x=inverse_cosh_lengths(alpha)[0]
   assert x<B
   err.append(B-x)
  assert err[2]<err[1]<err[0]
  sequences.append({'caps_over_pi':[m/math.pi,M/math.pi],'limit':B,'errors':err})
 assert abs(asym_cap(math.pi/3,2*math.pi/3)-2)<1e-12
 # Larger angular window: target plus three neighbours <=pi/5;
 # the remaining neighbour is allowed all the way to 7pi/15.
 window=0
 for _ in range(1000):
  alpha=[rng.uniform(.015,math.pi/5) for j in EDGES]
  alpha[4]=rng.uniform(.015,7*math.pi/15)
  cap=math.pi-max(alpha[1]+alpha[5],alpha[2]+alpha[4])
  alpha[3]=rng.uniform(.005,cap-.005)
  assert genuine(alpha)
  assert inverse_cosh_lengths(alpha)[0]<3
  window+=1
 assert abs(envelope(math.pi/5,3*math.pi/5,13*math.pi/15)-3)<1e-12
 return {'independent_edge_envelopes':checked,'combined_caps':total_caps,
         'combined_caps_outside_old_coordinate_caps':old_cap_missed,
         'long_edge_demands':long_edges,'half_angle_relative_error':worst,
         'sharp_asymmetric_sequences':sequences,'enlarged_window_cases':window}

def check_singleton_packet():
 rows=list(ROWS)
 assert rows[12]==(1,0,3,0,'0132')
 rows[12]=(1,0,3,0,'0213')
 n=11;face={};edges=DSU(66);vertices=DSU(44);ends=DSU(132);dual=DSU(11);fans=collections.defaultdict(list)
 for t,f,u,g,word in rows:
  p=tuple(map(int,word));assert sorted(p)==list(range(4)) and p[f]==g
  assert sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))%2==1
  assert (t,f)!=(u,g) and (t,f) not in face and (u,g) not in face
  face[t,f]=(u,g,p);face[u,g]=(t,f,tuple(p.index(i) for i in range(4)));dual.union(t,u)
  for a in range(4):
   if a!=f:vertices.union(4*t+a,4*u+p[a])
  for j,(a,b) in enumerate(EDGES):
   if f in (a,b):continue
   k=6*u+INDEX[tuple(sorted((p[a],p[b])))];j+=6*t;edges.union(j,k)
   for side in (0,1):
    x,y=2*j+side,2*k+(side^(p[a]>p[b]));ends.union(x,y);fans[x].append(y);fans[y].append(x)
 assert len(face)==44 and len(dual.groups())==1 and len(vertices.groups())==1
 groups=edges.groups();assert sorted(map(len,groups))==[6,6,54]
 assert len(ends.groups())==6 and all(ends.find(2*j)!=ends.find(2*j+1) for j in range(66))
 circles=[];angles={};labels={}
 for group in groups:
  if len(group)==6:assert len({j//6 for j in group})==6
  lab='U' if 0 in group else ('V' if 3 in group else 'H')
  t,j=divmod(group[0],6);a,b=EDGES[j];entry=min(v for v in range(4) if v not in(a,b))
  start=(t,a,b,entry);state=start;seen=set();circle=[]
  while state not in seen:
   seen.add(state);t,a,b,entry=state;circle.append(6*t+INDEX[tuple(sorted((a,b)))])
   out=next(v for v in range(4) if v not in(a,b,entry));u,g,p=face[t,out];state=(u,p[a],p[b],g)
  assert state==start and sorted(circle)==group
  for j in group:angles[j]=Fraction(2,len(group));labels[j]=lab
  circles.append({'label':lab,'degree':len(group),'normal_circle':circle})
 for gr in ends.groups():
  assert all(len(fans[x])==2 for x in gr)
  seen={gr[0]};todo=[gr[0]]
  while todo:
   for y in fans[todo.pop()]:
    if y not in seen:seen.add(y);todo.append(y)
  assert seen==set(gr)
 maximum=Fraction(0)
 for t in range(n):
  assert sum(labels[6*t+j]=='U' for j in range(6))<=1
  assert sum(labels[6*t+j]=='V' for j in range(6))<=1
  for v in range(4):
   total=sum(angles[6*t+j] for j,e in enumerate(EDGES) if v in e)
   assert 0<total<1;maximum=max(maximum,total)
 assert maximum==Fraction(11,27)
 return {'tetrahedra':11,'face_pairs':22,'changed_row':rows[12],
         'edges':circles,'link':{'V':6,'E':66,'F':44,'chi':-16,'genus':9},
         'max_normalized_corner':str(maximum),
         'theorem_hypotheses':'three actual edges; U,V each occur at most once per tetrahedron'}

if __name__ == '__main__':
    print(json.dumps({'packet':check_packet(),'local_star':check_local_star(),
                      'packet22':check_packet22(),
                      'analytic_continuation':check_analytic_continuation(),
                      'coupled_endpoint_continuation':check_new_analytic(),
                      'singleton_packet':check_singleton_packet()},indent=2))
