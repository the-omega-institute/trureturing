#!/usr/bin/env python3
"""Fixed CFMP triangle-seed certificate, Sections 106-110.

Standard-library supplementary checks, not a numerical existence proof.
The face table is fixed. No random topology search is required to run it.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import permutations, combinations
import json
import math
import random

EDGES = ((0,1),(0,2),(0,3),(2,3),(1,3),(1,2))
INDEX = {e:j for j,e in enumerate(EDGES)}
PERMS = tuple(permutations(range(4)))
LABELS = (('C', 'A', 'B', 'C', 'A', 'B'),
 ('C', 'A', 'B', 'C', 'A', 'B'),
 ('U', 'A', 'B', 'C', 'A', 'B'),
 ('U', 'A', 'B', 'A', 'A', 'B'),
 ('U', 'A', 'B', 'A', 'A', 'B'),
 ('U', 'A', 'B', 'A', 'A', 'B'),
 ('U', 'A', 'B', 'A', 'A', 'B'),
 ('U', 'A', 'B', 'A', 'A', 'B'),
 ('V', 'B', 'C', 'A', 'B', 'C'),
 ('V', 'B', 'C', 'B', 'B', 'C'),
 ('V', 'B', 'C', 'B', 'B', 'C'),
 ('V', 'B', 'C', 'B', 'B', 'C'),
 ('V', 'B', 'C', 'B', 'B', 'C'),
 ('V', 'B', 'C', 'B', 'B', 'C'))
SIGNS = (1, -1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, -1, -1)
ROWS = ((1, 1, 2, 0, '1032'),
 (1, 2, 0, 1, '3210'),
 (8, 1, 2, 1, '3102'),
 (1, 3, 0, 2, '1032'),
 (1, 0, 0, 0, '0123'),
 (8, 0, 0, 3, '3102'),
 (7, 3, 3, 3, '0123'),
 (2, 3, 5, 3, '0123'),
 (4, 2, 5, 2, '0123'),
 (7, 2, 2, 2, '0123'),
 (3, 2, 6, 3, '1032'),
 (6, 2, 4, 3, '1032'),
 (4, 1, 3, 1, '3120'),
 (3, 0, 5, 0, '0123'),
 (4, 0, 6, 0, '0123'),
 (7, 1, 5, 1, '3120'),
 (7, 0, 6, 1, '1302'),
 (8, 3, 10, 3, '0123'),
 (9, 3, 8, 2, '1032'),
 (13, 3, 11, 2, '1032'),
 (13, 2, 9, 2, '0123'),
 (11, 3, 12, 3, '0123'),
 (10, 2, 12, 2, '0123'),
 (11, 1, 10, 1, '3120'),
 (11, 0, 10, 0, '0213'),
 (9, 1, 12, 1, '0123'),
 (12, 0, 13, 0, '0213'),
 (9, 0, 13, 1, '1032'))

class DSU:
    def __init__(self, n): self.parent = list(range(n))
    def find(self, x):
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x
    def union(self, x, y): self.parent[self.find(x)] = self.find(y)
    def groups(self):
        groups = defaultdict(list)
        for i in range(len(self.parent)): groups[self.find(i)].append(i)
        return sorted(groups.values(), key=lambda g:g[0])

def sign(p):
    return -1 if sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))%2 else 1

def relabel(labels, p):
    return tuple(labels[INDEX[tuple(sorted((p[a],p[b])))]] for a,b in EDGES)

def canonical(labels): return min(relabel(labels,p) for p in PERMS)

def paired_frames(labels, H):
    return {z for p in PERMS if (z:=relabel(labels,p))[1]==z[4]
            and z[2]==z[5] and z[1]!=z[2] and {z[1],z[2]}<=H}

def check_certificate(rows=ROWS):
    n = len(LABELS)
    ed,vd,en,dual = DSU(6*n),DSU(4*n),DSU(12*n),DSU(n)
    faces, fans = {}, defaultdict(list)
    for t,f,u,g,word in rows:
        p = tuple(map(int,word))
        assert sorted(p)==list(range(4)) and p[f]==g
        assert SIGNS[u]==-SIGNS[t]*sign(p)
        assert (t,f)!=(u,g) and (t,f) not in faces and (u,g) not in faces
        faces[t,f]=(u,g,p)
        faces[u,g]=(t,f,tuple(p.index(i) for i in range(4)))
        dual.union(t,u)
        for a in range(4):
            if a!=f: vd.union(4*t+a,4*u+p[a])
        for j,(a,b) in enumerate(EDGES):
            if f in (a,b): continue
            k=INDEX[tuple(sorted((p[a],p[b])))]
            assert LABELS[t][j]==LABELS[u][k]
            x,y=6*t+j,6*u+k
            ed.union(x,y)
            for end in (0,1):
                xx,yy=2*x+end,2*y+(end^(p[a]>p[b]))
                en.union(xx,yy); fans[xx].append(yy); fans[yy].append(xx)
    assert len(faces)==4*n and len(dual.groups())==1
    groups=ed.groups()
    by_label={}
    angles={}
    circles={}
    for group in groups:
        names={LABELS[i//6][i%6] for i in group}
        assert len(names)==1
        label=next(iter(names)); assert label not in by_label
        by_label[label]=len(group)
        t,j=divmod(group[0],6); a,b=EDGES[j]
        entry=min(v for v in range(4) if v not in (a,b))
        initial=(t,a,b,entry); state=initial; seen=set(); circle=[]
        while state not in seen:
            seen.add(state); t,a,b,entry=state
            circle.append(6*t+INDEX[tuple(sorted((a,b)))])
            out=next(v for v in range(4) if v not in (a,b,entry))
            u,g,p=faces[t,out]; state=(u,p[a],p[b],g)
        assert state==initial and len(circle)==len(group) and sorted(circle)==group
        circles[label]=circle
        for i in group: angles[i]=Fraction(2,len(group))
        assert sum(angles[i] for i in group)==2
    assert by_label=={'A':22,'B':33,'C':17,'U':6,'V':6}
    assert all(en.find(2*j)!=en.find(2*j+1) for j in range(6*n))
    end_groups=en.groups(); assert len(end_groups)==10
    for group in end_groups:
        assert all(len(fans[x])==2 for x in group)
        reached={group[0]}; stack=[group[0]]
        while stack:
            for y in fans[stack.pop()]:
                if y not in reached: reached.add(y); stack.append(y)
        assert reached==set(group)
    assert len(vd.groups())==1
    V,E,F=len(end_groups),6*n,4*n
    assert (V,E,F)==(10,84,56) and V-E+F==-18
    cap=max(sum(angles[6*t+j] for j,e in enumerate(EDGES) if v in e)
            for t in range(n) for v in range(4))
    assert cap==Fraction(287,561)<1
    types=defaultdict(list)
    for i,x in enumerate(LABELS): types[canonical(x)].append(i)
    assert sorted(map(len,types.values()))==[1,1,2,5,5]
    Z={i for group in types.values() if len(group)>=3 for i in group}
    # Two occurrences of the same three-pair named type are enough seeds.
    twins=set()
    seed_triples=set()
    for group in types.values():
        x=LABELS[group[0]]
        if len(group)>=2 and x[0]==x[3] and x[1]==x[4] and x[2]==x[5] and len(set(x))==3:
            twins.update(group); seed_triples.add(frozenset(x))
    assert twins=={0,1} and seed_triples=={frozenset('ABC')}
    K=Z|twins; H=set('ABC'); S=set('UV')
    assert K==set(range(14))-{2,8}
    assert all(any(h in LABELS[t] for t in K) for h in H)
    for i,x in enumerate(LABELS):
        assert x in paired_frames(x,H)
        if i not in K:
            for h in {x[0],x[3]} & H:
                assert h in {x[1],x[2]} or frozenset((h,x[1],x[2])) in seed_triples
    transported={}
    for e in S:
        pairs={tuple(sorted((x[1],x[2]))) for x in LABELS if e in x}
        assert len(pairs)==1
        transported[e]=next(iter(pairs))
        assert by_label[e]%2==0
    assert transported=={'U':('A','B'),'V':('B','C')}
    assert set.intersection(*(set(x) for x in LABELS))=={'B'}
    # Exhaust all H subsets and all 24 local vertex frames for the earlier
    # Theorem 102.1. Failure is about that exact certificate, not all methods.
    labels=set(by_label); old_certificates=[]
    for size in range(2,len(labels)):
        for hs in combinations(sorted(labels),size):
            HH=set(hs)
            if not all(any(h in LABELS[t] for t in Z) for h in HH): continue
            okay=True
            for t,x in enumerate(LABELS):
                fs=paired_frames(x,HH)
                if t not in Z:
                    fs={z for z in fs if ({z[0],z[3]}&HH)<={z[1],z[2]}}
                if not fs: okay=False; break
            if okay: old_certificates.append(hs)
    assert not old_certificates
    return {'tetrahedra':n,'face_pairs':len(rows),'degrees':by_label,
            'normal_circles':circles,'link':{'V':V,'E':E,'F':F,'genus':10},
            'link_fan_sizes':sorted(map(len,end_groups)),
            'maximum_normalized_corner':str(cap),'type_sizes':sorted(map(len,types.values())),
            'seed_tetrahedra':sorted(twins),'remaining_tetrahedra':sorted(set(range(n))-K),
            'transported_pairs':transported,'old_102_certificates':old_certificates}

def raw_cosines(x):
    def at(a,b): return x[INDEX[tuple(sorted((a,b)))]]
    values=[]
    for i,j in EDGES:
        k,h=[v for v in range(4) if v not in (i,j)]
        r,a,b,o,c,d=at(i,j),at(i,k),at(i,h),at(k,h),at(j,h),at(j,k)
        A=2*r*a*d+r*r+a*a+d*d-1
        B=2*r*b*c+r*r+b*b+c*c-1
        values.append((a*b+c*d+r*a*c+r*b*d-(r*r-1)*o)/math.sqrt(A*B))
    return values

def analytic_checks():
    rng=random.Random(9474106); dominated=obtuse=0
    minimum_excess=math.inf
    # Exact identities for the seed, including flat boundary samples.
    for _ in range(1000):
        h,a,b=[Fraction(rng.randint(11,400),10) for j in range(3)]
        D=h*h+a*a+b*b+2*h*a*b-1
        N=2*a*b+h*(a*a+b*b)-(h*h-1)*h
        assert D+N==(h+1)*((a+b)**2-(h-1)**2)
    for _ in range(2500):
        a,b=1+10**rng.uniform(-2,1.5),1+10**rng.uniform(-2,1.5)
        r=(1+a+b)*rng.uniform(1,2)
        low=max(1,(a-b)**2/(r+1)-1)
        high=1+(a+b)**2/(r-1)
        assert low<high
        o=low+(high-low)*rng.uniform(.02,.98)
        values=raw_cosines((r,a,b,o,a,b))
        assert all(-1<v<1 for v in values)
        alpha=[math.acos(v) for v in values]
        assert all(sum(alpha[j] for j,e in enumerate(EDGES) if v in e)<math.pi
                   for v in range(4))
        theta,beta,delta=alpha[:3]
        excess=2*theta+beta+delta-math.pi
        assert excess>0
        minimum_excess=min(minimum_excess,excess)
        dominated+=1; obtuse+=theta>math.pi/2
    # Normalized resource demand: exact integer comparison for both m values.
    resource_cases=0
    for d in range(6,100):
        for m in (0,1):
            g=d-m
            assert 2*g-4*(2-m)==2*(d+m-4)>=4
            resource_cases+=1
    return {'exact_seed_identities':1000,'dominated_genuine_cases':dominated,
            'obtuse_targets':obtuse,'minimum_sampled_excess':minimum_excess,
            'integer_resource_cases':resource_cases}

if __name__=='__main__':
    packet=check_certificate()
    wrong=list(ROWS); t,f,u,g,p=wrong[0]; wrong[0]=(t,f,u,g,'0123')
    try: check_certificate(tuple(wrong))
    except AssertionError: rejected=True
    else: raise AssertionError('Broken face map was accepted')
    print(json.dumps({'packet':packet,'wrong_map_rejected':rejected,
                      'analytic_checks':analytic_checks()},ensure_ascii=False,indent=2))
