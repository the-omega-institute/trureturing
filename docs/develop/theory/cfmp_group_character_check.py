#!/usr/bin/env python3
"""Supplementary checks for CFMP group/character continuation.

Python 3, standard library only. Run without -O. Polynomial identities and
finite topology checks supplement written proofs; no Lean or interval
certificate, universal enumeration, or full-CFMP solution is claimed.
"""
from __future__ import annotations

import collections
import itertools
import json
import math
import random
from fractions import Fraction as F


def pmul(p, q):
    """Function composition p after q; group words use this convention."""
    return tuple(p[q[i]] for i in range(len(p)))


def pinv(p):
    return tuple(p.index(i) for i in range(len(p)))


def ppow(p, k):
    if k < 0:
        return ppow(pinv(p), -k)
    out = tuple(range(len(p)))
    for _ in range(k):
        out = pmul(out, p)
    return out


def pcycles(p):
    used, out = set(), []
    for i in range(len(p)):
        if i in used:
            continue
        cycle, j = [], i
        while j not in used:
            used.add(j)
            cycle.append(j)
            j = p[j]
        assert j == i
        out.append(cycle)
    return out


def porder(p):
    out = 1
    for c in pcycles(p):
        out = out*len(c)//math.gcd(out, len(c))
    return out


def pclosure(gens):
    one = tuple(range(len(gens[0])))
    found, stack = {one}, [one]
    while stack:
        x = stack.pop()
        for g in gens:
            y = pmul(x, g)
            if y not in found:
                found.add(y)
                stack.append(y)
    return found


def psign(p):
    return (-1)**sum(p[i] > p[j] for i in range(len(p))
                    for j in range(i+1, len(p)))


def det4(matrix):
    return sum((psign(p)*math.prod(matrix[i][p[i]] for i in range(4))
                for p in itertools.permutations(range(4))), F(0))


def signed_matrix(values):
    r, a, b, o, c, d = values
    return [[1,-r,-a,-b],[-r,1,-d,-c],[-a,-d,1,-o],[-b,-c,-o,1]]


def edge_cosine_data(values):
    r, a, b, o, c, d = values
    d1 = r*r+a*a+d*d+2*r*a*d-1
    d2 = r*r+b*b+c*c+2*r*b*c-1
    numerator = a*b+c*d+r*a*c+r*b*d-(r*r-1)*o
    return numerator, d1, d2


def reindex(values, i, j):
    def at(a,b):
        return values[IDX[tuple(sorted((a,b)))]]
    k,h = [v for v in range(4) if v not in (i,j)]
    return (at(i,j),at(i,k),at(i,h),at(k,h),at(j,h),at(j,k))


def raw_cosines(values):
    out = []
    for i,j in EDGES:
        n,d1,d2 = edge_cosine_data(reindex(values,i,j))
        out.append(float(n)/math.sqrt(float(d1*d2)))
    return out


def character_data(values):
    r,a,b,o,c,d = values
    A,B = (a+c)/2,(b+d)/2
    xi,zeta = (a-c)/2,(b-d)/2
    L = (A+B)**2-(r-1)*(o-1)
    M = (r+1)*(o+1)-(A-B)**2
    defect = (2*(r*o-1-A*A+B*B)*xi*xi
              +2*(r*o-1+A*A-B*B)*zeta*zeta
              +4*(r-o)*xi*zeta+(xi*xi-zeta*zeta)**2)
    return A,B,xi,zeta,L,M,defect


def check_characters():
    pairs = [frozenset((frozenset(EDGES[i]),frozenset(EDGES[j])))
             for i,j in ((0,3),(1,4),(2,5))]
    kernel, images = [], set()
    for p in itertools.permutations(range(4)):
        image = tuple(pairs.index(frozenset(frozenset(p[v] for v in e)
                                           for e in pair)) for pair in pairs)
        images.add(image)
        if image == (0,1,2):
            kernel.append(p)
    assert len(images) == 6
    assert set(kernel) == {(0,1,2,3),(1,0,3,2),(2,3,0,1),(3,2,1,0)}
    rng = random.Random(9474119)
    for _ in range(600):
        values = [F(1)+F(rng.randrange(1,100),rng.randrange(1,25)) for _ in range(6)]
        matrix = signed_matrix(values)
        determinant = det4(matrix)
        A,B,xi,zeta,L,M,defect = character_data(values)
        assert determinant == -L*M+defect
        r,a,b,o,c,d = values
        T = ((1,0,1,0),(1,0,-1,0),(0,1,0,1),(0,1,0,-1))
        transformed = [[sum(T[k][i]*matrix[k][l]*T[l][j]
                            for k in range(4) for l in range(4))/2
                        for j in range(4)] for i in range(4)]
        expected = [[1-r,-A-B,0,-xi+zeta],[-A-B,1-o,-xi-zeta,0],
                    [0,-xi-zeta,1+r,-A+B],[-xi+zeta,0,-A+B,1+o]]
        assert transformed == expected
        for i,j in EDGES:
            v = reindex(values,i,j)
            n,d1,d2 = edge_cosine_data(v)
            assert d1 > 0 and d2 > 0
            assert d1*d2-n*n == -(v[0]*v[0]-1)*determinant
        t = xi*xi+zeta*zeta
        q = (A*A-B*B)*(zeta*zeta-xi*xi)+2*(r-o)*xi*zeta
        assert q*q <= ((A*A-B*B)**2+(r-o)**2)*t*t
        assert (xi*xi-zeta*zeta)**2 <= t*t
    values = tuple(map(F,('4.9','2.8','2','4.9','1.2','2')))
    assert det4(signed_matrix(values)) == F(189,80)
    average = tuple(map(F,('4.9','2','2','4.9','2','2')))
    assert det4(signed_matrix(average)) == -F(274999,10000)
    assert F(59,10)*(5-F(49,10)) == F(59,100)
    # Nonzero independent skew directions strictly inside the proved radius.
    tests = 0
    while tests < 1000:
        r,o,A,B = [1+rng.uniform(.2,4) for _ in range(4)]
        L=(A+B)**2-(r-1)*(o-1)
        M=(r+1)*(o+1)-(A-B)**2
        if L <= .01 or M <= .01:
            continue
        C=r*o-1+math.hypot(A*A-B*B,r-o)
        radius2=L*M/(math.sqrt(C*C+L*M)+C)
        radius=min(math.sqrt(radius2)*.8,A-1,B-1)
        xi,zeta=[rng.uniform(-.6,.6)*radius for _ in range(2)]
        vals=(r,A+xi,B+zeta,o,A-xi,B-zeta)
        assert min(vals)>1 and (xi*xi+zeta*zeta)<radius2
        cs=raw_cosines(vals)
        assert all(-1<c<1 for c in cs)
        angles=list(map(math.acos,cs))
        assert all(sum(angles[j] for j,e in enumerate(EDGES) if v in e)<math.pi
                   for v in range(4))
        tests += 1
    return dict(S4_images=len(images),V4_kernel_size=len(kernel),
                exact_rational_vectors=600,exact_cosine_identities=3600,
                symmetry_breaking_samples=tests,
                counterexample_det='189/80',averaged_det='-274999/10000',
                sharp_squared_radius='59/100')

from collections import defaultdict,Counter
from fractions import Fraction
from itertools import combinations
EDGES=((0,1),(0,2),(0,3),(2,3),(1,3),(1,2))
IDX={e:i for i,e in enumerate(EDGES)}
class DSU:
 def __init__(self,n):self.p=list(range(n))
 def find(self,x):
  while x!=self.p[x]:self.p[x]=self.p[self.p[x]];x=self.p[x]
  return x
 def union(self,a,b):self.p[self.find(a)]=self.find(b)
 def groups(self):
  g=defaultdict(list)
  for i in range(len(self.p)):g[self.find(i)].append(i)
  return list(g.values())
def parity(p):return sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))%2

def face_rows(U,V):
 return [(i,0,U[i],3,(3,0,1,2)) for i in range(len(U))]+[(i,1,V[i],2,(3,2,0,1)) for i in range(len(V))]

def analyze(U,V):
 n=len(U);rows=face_rows(U,V);edges=DSU(6*n);verts=DSU(4*n);ends=DSU(12*n);dual=DSU(n)
 faces={};fans=defaultdict(list)
 for t,f,u,g,p in rows:
  assert p[f]==g and parity(p)==1
  assert (t,f) not in faces and (u,g) not in faces
  faces[t,f]=(u,g,p);faces[u,g]=(t,f,tuple(p.index(i) for i in range(4)))
  dual.union(t,u)
  for a in range(4):
   if a!=f:verts.union(4*t+a,4*u+p[a])
  for j,(a,b) in enumerate(EDGES):
   if f in (a,b):continue
   k=IDX[tuple(sorted((p[a],p[b])))];x=6*t+j;y=6*u+k
   edges.union(x,y)
   for z in (0,1):
    xx=2*x+z;yy=2*y+(z^(p[a]>p[b]))
    ends.union(xx,yy);fans[xx].append(yy);fans[yy].append(xx)
 assert len(dual.groups())==1 and len(faces)==4*n
 groups=sorted(edges.groups(),key=lambda x:min(x));circles=[];colourdegree=defaultdict(list)
 for gr in groups:
  assert all(ends.find(2*j)!=ends.find(2*j+1) for j in gr)
  cset={j%6 in (0,3,5) for j in gr};assert len(cset)==1
  colourdegree['low' if cset=={True} else 'high'].append(len(gr))
  assert sorted(Counter(j%6 for j in gr).values())==[len(gr)//3]*3
  t,j=divmod(min(gr),6);a,b=EDGES[j];f=min(x for x in range(4) if x not in(a,b))
  st=(t,a,b,f);seen=[];cur=st
  for _ in range(len(gr)):
   t,a,b,f=cur;seen.append(6*t+IDX[tuple(sorted((a,b)))])
   exit=next(x for x in range(4) if x not in (a,b,f));u,g,p=faces[t,exit];cur=(u,p[a],p[b],g)
   assert cur!=st or len(seen)==len(gr)
  assert cur==st and sorted(seen)==gr
  circles.append(seen)
 for gr in ends.groups():
  assert all(len(fans[x])==2 for x in gr)
  done={gr[0]};stack=[gr[0]]
  while stack:
   for y in fans[stack.pop()]:
    if y not in done:done.add(y);stack.append(y)
  assert done==set(gr)
 links=[]
 for gr in verts.groups():
  vv=set()
  for tv in gr:
   t,a=divmod(tv,4)
   for b in range(4):
    if a!=b:vv.add(ends.find(2*(6*t+IDX[tuple(sorted((a,b)))])+(a>b)))
  F=len(gr);E=3*F//2;V=len(vv);chi=V-E+F
  assert F%2==0 and chi%2==0
  links.append({'V':V,'E':E,'F':F,'chi':chi,'genus':1-chi//2})
 angle=[None]*(6*n)
 for gr in groups:
  for j in gr:angle[j]=Fraction(2,len(gr))
 maxcorner=max(sum(angle[6*t+j] for j,(a,b) in enumerate(EDGES) if v in(a,b)) for t in range(n) for v in range(4))
 return {'tetrahedra':n,'face_pairs':len(rows),'edge_degrees':dict(colourdegree),'links':links,'fan_sizes':sorted(map(len,ends.groups())),'max_initial_corner':str(maxcorner),'circles':circles}



def right_coset_action(G, C, generators):
    """Cosets Cg acted on from the right; no normality assumed."""
    cosets, index = [], {}
    for g in sorted(G):
        if g in index:
            continue
        coset = {pmul(c,g) for c in C}
        j = len(cosets)
        cosets.append(sorted(coset))
        for x in coset:
            index[x] = j
    actions=[]
    for generator in generators:
        action=tuple(index[pmul(coset[0],generator)] for coset in cosets)
        assert sorted(action)==list(range(len(cosets)))
        for i,coset in enumerate(cosets):
            assert all(index[pmul(x,generator)]==action[i] for x in coset)
        actions.append(action)
    return cosets,index,actions


def peripheral_words(u,v):
    ell=pmul(pinv(v),ppow(u,2))
    h=pmul(ppow(v,2),u)
    s=pmul(ppow(u,-2),v)
    t=pmul(ppow(u,-3),pmul(v,u))
    k=pmul(v,ppow(u,3))
    c=(pinv(s),pmul(s,k),t,pinv(pmul(k,t)))
    assert c[0]==ell and c[3]==pinv(h)
    assert c[1]==pmul(ppow(u,-2),pmul(h,ppow(u,2)))
    assert c[2]==pmul(pinv(u),pmul(pinv(ell),u))
    assert pmul(pmul(pmul(c[0],c[1]),c[2]),c[3])==tuple(range(len(u)))
    return ell,h,s,t,k,c


def check_peripheral_prediction(u,v,C):
    G=pclosure([u,v])
    ell,h,s,t,k,cs=peripheral_words(u,v)
    cosets,index,(U,V)=right_coset_action(G,C,[u,v])
    K=pclosure([s,t,k])
    _,_,peripheral=right_coset_action(G,C,cs)
    used=set();predicted=[]
    for i,coset in enumerate(cosets):
        if i in used:continue
        orbit={index[pmul(coset[0],x)] for x in K}
        used.update(orbit)
        vertex_count=0
        for action in peripheral:
            seen=set()
            for j in orbit:
                if j in seen:continue
                vertex_count+=1;current=j
                while current not in seen:
                    seen.add(current);current=action[current]
                    assert current in orbit
                assert current==j
        m=len(orbit)
        predicted.append(dict(V=vertex_count,E=6*m,F=4*m,
                              chi=vertex_count-2*m,genus=1+m-vertex_count//2))
    actual=analyze(U,V)
    key=lambda row:(row['F'],row['V'])
    assert sorted(predicted,key=key)==sorted(actual['links'],key=key)
    return actual,len(K),U,V


def compact(packet):
    return dict(tetrahedra=packet['tetrahedra'],face_pairs=packet['face_pairs'],
                edge_degrees={k:dict(collections.Counter(v))
                              for k,v in packet['edge_degrees'].items()},
                links=packet['links'],fan_sizes=packet['fan_sizes'],
                max_initial_corner=packet['max_initial_corner'])


def check_A5():
    u=(0,1,3,4,2);v=(2,3,4,0,1)
    G=pclosure([u,v]);C=pclosure([v]);one=tuple(range(5))
    assert len(G)==60 and len(C)==5 and all(psign(x)==1 for x in G)
    ell,h,s,t,k,cs=peripheral_words(u,v)
    assert porder(ell)==2 and porder(h)==3
    assert len(pclosure([s,t,k]))==60
    packet,K,U,V=check_peripheral_prediction(u,v,C)
    assert U==(1,2,0,5,3,4,7,8,6,11,9,10)
    assert V==(0,2,8,7,6,10,1,5,4,3,9,11)
    assert packet['links']==[dict(V=20,E=72,F=48,chi=-4,genus=3)]
    assert packet['edge_degrees']=={'low':[6]*6,'high':[9]*4}
    assert packet['max_initial_corner']=='8/9'
    normalizer={g for g in G if {pmul(pinv(g),pmul(c,g)) for c in C}==C}
    assert len(normalizer)==10
    regular,_,_,_=check_peripheral_prediction(u,v,{one})
    assert regular['links']==[dict(V=100,E=360,F=240,chi=-20,genus=11)]
    # Check the exact P4 golden identity at floating precision as a supplement.
    x=(3+math.sqrt(5))/2;y=(1+3*math.sqrt(5))/4
    alpha=list(map(math.acos,raw_cosines((x,y,y,x,y,x))))
    assert abs(2*alpha[0]+alpha[5]-math.pi)<1e-12
    assert abs(2*alpha[1]+alpha[2]-2*math.pi/3)<1e-12
    # More finite, genuinely non-normal coset actions test peripheral formulas.
    rng=random.Random(9474122);tests=0
    S4=list(itertools.permutations(range(4)))
    for _ in range(35):
        uu,vv=rng.choice(S4),rng.choice(S4)
        GG=pclosure([uu,vv]);cc=pclosure([rng.choice(sorted(GG))])
        check_peripheral_prediction(uu,vv,cc);tests+=1
    return dict(schreier=compact(packet),regular=compact(regular),
                A5_order=60,coset_subgroup_order=5,normalizer_order=10,
                extra_coset_link_tests=tests)


def mm(x,y):
    a,b,c,d=x;e,f,g,h=y
    return ((a*e+b*g)%5,(a*f+b*h)%5,(c*e+d*g)%5,(c*f+d*h)%5)


def mi(x):
    a,b,c,d=x
    return (d%5,-b%5,-c%5,a%5)


def mpow(x,n):
    if n<0:return mpow(mi(x),-n)
    out=(1,0,0,1)
    for _ in range(n):out=mm(out,x)
    return out


def mclosure(gens):
    one=(1,0,0,1);found={one};stack=[one]
    while stack:
        x=stack.pop()
        for g in gens:
            y=mm(x,g)
            if y not in found:found.add(y);stack.append(y)
    return found


def check_binary_group():
    one=(1,0,0,1);minus=(4,0,0,4)
    G={x for x in itertools.product(range(5),repeat=4)
       if (x[0]*x[3]-x[1]*x[2])%5==1}
    assert len(G)==120
    assert {x for x in G if mpow(x,2)==one}=={one,minus}
    u=(0,1,4,1);v=(1,1,0,1)
    assert mclosure([u,v])==G
    ell=mm(mi(v),mpow(u,2));h=mm(mpow(v,2),u)
    assert mpow(ell,2)==minus and mpow(ell,4)==one
    assert h!=one and mpow(h,3)==one
    s=mm(mpow(u,-2),v);t=mm(mpow(u,-3),mm(v,u));k=mm(v,mpow(u,3))
    assert mclosure([s,t,k])==G
    ordered=sorted(G);index={x:i for i,x in enumerate(ordered)}
    U=tuple(index[mm(x,u)] for x in ordered)
    V=tuple(index[mm(x,v)] for x in ordered)
    packet=analyze(U,V)
    assert packet['links']==[dict(V=140,E=720,F=480,chi=-100,genus=51)]
    assert sorted(packet['edge_degrees']['low'])==[12]*30
    assert sorted(packet['edge_degrees']['high'])==[9]*40
    projective_involutions={x for x in G if mpow(x,2)==minus}
    assert len(projective_involutions)==30
    return dict(SL2F5_order=120,nontrivial_involutions=1,
                projective_order_two_lifts=len(projective_involutions),
                packet=compact(packet))


def run():
    if not __debug__:
        raise RuntimeError('Run without -O; assertions are part of these checks')
    return dict(characters=check_characters(),A5=check_A5(),binary=check_binary_group(),
                status='supplementary finite checks; written proofs not kernel certified')


if __name__=='__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))
