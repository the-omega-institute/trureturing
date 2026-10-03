#!/usr/bin/env python3
"""Finite checks for CFMP Sections 101-105, standard library only.

Run with ordinary Python 3, without -O. This validates a fixed actual
face-pairing packet and cross-checks an existing continuous inequality.
It is not a Lean, interval-arithmetic, or full-CFMP certificate.
"""
import itertools, random, collections, json, math
from fractions import Fraction
EDGES=((0,1),(0,2),(0,3),(2,3),(1,3),(1,2))
IDX={e:i for i,e in enumerate(EDGES)}
PERMS=list(itertools.permutations(range(4)))
def parity(p):return sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))%2
ODD=[p for p in PERMS if parity(p)]
class DSU:
 def __init__(self,n):self.p=list(range(n))
 def find(self,x):
  while x!=self.p[x]:self.p[x]=self.p[self.p[x]];x=self.p[x]
  return x
 def union(self,a,b):self.p[self.find(a)]=self.find(b)
 def groups(self):
  d=collections.defaultdict(list)
  for i in range(len(self.p)):d[self.find(i)].append(i)
  return sorted(d.values(),key=lambda x:x[0])
def analyze(rows,n,labs=None,details=False):
 E=DSU(6*n);V=DSU(4*n);ENDS=DSU(12*n);DUAL=DSU(n);face={};fans=collections.defaultdict(list)
 for t,f,u,g,s in rows:
  p=tuple(map(int,s))
  assert sorted(p)==list(range(4)) and p[f]==g
  assert (t,f) not in face and (u,g) not in face and (t,f)!=(u,g)
  face[t,f]=(u,g,p);face[u,g]=(t,f,tuple(p.index(i) for i in range(4)))
  DUAL.union(t,u)
  for a in range(4):
   if a!=f:V.union(4*t+a,4*u+p[a])
  for j,(a,b) in enumerate(EDGES):
   if f in(a,b):continue
   h=IDX[tuple(sorted((p[a],p[b])))];j1=6*t+j;j2=6*u+h
   if labs is not None:assert labs[t][j]==labs[u][h]
   E.union(j1,j2)
   for k in(0,1):
    x,y=2*j1+k,2*j2+(k^(p[a]>p[b]))
    ENDS.union(x,y);fans[x].append(y);fans[y].append(x)
 if len(DUAL.groups())!=1:return None
 if len(face)!=4*n:return None
 gs=E.groups()
 if any(ENDS.find(2*j)==ENDS.find(2*j+1) for j in range(6*n)):return None
 if labs is not None:
  if len(gs)!=len(set(itertools.chain.from_iterable(labs))):return None
 # Propagate tetrahedron orientations; even permutations reverse signs.
 orient={0:1};todo=[0]
 while todo:
  t=todo.pop()
  for f in range(4):
   u,g,p=face[t,f];required=orient[t]*(1 if parity(p) else -1)
   if u in orient:
    if orient[u]!=required:return None
   else:orient[u]=required;todo.append(u)
 circles=[]
 for G in gs:
  t,j=divmod(G[0],6);a,b=EDGES[j];entry=min(v for v in range(4) if v not in(a,b))
  start=(t,a,b,entry);st=start;seen=set();circle=[]
  while st not in seen:
   seen.add(st);t,a,b,entry=st;circle.append(6*t+IDX[tuple(sorted((a,b)))])
   out=next(v for v in range(4) if v not in(a,b,entry));u,g,p=face[t,out];st=(u,p[a],p[b],g)
  if st!=start or len(circle)!=len(G) or sorted(circle)!=G:return None
  circles.append(circle)
 for gr in ENDS.groups():
  if any(len(fans[x])!=2 for x in gr):return None
  stack=[gr[0]];seen={gr[0]}
  while stack:
   for y in fans[stack.pop()]:
    if y not in seen:seen.add(y);stack.append(y)
  if seen!=set(gr):return None
 links=[]
 for gr in V.groups():
  lv=set()
  for tv in gr:
   t,a=divmod(tv,4)
   for b in range(4):
    if b!=a:lv.add(ENDS.find(2*(6*t+IDX[tuple(sorted((a,b)))] )+(a>b)))
  F=len(gr);ee=3*F//2;vv=len(lv);chi=vv-ee+F
  if F%2 or chi>=0 or chi%2:return None
  links.append(dict(V=vv,E=ee,F=F,chi=chi,genus=1-chi//2))
 if details:
  return dict(n=n,groups=gs,circles=circles,links=links,fan_sizes=sorted(map(len,ENDS.groups())),rows=rows,labs=labs,orient=orient)
 return [len(g) for g in gs],links


ROWS32 = [(0, 1, 9, 3, '2310'), (7, 3, 6, 2, '0132'), (5, 2, 0, 0, '3201'), (7, 2, 8, 2, '1023'), (8, 3, 5, 3, '1023'), (9, 2, 6, 3, '0132'), (2, 2, 0, 2, '1023'), (3, 2, 1, 0, '3201'), (1, 3, 3, 3, '1023'), (2, 3, 4, 3, '1023'), (4, 2, 1, 2, '1023'), (0, 3, 1, 1, '3201'), (2, 1, 5, 0, '3012'), (8, 1, 14, 1, '0132'), (9, 0, 13, 1, '1023'), (12, 1, 8, 0, '1023'), (9, 1, 15, 1, '0132'), (11, 0, 15, 0, '0213'), (7, 0, 3, 1, '1023'), (6, 1, 6, 0, '2031'), (10, 1, 4, 1, '0132'), (14, 0, 4, 0, '0132'), (5, 1, 2, 0, '3012'), (3, 0, 12, 0, '0132'), (7, 1, 10, 0, '3012'), (11, 1, 13, 0, '2031'), (12, 2, 15, 2, '1023'), (14, 2, 15, 3, '0132'), (13, 2, 12, 3, '0132'), (11, 3, 14, 3, '1023'), (10, 2, 13, 3, '0132'), (16, 1, 25, 3, '2310'), (23, 3, 22, 2, '0132'), (21, 2, 16, 0, '3201'), (23, 2, 24, 2, '1023'), (24, 3, 21, 3, '1023'), (25, 2, 22, 3, '0132'), (18, 2, 16, 2, '1023'), (19, 2, 17, 0, '3201'), (17, 3, 19, 3, '1023'), (18, 3, 20, 3, '1023'), (20, 2, 17, 2, '1023'), (16, 3, 17, 1, '3201'), (18, 1, 21, 0, '3012'), (24, 1, 30, 1, '0132'), (25, 0, 29, 1, '1023'), (28, 1, 24, 0, '1023'), (25, 1, 31, 1, '0132'), (27, 0, 31, 0, '0213'), (23, 0, 19, 1, '1023'), (22, 1, 22, 0, '2031'), (26, 1, 20, 1, '0132'), (30, 0, 20, 0, '0132'), (21, 1, 18, 0, '3012'), (19, 0, 28, 0, '0132'), (23, 1, 26, 0, '3012'), (27, 1, 29, 0, '2031'), (28, 2, 31, 2, '1023'), (30, 2, 31, 3, '0132'), (29, 2, 28, 3, '0132'), (27, 3, 30, 3, '1023'), (26, 2, 29, 3, '0132'), (11, 2, 26, 3, '2130'), (27, 2, 10, 3, '2130')]
LABELS32 = ['UABVAB', 'UBAUBA', 'UBAABA', 'UABAAB', 'UABAAB', 'VBAABA', 'VABAAB', 'VBAABA', 'VABAAB', 'VBAABA', 'CBAABA', 'CABAAB', 'CBAABA', 'CABAAB', 'CBAABA', 'CABAAB', 'XCBYCB', 'XBCXBC', 'XBCCBC', 'XCBCCB', 'XCBCCB', 'YBCCBC', 'YCBCCB', 'YBCCBC', 'YCBCCB', 'YBCCBC', 'ABCCBC', 'ACBCCB', 'ABCCBC', 'ACBCCB', 'ABCCBC', 'ACBCCB']

def label_type(lab):
 return min(tuple(lab[IDX[tuple(sorted((p[a],p[b])))]] for a,b in EDGES)
            for p in PERMS)

def raw_cosines(values):
 def get(a,b):return values[IDX[tuple(sorted((a,b)))]]
 out=[]
 for i,j in EDGES:
  k,h=[v for v in range(4) if v not in (i,j)]
  r,a,b,o,c,d=(get(i,j),get(i,k),get(i,h),get(k,h),get(j,h),get(j,k))
  numerator=a*b+c*d+r*a*c+r*b*d-(r*r-1)*o
  denominator=math.sqrt((2*r*a*d+r*r+a*a+d*d-1)*(2*r*b*c+r*r+b*b+c*c-1))
  out.append(numerator/denominator)
 return out

def check_dominant_demand():
 rng=random.Random(9474105)
 minimum=math.inf;maximum_asym=0.;obtuse=0
 for _ in range(2500):
  a=1+rng.uniform(.05,8);b=1+rng.uniform(.05,8)
  r=1+a+b+rng.uniform(0,12)
  lower=max(1,(a-b)**2/(r+1)-1)
  upper=1+(a+b)**2/(r-1)
  assert upper>lower
  o=lower+rng.uniform(.02,.98)*(upper-lower)
  cs=raw_cosines((r,a,b,o,a,b))
  assert all(-1<c<1 for c in cs)
  alpha=list(map(math.acos,cs))
  assert all(sum(alpha[j] for j,e in enumerate(EDGES) if v in e)<math.pi
             for v in range(4))
  theta,beta,delta=alpha[:3]
  margin=2*theta+beta+delta-math.pi
  assert margin>0
  minimum=min(minimum,margin)
  maximum_asym=max(maximum_asym,abs(alpha[1]-alpha[4]),abs(alpha[2]-alpha[5]))
  obtuse+=theta>math.pi/2
 return dict(samples=2500,obtuse_targets=obtuse,
             min_demand_margin=minimum,max_pair_angle_error=maximum_asym)

def check_packet():
 n=32;labs=[tuple(x) for x in LABELS32]
 data=analyze(ROWS32,n,labs,True)
 assert data is not None
 H={'A','B','C'};S={'U','V','X','Y'}
 types=[label_type(ll) for ll in labs];counts=collections.Counter(types)
 core={t for t in range(n) if counts[types[t]]>=3}
 noncore=set(range(n))-core
 assert noncore=={0,1,16,17}
 assert sorted(counts.values())==[1,1,1,1,3,3,5,5,6,6]
 assert H<=set().union(*(set(labs[t]) for t in core))
 for t,ll in enumerate(labs):
  assert ll[1]==ll[4] and ll[2]==ll[5]
  pair={ll[1],ll[2]}
  assert len(pair)==2 and pair<=H
  if t not in core:assert {ll[0],ll[3]}&H<=pair
 degrees={labs[G[0]//6][G[0]%6]:len(G) for G in data['groups']}
 assert degrees=={'U':6,'V':6,'X':6,'Y':6,'A':52,'B':64,'C':52}
 transport={}
 repetitions={}
 for e in S:
  pairs=set();occ=[]
  for t,ll in enumerate(labs):
   for j,label in enumerate(ll):
    if label==e:
     assert j in(0,3)
     pairs.add(tuple(sorted((ll[1],ll[2]))));occ.append((t,j))
  assert len(pairs)==1 and len(occ)==degrees[e] and len(occ)%2==0
  transport[e]=list(next(iter(pairs)))
  repetitions[e]=max(ll.count(e) for ll in labs)
 assert transport=={'U':['A','B'],'V':['A','B'],'X':['B','C'],'Y':['B','C']}
 assert repetitions=={'U':2,'V':1,'X':2,'Y':1}
 assert set.intersection(*map(set,labs))=={'B'}
 assert data['links']==[dict(V=14,E=192,F=128,chi=-50,genus=26)]
 assert data['fan_sizes']==[6]*8+[52]*4+[64]*2
 assert data['orient']=={t:(1 if t<16 else -1) for t in range(32)}
 alpha=[Fraction(2,degrees[label]) for ll in labs for label in ll]
 for G in data['groups']:assert sum(alpha[j] for j in G)==2
 maxcorner=max(sum(alpha[6*t+j] for j,e in enumerate(EDGES) if v in e)
               for t in range(32) for v in range(4))
 assert maxcorner==Fraction(503,1248) and maxcorner<1
 # A deliberately wrong cross-face map still maps the missing vertex to
 # the requested target, but violates actual labels; the checker rejects it.
 wrong=list(ROWS32);last=wrong[-1];wrong[-1]=(*last[:4],'0132')
 rejected=False
 try:invalid=analyze(wrong,n,labs,True);rejected=invalid is None
 except AssertionError:rejected=True
 assert rejected
 return dict(tetrahedra=n,face_pairs=len(ROWS32),degrees=degrees,
             vertex_links=data['links'],link_fan_sizes=data['fan_sizes'],
             oriented_circuits={labs[G[0]//6][G[0]%6]:data['circles'][i]
                                for i,G in enumerate(data['groups'])},
             protected_blocks=sorted(core),nonprotected_blocks=sorted(noncore),
             label_type_sizes=sorted(counts.values()),special_pairs=transport,
             maximum_special_multiplicity=repetitions,common_labels=['B'],
             max_normalized_corner=str(maxcorner),bad_cross_map_rejected=rejected)

if __name__=='__main__':
 if not __debug__:raise RuntimeError('Run without -O: checks require assertions.')
 print(json.dumps(dict(packet=check_packet(),analytic_crosscheck=check_dominant_demand()),
                  ensure_ascii=False,indent=2))
