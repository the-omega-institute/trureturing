"""Exact certificate for the three-loop F13 bouquet."""
from itertools import product
P=13
C=[[7,4,8],[11,12,3],[11,6,5],[4,9,8],[4,7,12],[2,4,1]]
K=3
def rank(a):
 a=[list(r) for r in a]; n=len(a[0]) if a else 0; d=0
 for col in range(n):
  i=next((i for i in range(d,len(a)) if a[i][col]%P),None)
  if i is None: continue
  a[d],a[i]=a[i],a[d]; inv=pow(a[d][col],P-2,P); a[d]=[v*inv%P for v in a[d]]
  for j in range(len(a)):
   if j!=d:
    u=a[j][col]; a[j]=[(v-u*w)%P for v,w in zip(a[j],a[d])]
  d+=1
 return d

import itertools
for T in itertools.combinations(C,3):
 assert rank(list(T))==3,('central triple',T)
count=0
for choices in product(range(6),repeat=K):
 if sum(2 if c==5 else int(c>0) for c in choices)!=K: continue
 rr=[]
 for j,c in enumerate(choices):
  a,b=C[2*j:2*j+2]
  opts=[[],[a],[b],[[(u+v)%P for u,v in zip(a,b)]],[[(u-v)%P for u,v in zip(a,b)]],[a,b]]
  rr.extend(opts[c])
 assert rank(rr)==K,choices; count+=1
assert count==88
rows=[]
for j in range(K):
 for c in C[2*j:2*j+2]:
  for sign in (1,-1):
   row=c+[0]*K; row[K+j]=sign%P; rows.append(row)
assert rank(rows)==2*K
edges=[(0,i) for i in range(1,2*K+1)]+[(2*j+1,2*j+2) for j in range(K)]
assignments=[]
for sides in product((0,1),repeat=2*K+1):
 assignments.append((sides,sum(sides[u]!=sides[v] for u,v in edges)))
for mask in range(1<<(4*K)):
 f=[rows[i] for i in range(4*K) if mask>>i&1]; g=[rows[i] for i in range(4*K) if not mask>>i&1]
 r=[sum((mask>>(4*j+i))&1 for i in range(4)) for j in range(K)]
 active=sum(x>0 for x in r); complement=sum(x<4 for x in r); partial=sum(0<x<4 for x in r); e=sum([0,0,1,2,2][x] for x in r)
 assert rank(f)==active+min(K,e),(mask,'rankF')
 assert rank(g)==complement+min(K,6-e),(mask,'rankG')
 mc=min(hh+sum(sides[1+i//2]!=((mask>>i)&1) for i in range(4*K)) for sides,hh in assignments)
 assert rank(f)+rank(g)-2*K==mc,(mask,rank(f)+rank(g)-2*K,mc)
print('PASS bouquet3 F13: all 4096 regions; 88 virtual patterns; full support rank6')