#!/usr/bin/env python3
"""Supplementary finite checks for CFMP written Sections 111-118.
Run with Python 3 without -O. No Lean or interval certification is claimed.
The fixed face tables reproduce topology without rerunning discovery search.
"""
from itertools import permutations
from collections import defaultdict, Counter
from fractions import Fraction
import json, math, random
E=((0,1),(0,2),(0,3),(2,3),(1,3),(1,2));IX={e:i for i,e in enumerate(E)}
P=list(permutations(range(4)))
def odd(p):return sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))%2
class DSU:
 def __init__(self,n):self.p=list(range(n))
 def find(self,x):
  while self.p[x]!=x:self.p[x]=self.p[self.p[x]];x=self.p[x]
  return x
 def union(self,x,y):self.p[self.find(x)]=self.find(y)
 def groups(self):
  g=defaultdict(list)
  for x in range(len(self.p)):g[self.find(x)].append(x)
  return list(g.values())
def typ(ll):return min(tuple(ll[IX[tuple(sorted((p[i],p[j])))]] for i,j in E) for p in P)
def validate(rows,labs):
 n=len(labs);ed=DSU(6*n);vd=DSU(4*n);ends=DSU(12*n);dual=DSU(n);fm={};fan=defaultdict(list)
 for t,f,u,g,ps in rows:
  p=tuple(map(int,ps));assert 0<=t<n and 0<=u<n
  assert sorted(p)==list(range(4)) and p[f]==g and odd(p)==1
  assert (t,f)!=(u,g) and (t,f)not in fm and (u,g)not in fm
  fm[t,f]=(u,g,p);fm[u,g]=(t,f,tuple(p.index(i) for i in range(4)));dual.union(t,u)
  for i in range(4):
   if i!=f:vd.union(4*t+i,4*u+p[i])
  for j,(a,b) in enumerate(E):
   if f in(a,b):continue
   jj=IX[tuple(sorted((p[a],p[b])))];assert labs[t][j]==labs[u][jj]
   v1=6*t+j;v2=6*u+jj;ed.union(v1,v2)
   for k in(0,1):
    x,y=2*v1+k,2*v2+(k^(p[a]>p[b]));ends.union(x,y);fan[x].append(y);fan[y].append(x)
 assert len(fm)==4*n and len(ed.groups())==len(set(''.join(labs))) and len(dual.groups())==1
 assert all(ends.find(2*j)!=ends.find(2*j+1) for j in range(6*n))
 assert len(vd.groups())==1
 circles={}
 for group in ed.groups():
  t,j=divmod(group[0],6);a,b=E[j];entry=min(v for v in range(4) if v not in(a,b));st=(t,a,b,entry);start=st;seen=set();cc=[]
  while st not in seen:
   seen.add(st);tt,a,b,en=st;cc.append(6*tt+IX[tuple(sorted((a,b)))]);out=next(v for v in range(4) if v not in(a,b,en));uu,gg,p=fm[tt,out];st=(uu,p[a],p[b],gg)
  assert st==start and sorted(cc)==group
  circles[labs[t][j]]=cc
 for group in ends.groups():
  assert all(len(fan[x])==2 for x in group)
  seen={group[0]};todo=list(seen)
  while todo:
   for y in fan[todo.pop()]:
    if y not in seen:seen.add(y);todo.append(y)
  assert seen==set(group)
 degrees={k:len(v)for k,v in circles.items()}
 assert degrees==(dict(U=6,V=6,X=6,Y=6,A=29,B=52,C=27) if n==22 else dict(U=4,V=4,W=4,A=20,B=16))
 assert len(ends.groups())==2*len(degrees)
 types=[typ(ll)for ll in labs];counts=Counter(types)
 assert sorted(counts.values())==([1]*10+[2]*6 if n==22 else [1]*4+[2]*2)
 H=set('ABC') if n==22 else set('AB');S=set('UVXY') if n==22 else set('UVW');pairs={}
 for e in S:
  ps=set()
  for ll in labs:
   for j,c in enumerate(ll):
    if c==e:
     assert j in(0,3);ps.add(tuple(sorted((ll[1],ll[2]))))
  assert len(ps)==1;pairs[e]=next(iter(ps))
 assert set().union(*(set(p)for p in pairs.values()))==H
 seed=S|set().union(*(set(p)for p in pairs.values()))
 certified={t for t,tp in enumerate(types) if counts[tp]>=2 and
            all(set((labs[t][j],labs[t][k]))&seed for j,k in((0,3),(1,4),(2,5)))}
 assert len(certified)==(12 if n==22 else 4)
 # The concurrent three-label diagonal seed rule also has no seed in
 # the 22-block example: no duplicated type has all opposite pairs equal.
 diagonal_seeds={t for t,ll in enumerate(labs) if counts[types[t]]>=2
                 and all(ll[j]==ll[k] for j,k in((0,3),(1,4),(2,5)))}
 assert not diagonal_seeds
 for t,ll in enumerate(labs):
  assert ll[1]==ll[4] and ll[2]==ll[5] and ll[1]!=ll[2]
  assert {ll[1],ll[2]}<=H
  if t not in certified:assert set((ll[0],ll[3]))&H<=set((ll[1],ll[2]))
 alpha=[Fraction(2,degrees[l])for ll in labs for l in ll]
 assert all(sum(alpha[i]for i in cc)==2 for cc in circles.values())
 maxcorner=max(sum(alpha[6*t+j]for j,edge in enumerate(E)if v in edge)for t in range(n)for v in range(4))
 assert maxcorner==(Fraction(313,702) if n==22 else Fraction(29,40)) and maxcorner<1
 common=set.intersection(*(set(ll) for ll in labs));assert common==({'B'} if n==22 else {'A','B'})
 return dict(tetrahedra=n,face_pairs=len(rows),degrees=degrees,
             link=dict(V=2*len(degrees),E=6*n,F=4*n,chi=2*len(degrees)-2*n,genus=1-len(degrees)+n),fan_sizes=sorted(map(len,ends.groups())),
             named_type_multiplicities=sorted(counts.values()),three_copy_types=0,
             duplicate_diagonal_seed_blocks=sorted(diagonal_seeds),
             two_copy_protected_blocks=sorted(certified),transverse_pairs=pairs,
             common_labels=sorted(common),max_initial_corner_over_pi=str(maxcorner))

def raw(values):
 def at(i,j):return values[IX[tuple(sorted((i,j)))]]
 out=[]
 for i,j in E:
  k,h=[x for x in range(4)if x not in(i,j)]
  r,a,b,o,c,d=(at(i,j),at(i,k),at(i,h),at(k,h),at(j,h),at(j,k))
  out.append((a*b+c*d+r*a*c+r*b*d-(r*r-1)*o)/math.sqrt((r*r+a*a+d*d+2*r*a*d-1)*(r*r+b*b+c*c+2*r*b*c-1)))
 return out

def analytic_checks():
 rng=random.Random(9474107);trans=Counter();maxdiff=0.;dominant=0
 for _ in range(6000):
  a=1+math.exp(rng.uniform(-1,4));b=1+math.exp(rng.uniform(-1,4));r=1+math.exp(rng.uniform(-1,4));o=1+math.exp(rng.uniform(-1,4))
  Dr=r*r+a*a+b*b+2*r*a*b-1;Do=o*o+a*a+b*b+2*o*a*b-1
  L=(a+b)**2-(r-1)*(o-1);M=(r+1)*(o+1)-(a-b)**2
  cs=raw((r,a,b,o,a,b))
  delta=-(a-b)*L/math.sqrt(Dr*Do)
  err=abs((cs[1]-cs[2])-delta)/max(1,abs(delta));maxdiff=max(maxdiff,err)
  assert err<2e-12
  if M<0:
   assert L>0 and cs[0]>1 and cs[3]>1
   j,k=(1,2) if a>b else(2,1)
   assert cs[j]<-1+1e-11 and cs[k]>1-1e-11
   assert (a>b) if j==1 else (b>a)
   trans['A' if j==1 else 'B']+=1
 for _ in range(3000):
  a=1+rng.uniform(.05,20);b=1+rng.uniform(.05,20);r=1+a+b+rng.uniform(0,20)
  lo=max(1,(a-b)**2/(r+1)-1);hi=1+(a+b)**2/(r-1)
  o=lo+rng.uniform(.02,.98)*(hi-lo);cs=raw((r,a,b,o,a,b))
  assert all(-1<c<1 for c in cs)
  al=list(map(math.acos,cs));assert 2*al[0]+al[1]+al[2]>math.pi
  dominant+=1
 # Algebraic bookkeeping required by the new cap proof.
 for d in range(6,100):
  for m in(0,1):
   g=d-m
   assert g-2*(2-m)==d+m-4>=2
 return dict(raw_identity_samples=6000,transverse_flat_samples=dict(trans),max_relative_identity_error=maxdiff,
             dominant_local_samples=dominant,exact_capacity_count_cases=188)

def check_degree4():
 rng=random.Random(9474111); good=0;star_o=0;minr=1.;mino=1.;mincostr=100.;mincosto=100.
 for _ in range(40000):
  a=1+math.exp(rng.uniform(0,5));b=1+math.exp(rng.uniform(0,5));w=a+b
  r=1+w+rng.uniform(0,1)*w*w/4
  T=(r-1)/(r+1);F=2*(r-1)/w**2-T*(a-b)**2/w**2
  if F>=1/3:continue
  Dr=r*r+a*a+b*b+2*r*a*b-1
  q=(2*a*b+r*(a*a+b*b)-Dr/2)/(r*r-1)
  if q<=1:continue
  cs=raw((r,a,b,q,a,b))
  if not all(-1<x<1 for x in cs):continue
  al=list(map(math.acos,cs));assert abs(al[0]-math.pi/3)<1e-9
  K=((math.sqrt(a*a-1)+math.sqrt(b*b-1))/w)**2
  lr2=K*T
  assert lr2>1/3
  o=1+w*w/(r-1)+rng.uniform(0,10)
  lo2=K*(o-1)/(o+1)
  assert lo2>1/7
  denominator=1+2*(r-1)/w**2
  assert abs(denominator-(1+F+T*(a-b)**2/w**2))<1e-12*denominator
  assert denominator<7/3
  cr=12*math.atan(math.sqrt(3*lr2));co=6*math.atan(math.sqrt(3*lo2))
  assert cr>3*math.pi and co>math.pi and cr+co>4*math.pi
  minr=min(minr,lr2);mino=min(mino,lo2);mincostr=min(mincostr,cr);mincosto=min(mincosto,co)
  D=o*o+a*a+b*b+2*o*a*b-1
  q2=(2*a*b+o*(a*a+b*b)-D/2)/(o*o-1)
  if q2>1 and all(-1<c<1 for c in raw((o,a,b,q2,a,b))):star_o+=1
  good+=1
  if good==3000:break
 assert good==3000
 return dict(paired_flat_partner_cases=good,other_star_mean_feasible=star_o,
             min_sample_lambda_r_squared=minr,min_sample_lambda_o_squared=mino,
             min_sample_disjoint_cost_r_over_pi=mincostr/math.pi,min_sample_half_cost_o_over_pi=mincosto/math.pi)

ROWS22 = [[8, 3, 7, 2, '0132'], [2, 0, 0, 1, '1023'], [7, 3, 2, 2, '0132'], [6, 2, 8, 2, '1023'], [2, 1, 6, 3, '2310'], [2, 3, 0, 0, '2310'], [5, 3, 1, 3, '1023'], [4, 3, 0, 3, '1023'], [3, 3, 4, 2, '0132'], [1, 0, 0, 2, '2310'], [1, 1, 5, 2, '3201'], [3, 2, 1, 2, '1023'], [6, 0, 3, 1, '1302'], [4, 1, 4, 0, '3012'], [19, 2, 18, 3, '0132'], [18, 2, 3, 0, '1302'], [6, 1, 19, 3, '2310'], [7, 0, 8, 1, '1023'], [5, 1, 8, 0, '1023'], [7, 1, 5, 0, '3012'], [15, 3, 11, 2, '0132'], [17, 2, 16, 3, '0132'], [17, 3, 9, 1, '3201'], [11, 0, 15, 2, '2310'], [11, 1, 9, 0, '1023'], [16, 2, 11, 3, '0132'], [10, 3, 9, 3, '1023'], [14, 3, 13, 2, '0132'], [13, 3, 9, 2, '0132'], [14, 2, 10, 1, '2310'], [10, 2, 12, 2, '1023'], [10, 0, 12, 3, '3201'], [20, 1, 13, 1, '0132'], [20, 0, 15, 0, '0213'], [15, 1, 21, 0, '1023'], [12, 1, 13, 0, '1023'], [12, 0, 21, 1, '1023'], [14, 1, 17, 0, '1023'], [16, 0, 17, 1, '1023'], [14, 0, 16, 1, '1230'], [18, 1, 21, 3, '1302'], [21, 2, 18, 0, '1302'], [20, 3, 19, 0, '1230'], [20, 2, 19, 1, '3012']]
LABELS22 = ['UABVAB', 'UBAUBA', 'VBAVBA', 'UABAAB', 'UBAABA', 'UABBAB', 'VABAAB', 'VABBAB', 'VBABBA', 'XBCYBC', 'XCBXCB', 'YCBYCB', 'XBCBBC', 'XCBBCB', 'XBCCBC', 'YBCBBC', 'YBCCBC', 'YCBCCB', 'AABCAB', 'ABACBA', 'ABCBBC', 'ACBBCB']

ROWS8 = [[1, 2, 5, 3, '0132'], [5, 2, 0, 1, '2310'], [4, 3, 0, 0, '2310'], [1, 3, 4, 2, '0132'], [0, 3, 3, 1, '3201'], [3, 2, 2, 1, '2310'], [2, 0, 3, 0, '0132'], [0, 2, 3, 3, '0132'], [7, 3, 1, 1, '3201'], [2, 2, 6, 2, '1023'], [6, 3, 1, 0, '2310'], [7, 2, 2, 3, '0132'], [5, 0, 7, 1, '1230'], [6, 1, 6, 0, '3012'], [7, 0, 5, 1, '1230'], [4, 0, 4, 1, '1230']]
LABELS8 = ['UABVAB', 'VABWAB', 'WABUAB', 'UBAUBA', 'VBAABA', 'VBAABA', 'WBAABA', 'WBAABA']


def main():
    a=validate(ROWS22,LABELS22);b=validate(ROWS8,LABELS8)
    # An edge-preserving, orientation-compatible map is necessary. Reject
    # a map that still sends the omitted vertex to the requested face but
    # corrupts the named-edge transport.
    bad=[list(row) for row in ROWS22]
    t,f,u,g,_=bad[0]
    for p in P:
        if p[f]==g and odd(p) and any(LABELS22[t][j]!=LABELS22[u][IX[tuple(sorted((p[i],p[k])))]] for j,(i,k) in enumerate(E) if f not in(i,k)):
            bad[0][4]=''.join(map(str,p));break
    else:
        raise AssertionError('No invalid-map negative control found')
    rejected=False
    try:validate(bad,LABELS22)
    except AssertionError:rejected=True
    assert rejected
    out=dict(packet22=a,packet8=b,analytic=analytic_checks(),partner_transfer=check_degree4(),invalid_map_rejected=rejected,
             status='finite auxiliary checks; written proofs carry the universal claims')
    print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__':
    main()
