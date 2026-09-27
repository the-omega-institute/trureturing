#!/usr/bin/env python3
"""Rational transport on the same support removes saturated cut78 centres.

The universal minimum-cut proof and the outer same-source construction are
in Report449. Exact finite controls exercise the construction, not replace
that proof. No original odd-covering realization or Lean claim is made.
"""
from collections import defaultdict, deque, Counter
from fractions import Fraction as Q
from itertools import product
from math import lcm
from pathlib import Path
import argparse
import json
import random


def require(value,message):
 if not value: raise ValueError(message)

class Dinic:
 def __init__(self,n): self.g=[[] for _ in range(n)]
 def add(self,u,v,cap):
  self.g[u].append([v,cap,len(self.g[v])]); self.g[v].append([u,0,len(self.g[u])-1])
  return u,len(self.g[u])-1,cap
 def flow(self,s,t,limit):
  result=0
  while result<limit:
   level=[-1]*len(self.g); level[s]=0; q=deque([s])
   while q:
    u=q.popleft()
    for v,cap,_ in self.g[u]:
     if cap and level[v]<0: level[v]=level[u]+1; q.append(v)
   if level[t]<0: break
   ptr=[0]*len(self.g)
   def dfs(u,f):
    if u==t:return f
    while ptr[u]<len(self.g[u]):
     e=self.g[u][ptr[u]]; v,cap,rev=e
     if cap and level[v]==level[u]+1:
      sent=dfs(v,min(f,cap))
      if sent:
       e[1]-=sent; self.g[v][rev][1]+=sent; return sent
     ptr[u]+=1
    return 0
   while result<limit:
    sent=dfs(s,limit-result)
    if not sent:break
    result+=sent
  return result

def flow(edges,reduce=None):
 d=Dinic(14); source=12;sink=13
 refs={}
 for i in range(5): d.add(source,i,5 if reduce==('r',i) else 6)
 for j in range(7): d.add(5+j,sink,6 if reduce==('c',j) else 7)
 for i,j in sorted(edges):refs[i,j]=d.add(i,5+j,1 if reduce==('x',i,j) else 2)
 total=d.flow(source,sink,21)
 if total!=21:return None
 return {e:cap-d.g[u][k][1] for e,(u,k,cap) in refs.items()}

def margins(f):return [sum(v for (i,j),v in f.items() if i==r) for r in range(5)],[sum(v for (i,j),v in f.items() if j==c) for c in range(7)]

def construct(edges,initial=None):
 edges=set(edges)
 require(all(type(i) is int and type(j) is int and 0<=i<5 and 0<=j<7
             for i,j in edges),'literal support coordinates')
 base=flow(edges) if initial is None else {e:initial.get(e,0) for e in edges}
 if base is None:return None
 require(initial is None or set(initial)<=edges,'initial support')
 require(all(type(v) is int and 0<=v<=2 for v in base.values()),'initial integral entries')
 r,c=margins(base)
 require(sum(base.values())==21 and max(r)<=6 and max(c)<=7,'initial feasible21 matrix')
 bad=[(i,j) for (i,j),x in base.items() if r[i]==6 and c[j]==7 and x==2]
 if len(bad)>9:raise RuntimeError('too many critical cells')
 laws=[base]; alternatives=[]
 for i,j in bad:
  for reduce in [('r',i),('c',j),('x',i,j)]:
   trial=flow(edges,reduce)
   if trial is not None:
    laws.append(trial);alternatives.append(reduce);break
  else:raise RuntimeError(('forced triple',sorted(edges),i,j))
 mean={e:sum(Q(f[e]) for f in laws)/len(laws) for e in edges}
 rr,cc=margins(mean)
 if sum(mean.values())!=21 or max(rr)>6 or max(cc)>7 or max(mean.values())>2:raise RuntimeError('capacity')
 require(all(mean[e]>0 for e,v in base.items() if v>0),'initial positive support retained')
 charges={(i,j):20*rr[i]+20*cc[j]+25*mean.get((i,j),0) for i in range(5) for j in range(7)}
 if max(charges.values())>308:raise RuntimeError(('charge',max(charges.values())))
 return {'initial_critical_cells':len(bad),'averaged_flows':len(laws),'max_local_charge':str(max(charges.values())),'alternatives':alternatives,'law':[[i,j,str(v)] for (i,j),v in sorted(mean.items())]}


def matrix_controls():
 patterns=[set(range(5))]+[set(range(5))-{i} for i in range(5)]
 counts=Counter(); worst=Q(0); worst_case=None
 for neighborhoods in product(patterns,repeat=3):
  edges={(i,j) for j,ns in enumerate(neighborhoods) for i in ns}
  ans=construct(edges)
  if ans is None:raise RuntimeError('unexpected three-column infeasibility')
  counts['three_column_feasible_supports']+=1
  value=Q(ans['max_local_charge'])
  if value>worst:worst=value;worst_case={'edges':sorted(edges),**ans}
 rng=random.Random(20260927)
 for p in [Q(1,4),Q(1,3),Q(1,2),Q(2,3),Q(3,4)]:
  for _ in range(1000):
   edges={(i,j) for i in range(5) for j in range(7) if rng.randrange(p.denominator)<p.numerator}
   counts['random_supports']+=1
   ans=construct(edges)
   if ans is None:counts['random_infeasible']+=1;continue
   counts['random_feasible']+=1
   counts['random_initial_critical_cells']+=ans['initial_critical_cells']
   value=Q(ans['max_local_charge'])
   if value>worst:worst=value;worst_case={'edges':sorted(edges),**ans}
 cut_types=[(a,b,c) for a in range(6) for b in range(8) for c in range(36) if 6*a+7*b+2*c==21]
 if cut_types!=[(0,1,7),(0,3,0),(1,1,4),(2,1,1)]:raise RuntimeError(cut_types)
 return {'cut_types':cut_types,'counts':dict(counts),'worst_tested_charge':str(worst),'worst_control':worst_case,'K43':construct({(i,j) for i in range(4) for j in range(3)})}


def check_network(atoms,source):
 require(set(atoms)<=source,'actual bridge support')
 require(sum(atoms.values())==78,'fixed flow value78')
 root,child,private,public,leaf=(defaultdict(Q) for _ in range(5))
 for (r,c,g,h),v in atoms.items():
  require(v>=0 and v<=2,'private leaf capacity')
  root[r]+=v;child[r,c]+=v;private[r,c,g]+=v
  public[g]+=v;leaf[g,h]+=v
 require(max(root.values())<=21,'root capacity')
 require(max(child.values())<=7,'child capacity')
 require(max(private.values())<=6,'private column capacity')
 require(max(public.values())<=21,'public column capacity')
 require(max(leaf.values())<=7,'public leaf capacity')
 # Sending each atom along its actual path yields a conserved feasible flow.
 return root,public


def repair(atoms,source):
 require(all(type(v) is int for v in atoms.values()),'integer initial flow')
 root,columns=check_network(atoms,source)
 blocks=[(r,g) for r in root for g in columns
         if root[r]==columns[g]==sum(v for (rr,c,gg,h),v in atoms.items() if rr==r and gg==g)==21]
 require(len(blocks)<=3 and len({r for r,g in blocks})==len(blocks)
         and len({g for r,g in blocks})==len(blocks),'disjoint saturated blocks')
 updated={p:Q(v) for p,v in atoms.items()}; changes=[]
 for r,g in blocks:
  initial={(c,h):v for (rr,c,gg,h),v in atoms.items() if rr==r and gg==g and v>0}
  info=construct(set(initial),initial)
  replacement={(c,h):Q(v) for c,h,v in info['law']}
  require(set(replacement)==set(initial) and all(replacement.values()),'exact positive support')
  for c,h in initial:updated[r,c,g,h]=replacement[c,h]
  changes.append({'root':r,'column':g,**info})
 check_network(updated,source)
 require(set(updated)==set(atoms),'no new or lost initial atom')
 for r in range(5):
  for g in range(7):
   old=sum(v for (rr,c,gg,h),v in atoms.items() if (rr,gg)==(r,g))
   new=sum(v for (rr,c,gg,h),v in updated.items() if (rr,gg)==(r,g))
   require(old==new,'integer coarse block masses unchanged')
 axes=((5,1),(1,7),(25,1),(5,7),(1,49),(25,7),(5,49),(25,49))
 coeffs=(3,3,5,9,5,15,15,25)
 cylinders=[]
 for px,py in axes:
  vals=defaultdict(Q)
  for (r,c,g,h),v in updated.items():vals[(r+5*c)%px,(g+7*h)%py]+=v
  cylinders.append(vals)
 max_full=max_other=Q(0)
 for x in range(25):
  for y in range(49):
   masses=[tab[x%px,y%py] for tab,(px,py) in zip(cylinders,axes)]
   a,b,c,d,e,f,g,h=masses
   require(c+d<=a+f,'joint subset inequality')
   charge=sum(k*v for k,v in zip(coeffs,masses))
   if (x%5,y%7) in blocks:
    require(charge==315+20*c+20*e+25*h and charge<=623,'full block coherent charge')
    max_full=max(max_full,charge)
   else:
    require(min(a,b,d)<=20,'integer deficit outside full blocks')
    require(charge<=8*a+3*b+4*d+20*f+5*e+15*g+25*h<=622,'non-full coherent bound')
    max_other=max(max_other,charge)
 # Noncoherent layouts use the existing rational cap theorem LC2 from Report449.
 bound=1+max(Q(622),max_full,max_other)/78
 require(bound<=Q(701,78)<9,'same-law all-layout theorem bound')
 return {'initial_blocks':blocks,'block_replacements':changes,
         'maximum_full_coherent_charge':str(max_full),
         'maximum_other_coherent_charge':str(max_other),
         'noncoherent_bound_from_report449':'622',
         'normalized_all_layout_upper':str(bound),
         'retained_atoms':len(updated),'coherent_centres_checked':1225,
         'law_units':[[*p,str(v)] for p,v in sorted(updated.items())]}


def verify(directory):
 result={'matrix_controls':matrix_controls(),'actual_flow_controls':{}}
 for name in ('height_two_cut78_flow_choice','height_two_cut78_forced_block'):
  data=json.loads((directory/(name+'.json')).read_text())
  source=set(map(tuple,data['source']))
  atoms={tuple(row[:4]):row[4] for row in data['bad_flow']['atoms']}
  result['actual_flow_controls'][name]=repair(atoms,source)
 result['universal_gamma_bound']='701/78'
 result['scope']='Universal ordinary support theorem plus exact controls. Repaired flows retain the same actual positive support. The all-layout bound uses the existing rational noncoherent cap theorem; finite examples do not assert original odd-covering realization or outside-cofactor lifting.'
 return result


def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
 args=parser.parse_args()
 payload=json.dumps(verify(Path(__file__).parent),indent=2)+'\n'
 args.output.write_text(payload,encoding='utf-8')
 print(payload,end='')


if __name__=='__main__':main()
