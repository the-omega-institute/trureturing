"""One weighted selector inventory strictly strengthens all subset budgets.
Report497: literal cofactor boxes and complete rational vertex enumeration.
Standard library only. No actual-source or global mass gain is claimed.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations,product
from pathlib import Path
import argparse,json
from math import prod

PROFILES=((2,2,-2,2,2,1,1),(10,-2,0,2,1,1,1),(-3,0,0,2,2,1,2))
WEIGHT=(1,1,2)
SUBSETS=tuple(tuple((mask>>i)&1 for i in range(3)) for mask in range(1,8))
EXPECTED=(20,22,40,24,40,42,58)
def need(test,message):
 if not test:raise ValueError(message)
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path)
args=parser.parse_args()

def boxes(s):
 a=tuple(max(1,x) for x in s[:3])+s[3:]
 b=tuple(max(1,-x) for x in s[:3])+s[3:]
 return set(product(*(range(f) for f in a))),set(product(*(range(f) for f in b)))
AB=[boxes(s) for s in PROFILES]
labels=set().union(*(a|b for a,b in AB))
patterns=Counter((tuple(int(d in a) for a,b in AB),tuple(int(d in b) for a,b in AB)) for d in labels)
def capacity(w):
 return sum(n*max(sum(x*y for x,y in zip(w,a)),sum(x*y for x,y in zip(w,b)))
            for (a,b),n in patterns.items())
need(tuple(map(capacity,SUBSETS))==EXPECTED and capacity(WEIGHT)==80,
     'literal subset and weighted capacities')
# Separate maxima need not use the same selector. Locate the exact labels
# responsible for N111+N001=82 versus N112=80.
conflicts=[]
for d in labels:
 a=tuple(int(d in x) for x,y in AB);b=tuple(int(d in y) for x,y in AB)
 slack=max(sum(a),sum(b))+max(a[2],b[2])-max(sum(w*x for w,x in zip(WEIGHT,a)),
                                                        sum(w*x for w,x in zip(WEIGHT,b)))
 if slack:
  conflicts.append({'old_cofactor':prod(p**e for p,e in zip((3,5,7,11,13,17,19),d)),
                    'A':list(a),'B':list(b),'separate_maximum_slack':slack})
conflicts.sort(key=lambda x:x['old_cofactor'])
need([c['old_cofactor'] for c in conflicts]==[3,33]
     and all(c['A']==[1,1,0] and c['B']==[0,0,1]
             and c['separate_maximum_slack']==1 for c in conflicts),
     'exact two original-cofactor selector conflicts')
# No weighted inequality is assumed: both selector alternatives are checked
# at every contributing numerical old-cofactor label.
for d in labels:
 for selector in (0,1):
  contribution=sum(w*int(d in AB[i][selector]) for i,w in enumerate(WEIGHT))
  bound=max(sum(w*int(d in AB[i][a]) for i,w in enumerate(WEIGHT)) for a in (0,1))
  need(contribution<=bound,'one fixed selector across all three points')

def constraints(axis,weighted):
 out=[(tuple(-int(i==j) for i in range(3)),0) for j in range(3)]
 for w in SUBSETS:
  rhs=capacity(w)
  if sum(w)==1:rhs=min(rhs,axis)
  out.append((w,rhs))
 if weighted:out.append((WEIGHT,capacity(WEIGHT)))
 return out

def solve(rows,rhs):
 A=[[F(x) for x in row]+[F(b)] for row,b in zip(rows,rhs)]
 for col in range(3):
  pivot=next((j for j in range(col,3) if A[j][col]),None)
  if pivot is None:return None
  A[col],A[pivot]=A[pivot],A[col]
  A[col]=[x/A[col][col] for x in A[col]]
  for j in range(3):
   if j==col:continue
   coeff=A[j][col];A[j]=[x-coeff*y for x,y in zip(A[j],A[col])]
 return tuple(A[i][-1] for i in range(3))

def vertices(axis,weighted):
 cons=constraints(axis,weighted);out=set();bases=0
 for ids in combinations(range(len(cons)),3):
  v=solve([cons[i][0] for i in ids],[cons[i][1] for i in ids])
  if v is None:continue
  bases+=1
  if all(sum(a*x for a,x in zip(row,v))<=b for row,b in cons):out.add(v)
 need(out,'nonempty vertex set')
 return sorted(out),bases

def certificate(weighted):
 V,n=vertices(22,weighted);W,m=vertices(28,weighted)
 val,i,j=min((sum((22-t)*(28-u) for t,u in zip(v,w))-58,i,j)
             for i,v in enumerate(V) for j,w in enumerate(W))
 return {'axis23_vertices':[[str(x) for x in v] for v in V],
  'axis29_vertices':[[str(x) for x in v] for v in W],
  'nonsingular_bases':[n,m],'vertex_pairs':len(V)*len(W),
  'minimum':str(val),'minimum_at':[i,j],
  'minimizing_axes':[list(map(str,V[i])),list(map(str,W[j]))]}
old=certificate(False);new=certificate(True)
need(F(old['minimum'])==2 and F(new['minimum'])==6,'strict improvement')
old_t=(20,20,18);old_u=(16,18,24)
for axis,v in ((22,old_t),(28,old_u)):
 need(all(sum(a*x for a,x in zip(row,v))<=b for row,b in constraints(axis,False)),
      'old minimizer obeys every subset budget')
need(sum((22-t)*(28-u) for t,u in zip(old_t,old_u))-58==2,'old sharp witness')
need(sum(w*v for w,v in zip(WEIGHT,old_u))==82>80,
     'all subset budgets fail to enforce the weighted constraint')
new_t=(16,20,22);new_u=(20,20,0)
for axis,v in ((22,new_t),(28,new_u)):
 need(all(sum(a*x for a,x in zip(row,v))<=b for row,b in constraints(axis,True)),
      'weighted minimizer feasible')
need(sum((22-t)*(28-u) for t,u in zip(new_t,new_u))-58==6,'new sharp witness')
out={'verified':True,'profiles':list(map(list,PROFILES)),
 'profile_indices_in_report495':[110,8038,14062],'subset_capacities':list(EXPECTED),
 'weight':list(WEIGHT),'weighted_capacity':80,'label_count':len(labels),
 'membership_pattern_counts':[{'A':list(a),'B':list(b),'count':n}
                              for (a,b),n in sorted(patterns.items())],
 'separate_subset_sum_capacity':capacity((1,1,1))+capacity((0,0,1)),
 'selector_conflict_labels':conflicts,
 'old_subset_certificate':old,'weighted_certificate':new,
 'excluded_old_minimizer':{'axis23':list(old_t),'axis29':list(old_u),
                         'weighted_axis29_load':82},
 'sharp_weighted_minimizer':{'axis23':list(new_t),'axis29':list(new_u)},
 'old_survivor_sum_bound':str(F(2,616)),'new_survivor_sum_bound':str(F(6,616)),
 'old_isolated_threshold':str(F(2,3*616)),'new_isolated_threshold':str(F(6,3*616)),
 'common_pair_threshold':'1/3696','Lean_rerun':False,
 'boundary':'Weighted necessary budgets preserve the same selector for each full original label. Only the axis constraints are strengthened; the mixed term keeps total capacity58. No claim that any relaxed minimizer is arithmetically realizable. This improves an already known hyperedge at the common threshold and proves no new global mass bound or unrestricted noncoverage.'}
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==out,'retained result differs')
print(json.dumps({'weighted_capacity':80,'old_minimum':old['minimum'],
 'new_minimum':new['minimum'],'new_vertex_pairs':new['vertex_pairs'],
 'survivor_sum_lower':out['new_survivor_sum_bound']},indent=2))
