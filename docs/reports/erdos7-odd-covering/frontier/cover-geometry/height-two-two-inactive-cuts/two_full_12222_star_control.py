"""Finite actual-source control for the stated parallel-star cut78 subclass.
Prediction: all480 literal pair tests hold; explicit flow77 and cut77 match;
an additional inactive-root2/private18 cut has78; an18-point common law
has the stated ordered-LCM envelope79/9. This is not a source enumeration,
not a Lean proof, and not an unrestricted Erdős7 conclusion.
"""
from itertools import combinations
from fractions import Fraction as F
from collections import defaultdict,Counter
from pathlib import Path
from hashlib import sha256
import json
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", type=Path, required=True, help="Result JSON path")
args=parser.parse_args()
children={0:range(4),1:range(5),2:range(5),3:range(5)}
q={0:2,1:3,2:3,3:3}
H,K,L=0,1,2
fibres={}
for r in (0,3):
 for c in children[r]:fibres[r,c]={(g,h)for g in range(7)for h in range(7)}
fibres[1,0]={(H,0)};fibres[2,0]={(K,0)}
for c in range(1,5):
 fibres[1,c]={(H,c),(L,0)}
 fibres[2,c]={(K,c),(L,c)}
E={(r,c,g,h)for(r,c),ys in fibres.items()for(g,h)in ys}
checks=Counter()
def ck(name,value):
 if not value:raise ArithmeticError(name)
 checks[name]+=1
for r,s in combinations(range(4),2):
 for A in combinations(children[r],q[r]):
  for B in combinations(children[s],q[s]):
   union=set().union(*(fibres[r,c]for c in A),*(fibres[s,c]for c in B));counts=Counter(g for g,h in union)
   ck('literal_ternary_pair',sum(v>=3 for v in counts.values())>=3)
projection=set((g,h)for r,c,g,h in E);pc=Counter(g for g,h in projection)
ck('standalone_five_tree',sum(v>=5 for v in pc.values())>=5)
flow=defaultdict(F)
for r in (1,2):
 for c in children[r]:
  for g,h in fibres[r,c]:flow[r,c,g,h]=F(2)
flow[1,1,L,0]=F(1)
matrix=((2,2,2,0),(2,2,1,0),(2,1,0,2),(1,0,2,2))
for r,g in ((0,3),(3,4)):
 for c,row in enumerate(matrix):
  for h,w in enumerate(row):
   if w:flow[r,c,g,h]=F(w)
ck('actual_supported',set(flow)<=E)
ck('total77',sum(flow.values())==77)
for label,indices,cap in [('root',(0,),21),('child',(0,1),7),('private_column',(0,1,2),6),('entry',(0,1,2,3),2),('public_leaf',(2,3),7),('public_column',(2,),21)]:
 totals=defaultdict(F)
 for point,w in flow.items():totals[tuple(point[i]for i in indices)]+=w
 for w in totals.values():ck(label+'_capacity',0<=w<=cap)
# The source-root cut edges cover inactive roots. At active roots every
# actual point is covered by its finite private leaf or the public L/0 leaf.
private77={(r,c,g,h)for(r,c,g,h)in E if r in(1,2)and(g,h)!=(L,0)}
private78={(r,c,g,h)for(r,c,g,h)in E if r in(1,2)}
ck('all_original_points_covered77',all(r in(0,3)or p in private77 or(g,h)==(L,0)for p in E for r,c,g,h in[p]))
ck('cut77_cost',2*21+2*len(private77)+7==77)
ck('all_original_points_covered78',all(r in(0,3)or p in private78 for p in E for r,c,g,h in[p]))
ck('cut78_cost',2*21+2*len(private78)==78)
selected={(1,c,H,c)for c in range(5)}|{(2,c,K,c)for c in range(5)}|{(0,c,3,c)for c in range(4)}|{(3,c,4,c)for c in range(4)}
ck('eighteen_actual_points',len(selected)==18 and selected<=E)
ck('distinct_children',len({p[:2]for p in selected})==18)
ck('distinct_seven_leaves',len({p[2:]for p in selected})==18)
ck('column_cap_five',max(Counter(p[2]for p in selected).values())<=5)
# Solve the two prime-power congruences using the original numerical labels.
xs=[]
for r,c,g,h in sorted(selected):
 a=r+5*c;b=g+7*h
 x=a+25*((b-a)*pow(25,-1,49)%49)
 ck('original_CRT_labels',x%25==a and x%49==b)
 xs.append(x)
divisors=(1,5,7,25,35,49,175,245,1225);coeff=(1,3,3,5,9,5,15,15,25)
caps={d:F(max(Counter(x%d for x in xs).values()),18)for d in divisors}
envelope=sum(F(c)*caps[d]for d,c in zip(divisors,coeff));ck('one_law_envelope',envelope==F(79,9))
result={'scope':'One actual literal4555 finite parallel-star source, not an exhaustive classification; no Lean run','actual_points':len(E),'literal_pair_tests':checks['literal_ternary_pair'],'maximum_flow':77,'explicit_cut_capacities':[77,78],'inactive_roots_in_cut78':[0,3],'active_shapes':['12222','12222'],'selected_law_points':[list(p)for p in sorted(selected)],'ordered_LCM_caps':{str(d):str(caps[d])for d in divisors},'one_law_envelope_upper':str(envelope),'flow_atoms':[list(p)+[str(w)]for p,w in sorted(flow.items())],'check_counts':dict(checks),'total_checks':sum(checks.values()),'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k]for k in ('actual_points','literal_pair_tests','maximum_flow','explicit_cut_capacities','one_law_envelope_upper','total_checks','program_sha256')},indent=2))
