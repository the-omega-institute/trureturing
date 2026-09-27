"""Exact examples for pure-support-preserving prefix averaging.

The general theorem is ordinary mathematics in the companion note. These
finite examples distinguish its hypotheses; they are not a Lean proof.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from hashlib import sha256
import json

parser=ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
checks=Counter()
def ck(name,condition):
 checks[name]+=1
 if not condition:raise ArithmeticError(name)

def cap(p,e):
 return F(1) if e==0 else F(1,p-1) if e==1 else F(1,(p-2)*p**(e-1))

def pure_law(p,forbidden,depth=3):
 atoms=[x for x in range(p**depth) if all(x%(p**e)!=a for e,a in forbidden)]
 roots=Counter(x%p for x in atoms)
 weights={x:F(1,(p-1)*roots[x%p]) for x in atoms}
 ck('normalized_pure_law',sum(weights.values(),F())==1)
 return weights

rho3=pure_law(3,((1,2),(2,1),(3,4)))
rho5=pure_law(5,((1,4),(2,1),(3,2)))
atoms=list(product(rho3,rho5))
ck('toy_joint_atoms',len(atoms)==1316)
mu3={a:sum((w for x,w in rho3.items() if x%9==a),F()) for a in range(9)}
mu5={b:sum((w for y,w in rho5.items() if y%25==b),F()) for b in range(25)}
prefixes=[(a,b) for a,b in product(range(9),range(25)) if mu3[a]*mu5[b]]

def legal(c,a,b):
 if c==0:return a!=7 and not(a%3==0 and b%5==0)
 return b!=3 and not(a==4 and b%5==1)

f=[]
averages=[]
for c in range(2):
 values={(x,y):F(((c+2)*x+(c+3)*y+x*y)%11,10) if legal(c,x%9,y%25) else F() for x,y in atoms}
 table={ab:F() for ab in prefixes}
 for (x,y),value in values.items():
  table[x%9,y%25]+=rho3[x]*rho5[y]*value
 for (a,b),mass in table.items():
  table[a,b]=mass/(mu3[a]*mu5[b])
  ck('averaged_density_within_box',0<=table[a,b]<=1)
  ck('actual_head_support_preserved',legal(c,a,b) or table[a,b]==0)
 oldmass=sum((rho3[x]*rho5[y]*values[x,y] for x,y in atoms),F())
 newmass=sum((mu3[a]*mu5[b]*table[a,b] for a,b in prefixes),F())
 ck('each_cell_mass_preserved',oldmass==newmass)
 f.append(values);averages.append(table)

def literal_screens(values):
 screens={}
 for e3,e5 in product(range(4),repeat=2):
  bins=defaultdict(F)
  for (x,y),mass in values.items():
   bins[x%(3**e3),y%(5**e5)]+=mass
  scale=cap(3,e3)*cap(5,e5)
  for r3,r5 in product(range(3**e3),range(5**e5)):
   screens[e3,e5,r3,r5]=bins[r3,r5]/scale
 ck('all6240_literal_queries',len(screens)==6240)
 return screens

def finite_menu(p,rho,mu):
 result={0:[('whole',dict(mu))],1:[]}
 for root in range(p):
  if not any(x%p==root for x in rho):continue
  result[1].append((f'root:{root}',{a:(mass/cap(p,1) if a%p==root else F()) for a,mass in mu.items()}))
 for atom,mass in mu.items():
  if not mass:continue
  witnesses=[x for x in rho if x%(p*p)==atom]
  kappa=max(rho[x]/cap(p,3) for x in witnesses)
  ck('constant_density_on_surviving_prefix',all(rho[x]/cap(p,3)==kappa for x in witnesses))
  result[1].append((f'leaf:{atom}',{a:(mass/cap(p,2) if a==atom else F()) for a in mu}))
  result[1].append((f'deep:{atom}',{a:(kappa if a==atom else F()) for a in mu}))
 return result

menu3=finite_menu(3,rho3,mu3)
menu5=finite_menu(5,rho5,mu5)
comparisons=[]
for central in ((F(1),F()),(F(),F(1)),(F(1),F(1)),(F(2,3),F(4,5))):
 old={(x,y):rho3[x]*rho5[y]*sum((central[c]*f[c][x,y] for c in range(2)),F()) for x,y in atoms}
 new={(x,y):rho3[x]*rho5[y]*sum((central[c]*averages[c][x%9,y%25] for c in range(2)),F()) for x,y in atoms}
 oldqueries=literal_screens(old);newqueries=literal_screens(new)
 combined={ab:sum((central[c]*averages[c][ab] for c in range(2)),F()) for ab in prefixes}
 for support3,support5 in product(range(2),repeat=2):
  oldmax=max(value for (e3,e5,r3,r5),value in oldqueries.items() if (e3>0)==bool(support3) and (e5>0)==bool(support5))
  newmax=max(value for (e3,e5,r3,r5),value in newqueries.items() if (e3>0)==bool(support3) and (e5>0)==bool(support5))
  candidates=[]
  for (label3,row3),(label5,row5) in product(menu3[support3],menu5[support5]):
   value=sum((combined[a,b]*row3[a]*row5[b] for a,b in prefixes),F())
   candidates.append(value)
  finite=max(candidates)
  ck('averaging_does_not_increase_fullheight_supremum',newmax<=oldmax)
  ck('finite_menu_exact_for_averaged_kernel',finite==newmax)
  comparisons.append({'central_coefficients':list(map(str,central)),'support':[support3,support5],'old':str(oldmax),'averaged':str(newmax),'finite_menu':str(finite)})

# Same q² masses and capacities, different named deeper-query readings.
sevenA=pure_law(7,((1,0),(2,1),(3,2)))
sevenB=pure_law(7,((1,0),(2,1),(3,51)))
prefix7A=[sum((mass for x,mass in sevenA.items() if x%49==a),F()) for a in range(49)]
prefix7B=[sum((mass for x,mass in sevenB.items() if x%49==a),F()) for a in range(49)]
ck('same_q2_mass_table',prefix7A==prefix7B)
ck('different_fixed343_query',sevenA.get(2,F())==0 and sevenB[2]==F(1,288))
ck('same_q2_atom_mass',prefix7A[2]==F(1,48))

# Descendant closure is necessary: a singleton charged menu can increase.
selected=sevenA[51]
average_density=selected/prefix7A[2]
restricted_before=F()
restricted_after=average_density*sevenA[100]
ck('restricted_menu_counterexample',average_density==F(1,6) and restricted_after==F(1,1728)>restricted_before)

# Merely having root/deep caps is insufficient for rho-conditional averaging.
general={}
for x in range(27):
 if x%3==2:continue
 if x%3==1:general[x]=F(1,18)
 elif x in(0,9):general[x]=F(1,100)
 elif x==18:general[x]=F(1,10)
 else:general[x]=F(19,300)
ck('general_rho_normalized',sum(general.values(),F())==1)
for e in range(1,4):
 for root in range(3**e):
  mass=sum((value for x,value in general.items() if x%(3**e)==root),F())
  ck('general_rho_obeys_caps',mass<=cap(3,e))
old={x:(mass if x in(0,9) else F()) for x,mass in general.items()}
prefix_mass=sum((mass for x,mass in general.items() if x%9==0),F())
retained=sum(old.values(),F())
new={x:(mass*retained/prefix_mass if x%9==0 else F()) for x,mass in general.items()}
def one_norm(measure):
 return max(sum((mass for x,mass in measure.items() if x%(3**e)==root),F())/cap(3,e) for e in range(1,4) for root in range(3**e))
oldnorm=one_norm(old);newnorm=one_norm(new)
ck('general_rho_averaging_counterexample',oldnorm==F(9,100) and newnorm==F(3,20)>oldnorm)

# The same unary masses and edge probabilities do not determine a joint union.
root_triples=list(product(range(1,7),range(1,11),range(1,13)))
edge77=lambda x:x[0]==1 and x[1]==1
edge91A=lambda x:x[0]==1 and x[2]==1
edge91B=lambda x:x[0]==2 and x[2]==1
survivorsA=sum(not(edge77(x) or edge91A(x)) for x in root_triples)
survivorsB=sum(not(edge77(x) or edge91B(x)) for x in root_triples)
ck('same_first_edge_mass',sum(edge77(x) for x in root_triples)==12)
ck('same_second_edge_mass',sum(edge91A(x) for x in root_triples)==sum(edge91B(x) for x in root_triples)==10)
ck('different_shared_endpoint_union',survivorsA==699 and survivorsB==698)
ck('fixed_actual_second_residue',79%7==2 and 79%13==1)

result={'schema':'pure-support-prefix-averaging-checks-v1','status':'PASS','optimizer_used':False,'new_lean_verification':False,'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'check_count':sum(checks.values()),'checks':dict(sorted(checks.items())),'toy_actual_joint_atoms':len(atoms),'toy_prefix_atoms':len(prefixes),'toy_queries_per_measure':6240,'fullheight_comparisons':comparisons,'same_prefix_different_literal_query':{'prime':7,'pureA':[[1,0],[2,1],[3,2]],'pureB':[[1,0],[2,1],[3,51]],'shared_prefix2_mass':str(prefix7A[2]),'query_modulus':343,'query_residue':2,'readingA':'0','readingB':str(sevenB[2])},'restricted_menu_failure':{'query_modulus':343,'query_residue':100,'before':'0','after':str(restricted_after)},'general_rho_caps_only_failure':{'prime':3,'old_norm':str(oldnorm),'new_norm':str(newnorm),'rho_terminal_masses':[[x,str(mass)] for x,mass in general.items()]},'shared_endpoint_union_failure':{'primes':[7,11,13],'first_original':[77,1],'second_original_A':[91,1],'second_original_B':[91,79],'first_edge_mass':'1/60','second_edge_mass':'1/72','survivorA':str(F(survivorsA,720)),'survivorB':str(F(survivorsB,720)),'difference':'1/720'},'scope':'Finite exact illustrations and hypothesis counterexamples. The arbitrary-height/source averaging theorem is the ordinary argument in the companion note; no finite scan replaces that proof.'}
args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','checks':result['check_count'],'comparisons':len(comparisons),'same_prefix_readings':['0',str(sevenB[2])],'caps_only_failure':[str(oldnorm),str(newnorm)]},sort_keys=True))
