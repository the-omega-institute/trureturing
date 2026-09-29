"""Exact joint-source certificates for E9 plus late nonrooted hyperedges.

The arbitrary-family theorem is the companion ordinary mathematical proof.
This program keeps complete means and enumerates only exact low events.
No numerical optimizer or Lean proof is used.
"""
from fractions import Fraction as F
from itertools import combinations,product
from math import prod
from pathlib import Path
import json

P=(3,5,7,11,13,17,19);Q=P[1:];L=(11,13,17,19)
E9=frozenset(((5,7),(5,11),(7,17),(7,19),(11,17),(11,19),(13,17),(13,19),(17,19)))
ALL_HIGH=tuple(S for k in (3,4) for S in combinations(L,k))
FOUR_HIGH=tuple(S for S in ALL_HIGH if 19 in S)
checks=[]
def need(name,ok):
 if not ok:raise RuntimeError(name)
 if name in checks:raise RuntimeError('duplicate check name '+name)
 checks.append(name)

def calculate(last_threshold,extra):
 thresholds={5:0,7:1,11:3,13:4,17:5,19:last_threshold}
 caps={3:F(2),**{p:F(p-1,p-2-thresholds[p]) for p in Q}}
 g={p:caps[p]/(p-1) for p in P}
 def atom(p,k):return 1-caps[p]/p if k==0 else caps[p]*F(p-1,p**(k+1))
 rows=[]
 for q in Q:
  previous=tuple(p for p in Q if p<q)
  neighbors=tuple(p for p in previous if (p,q) in E9)
  terms=tuple(S[:-1] for S in extra if S[-1]==q)
  t=thresholds[q]
  low={m:F(0) for m in range(t)}
  for k3 in range(t):
   weights={p:k3+int(p in neighbors) for p in previous}
   active=tuple(p for p in previous if weights[p])
   if any(p not in active for S in terms for p in S):raise RuntimeError('nonlinear inactive variable')
   ranges=tuple(range((t-1-k3)//weights[p]+1) for p in active)
   for ks in product(*ranges):
    K=dict(zip(active,ks))
    m=k3+sum(weights[p]*K[p] for p in active)+sum(prod(K[p] for p in S) for S in terms)
    if m<t:low[m]+=atom(3,k3)*prod((atom(p,K[p]) for p in active),start=F(1))
  mean=g[3]*(1+sum((g[p] for p in previous),F(0)))+sum((g[p] for p in neighbors),F(0))+sum((prod((g[p] for p in S),start=F(1)) for S in terms),F(0))
  hinge=mean-t+sum(((t-m)*w for m,w in low.items()),F(0))
  charge=hinge/(q-2-t)
  rows.append({'q':q,'t':t,'cap':caps[q],'neighbors':neighbors,'extra_cofactor_supports':terms,'mean':mean,'low_atoms':low,'hinge':hinge,'charge':charge})
 lowV={1:F(1)}
 for p in P:
  nxt={}
  for m,w in lowV.items():
   for k in range(5//m):
    v=m*(k+1)
    nxt[v]=nxt.get(v,F(0))+w*atom(p,k)
  lowV=nxt
 EV=prod((1+g[p] for p in P),start=F(1))
 B=EV-6+sum(((6-v)*w for v,w in lowV.items()),F(0))
 s=1-sum((r['charge'] for r in rows),F(0))
 gate=321*s-49*B
 density=prod(caps.values(),start=F(1))
 return {'thresholds':thresholds,'caps':caps,'extra_supports':extra,'rows':rows,'query_mean':EV,'query_low_atoms':lowV,'query_hinge_B':B,'survivor_lower':s,'query_upper':5+B/s,'raw_gate':gate,'density':density,'head_Haar_lower':s/density,'nine_Haar_lower':gate/(616*density),'full_added_cap':sum((prod((g[p] for p in S),start=F(1)) for S in extra),F(0))}

base=calculate(6,())
four=calculate(6,FOUR_HIGH)
failed=calculate(6,ALL_HIGH)
final=calculate(7,ALL_HIGH)
base7=calculate(7,())
need('all five higher supports',len(ALL_HIGH)==5 and len(FOUR_HIGH)==4)
need('base exactly reproduces570 reserve',base['survivor_lower']==F(67038203235808184648406028960843,258635013666908098037407214625000))
need('base exactly reproduces570 query',base['query_upper']==F(1904964287547135260286877282656943722389,165993227993981410199733519903914391457))
need('four higher supports pass at t19 six',four['query_upper']<F(566,49))
need('all higher supports fail old fixed t19 six certificate',failed['query_upper']>F(566,49))
need('all higher supports pass t19 seven',final['query_upper']<F(566,49))
need('final query exact',final['query_upper']==F(224167587171895144296993552278596972445671925,19408569499185259521646920039976279342177201))
need('final reserve exact',final['survivor_lower']==F(7838365711219648132666311015826216699,30008127460703012074790172076865625000))
need('final query hinge exact',final['query_hinge_B']==F(110858473194725664986233638097168,64795630020766937106234185390625))
need('final density exact',final['density']==F(1152,35))
need('final raw gate exact',final['raw_gate']==F(346188371998272899824226991774152611457147,24767698132439755831791956763118299065625000))
need('nine Haar exact',final['nine_Haar_lower']==F(346188371998272899824226991774152611457147,502170033174842537440748281763576137215360000000))
need('nine Haar exceeds one per1500000',final['nine_Haar_lower']>F(1,1500000))
need('same-law density cancellation',final['nine_Haar_lower']==(final['raw_gate']/567)/(final['density']*F(616,567)))
need('positive seven source',final['survivor_lower']>0)
for row in final['rows']:
 q=row['q'];t=row['t'];cap=row['cap'];low=row['low_atoms']
 need('valid normalized row '+str(q),0<=t<q-2 and 0<cap<q)
 need('nonnegative row loss '+str(q),row['charge']>=0)
 need('low probability '+str(q),all(w>=0 for w in low.values()) and sum(low.values())<=1)
 need('low first moment '+str(q),sum(F(m)*w for m,w in low.items())<=row['mean'])
need('added cap exact',final['full_added_cap']==F(17,2100))
crude_s=base7['survivor_lower']-final['full_added_cap']
need('same-cap after-the-fact additive certificate fails',crude_s>0 and 5+final['query_hinge_B']/crude_s>F(566,49))
# Independently enumerate literal exponent-labelled numerical cofactor sets
# at a two-height sample. This detects inventory multiplicity mistakes.
for q in Q:
 prev=tuple(p for p in P if p<q)
 supportsets=[(3,)]+[(3,p) for p in prev if p>3]+[(p,) for p in prev if p>3 and (p,q) in E9]+[S[:-1] for S in ALL_HIGH if S[-1]==q]
 K={p:2 for p in prev}
 labels=[]
 for S in supportsets:
  labels.extend(prod(p**e for p,e in zip(S,es)) for es in product(*(range(1,K[p]+1) for p in S)))
 expected=K[3]*(1+sum(K[p] for p in prev if p>3))+sum(K[p] for p in prev if p>3 and (p,q) in E9)+sum(prod(K[p] for p in S[:-1]) for S in ALL_HIGH if S[-1]==q)
 need('literal cofactor uniqueness and count '+str(q),len(labels)==len(set(labels))==expected)

out={'kind':'ordinary all-height joint-source certificate','final':final,'old_base':base,'four_support_old_schedule':four,'all_five_old_schedule':failed,'same_final_caps_base':base7,'after_the_fact_query_upper':5+final['query_hinge_B']/crude_s,'checks':checks,'check_count':len(checks),'scope':{'globally_fixed_actual_phases':True,'all_finite_original_heights':True,'all_query_heights':True,'arbitrary_rooted_supports_size_four_plus':False,'all_nonrooted_pairs':False,'new_Lean':False}}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,default=str,indent=2)+'\n')
print('PASS',len(checks),'exact checks')
for k in ('query_upper','raw_gate','nine_Haar_lower'):print(k,str(final[k]),float(final[k]))
