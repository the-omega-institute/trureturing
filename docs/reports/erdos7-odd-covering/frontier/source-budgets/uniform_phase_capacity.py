"""Global partial-cylinder obstruction to one fixed balanced-profile budget."""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from math import gcd,prod
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True

_spec=importlib.util.spec_from_file_location('uniform_phase_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require,load_module=_io.require,_io.load_module

CERTIFICATE='certificates/source_norms/source-budgets/uniform_phase_capacity.json'
SOURCES=('certificate_io.py','frontier/source-budgets/adaptive_phase_io.py','problem-details/59-terminal-phase-elimination-and-uniform-balanced-profile-obstruction.md','problem-details/58-adaptive-initial-block-recovery-and-all-schedule-budget-obstruction.md','frontier/source-budgets/uniform_phase_capacity_input.json','frontier/source-budgets/uniform_phase_private_witnesses_input.json','frontier/source-budgets/balanced_profile_head_input.json','frontier/source-budgets/capped_head_bellman.py','frontier/source-budgets/verify_balanced_profile_tail_budget.py')

def evaluate(data,terminal_factor=True):
 P=tuple(data['prime_order']);H=tuple(data['heights']);L=tuple(tuple(v) for v in data['labels']);R=tuple(tuple(F(x) for x in row) for row in data['profiles']);core=sum(p<23 for p in P)
 sizes=[p**h for p,h in zip(P,H)];unit=[row[-1].denominator for row in R];price=[row[-1].numerator for row in R];D=[prod(unit[i:]) for i in range(len(P)+1)]
 require(len(L)==len({m for m,a in L})==154 and core==7,'original154 core shape')
 require(all(m>1 and m%2 and 0<=a<m and prod(sizes)%m==0 for m,a in L),'all actual full moduli')
 scopes=[sum(1<<i for i,p in enumerate(P) if m%p==0) for m,a in L]
 completed=[sum(1<<j for j,s in enumerate(scopes) if s<(1<<i)) for i in range(len(P)+1)]
 matches=[]
 for i,(size,row) in enumerate(zip(sizes,R)):
  require(row[0]==1 and len(row)==H[i]+1 and all(F(1,P[i]**e)<=row[e]<=row[e-1] for e in range(1,H[i]+1)),'full feasible profiles')
  q=[gcd(m,size) for m,a in L]
  matches.append(tuple(sum(1<<j for j,((m,a),v) in enumerate(zip(L,q)) if x%v==a%v) for x in range(size)))
 if terminal_factor:
  require(all((s>>core).bit_count()<=1 for s in scopes),'disjoint terminal scopes')
  require(all(h==1 for h in H[core:]),'terminal height1')
  leaf_values=[{} for _ in P]
  for i in range(core,len(P)):
   for j,(m,a) in enumerate(L):
    if m%P[i]==0:leaf_values[i].setdefault(a%P[i],0);leaf_values[i][a%P[i]]|=1<<j
 @lru_cache(None)
 def cap(i,active):
  if not active:return D[i]
  if active&completed[i]:return 0
  if terminal_factor and i==core:
   numerator=1
   for k in range(core,len(P)):
    n=sum(bool(active&mask) for mask in leaf_values[k].values())
    numerator*=min(unit[k],price[k]*(P[k]-n))
   return numerator
  require(i<len(P),'resolved full leaf')
  grouped=Counter(active&mask for mask in matches[i]);v=sum(mul*cap(i+1,mask) for mask,mul in grouped.items())*price[i]
  return min(D[i],v)
 U=F(cap(0,(1<<len(L))-1),D[0]);return dict(survival_upper=str(U),bad_lower=str(1-U),bad_lower_float=float(1-U),states=cap.cache_info().currsize)


def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    d=ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json')
    profile=ctx.read('frontier/source-budgets/balanced_profile_head_input.json')
    literal=load_module('uniform_phase_original_labels',Path(base)/'frontier/source-budgets/capped_head_bellman.py')
    old=dict(labels=[list(v) for v in literal.counterexample_154_labels()],prime_order=profile['prime_order'],heights=profile['heights'])
    tail=ctx.fresh('certificates/source_norms/source-budgets/balanced_profile_tail_verification.json','frontier/source-budgets/verify_balanced_profile_tail_budget.py')
    require([n for n,a in d['labels']]==[n for n,a in old['labels']],'same complete original154 modulus list')
    require(d['profiles']==tail['profiles']==profile['profiles'],'same certified balanced profile')
    require(d['prime_order']==old['prime_order'] and d['heights']==old['heights'],'same named axes and heights')
    changes=[{'modulus':n,'original':a,'new':b} for (n,a),(n2,b) in zip(old['labels'],d['labels']) if a!=b]
    require([[row['modulus'],row['new']] for row in changes]==d['changes']==[[25,13],[39,14],[45,26],[55,28],[63,32],[189,29],[225,11]],'exact seven committed edits')
    oldcap=evaluate(d,False);newcap=evaluate(d,True)
    C,J,T=map(F,[tail['C_upper'],tail['J_upper'],tail['independent_T_lower']]);eta=1-C-(J-1)/(T-1);lower=F(newcap['bad_lower']);score=lower+C+(J-1)/(T-1)
    require(T==F(326059,4),'same existing continuation threshold')
    require(F(oldcap['bad_lower'])<eta<lower and score>1,'stronger partial-cylinder certificate crosses fixed baseline threshold')
    require(all(34%n!=a for n,a in d['labels']),'explicit uncovered actual integer34')
    witnesses=ctx.read('frontier/source-budgets/uniform_phase_private_witnesses_input.json')
    require(witnesses['found']==len(witnesses['private_witnesses'])==154 and not witnesses['unresolved_moduli'] and not witnesses['comparable_containments'],'complete private-witness table')
    for label,witness in zip(d['labels'],witnesses['private_witnesses']):
        n,a=label;x=witness['witness']
        require(witness['modulus']==n and witness['residue']==a and isinstance(x,int) and 0<=x<witnesses['window'],'private integer with correct original class')
        require([(m,b) for m,b in d['labels'] if x%m==b]==[(n,a)],'private integer hits this class and no other')
    palette={n for n,a in d['labels']}
    require(all(divisor in palette for n in palette for divisor in range(2,n+1) if n%divisor==0),'numerical palette closed under every nontrivial divisor')
    actual_primes=sorted(n for n in palette if all(n%d for d in range(2,n)))
    require(actual_primes==d['prime_order'],'initial odd-prime support')
    result={'schema':'all-schedule-balanced-budget-obstruction-v1','scope':'Global partial-cylinder-cap certificate, valid for every adaptive read-once law with the named deterministic full-history caps. Excludes only the fixed sufficient budget, not noncoverage.','changes':changes,'old_prefix':oldcap,'partial_cylinder':newcap,'C_upper':str(C),'J_upper':str(J),'T_lower':str(T),'eta':str(eta),'base_score_lower':str(score),'base_score_lower_decimal':float(score),'strict_margin':str(lower-eta),'uncovered_witness':34,'all154_witness_checks':True}
    result['private_witness_verification']=dict(count=154,bound_exclusive=witnesses['window'],class_membership_checks=154*154,all_classes_irredundant=True,nontrivial_divisor_closed=True,prime_support=actual_primes)
    return ctx.finish(result)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
