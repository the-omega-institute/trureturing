"""Independent actual-local-leaf verification of the fixed seven-phase obstruction."""
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import gcd,lcm,prod
from pathlib import Path
import importlib.util
import sys
sys.dont_write_bytecode = True

_spec=importlib.util.spec_from_file_location('uniform_phase_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require,load_module=_io.require,_io.load_module

CERTIFICATE='certificates/source_norms/source-budgets/uniform_phase_capacity_verification.json'
SOURCES=('certificate_io.py','frontier/source-budgets/adaptive_phase_io.py','problem-details/59-terminal-phase-elimination-and-uniform-balanced-profile-obstruction.md','frontier/source-budgets/uniform_phase_capacity_input.json','frontier/source-budgets/uniform_phase_private_witnesses_input.json','frontier/source-budgets/balanced_profile_head_input.json','frontier/source-budgets/capped_head_bellman.py','frontier/source-budgets/uniform_phase_capacity.py','frontier/source-budgets/verify_balanced_profile_tail_budget.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    data=ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json')
    require(sha256(ctx.raw('frontier/source-budgets/uniform_phase_capacity_input.json')).hexdigest()=='ea227d216660f496ecb3a2c89dbc145605f0ad83c94e5996a7ee76d746ea712b','exact clean seven-phase input')
    profile_row=ctx.read('frontier/source-budgets/balanced_profile_head_input.json')
    profile=dict(records=[profile_row])
    literal=load_module('uniform_phase_original_literals',Path(base)/'frontier/source-budgets/capped_head_bellman.py')
    original=dict(labels=[list(x) for x in literal.counterexample_154_labels()],prime_order=profile_row['prime_order'],heights=profile_row['heights'])
    tail=ctx.fresh('certificates/source_norms/source-budgets/balanced_profile_tail_verification.json','frontier/source-budgets/verify_balanced_profile_tail_budget.py')
    candidate=ctx.fresh('certificates/source_norms/source-budgets/uniform_phase_capacity.json','frontier/source-budgets/uniform_phase_capacity.py')
    given=candidate
    PRIVATE='frontier/source-budgets/uniform_phase_private_witnesses_input.json'
    read=ctx.read
    P=tuple(data['prime_order']);H=tuple(data['heights']);labels=data['labels'];R=[[F(x) for x in row] for row in data['profiles']]
    require(list(P)==original['prime_order'] and list(H)==original['heights'],'full original coordinate inventory')
    require(data['profiles']==profile['records'][0]['profiles']==tail['profiles'],'unchanged exact balanced profile')
    require(len(labels)==len({m for m,a in labels})==154 and [m for m,a in labels]==[m for m,a in original['labels']],'all154 original numerical labels')
    changes=[{'modulus':m,'original':a,'new':b} for (m,a),(n,b) in zip(original['labels'],labels) if a!=b]
    require(changes==given['changes'] and [(r['modulus'],r['new']) for r in changes]==[(25,13),(39,14),(45,26),(55,28),(63,32),(189,29),(225,11)],'exact seven global fixed edits')
    require(all(m>1 and m%2 and 0<=a<m for m,a in labels),'canonical literal odd classes')
    sizes=[p**h for p,h in zip(P,H)];period=prod(sizes);require(period==lcm(*(m for m,a in labels)),'complete CRT period')
    units=[lcm(*(x.denominator for x in row)) for row in R];D=[prod(units[i:]) for i in range(len(P)+1)]
    prices=[];matches=[];last=[];scopes=[]
    for m,a in labels:
     scope=tuple(i for i,p in enumerate(P) if m%p==0);last.append(max(scope));scopes.append(scope)
    completed=[sum(1<<j for j,lastaxis in enumerate(last) if lastaxis<i) for i in range(len(P)+1)]
    for p,h,row,size,unit in zip(P,H,R,sizes,units):
     require(len(row)==h+1 and row[0]==1 and all(F(1,p**e)<=row[e]<=row[e-1] for e in range(1,h+1)),'feasible full-transcript profile')
     v=row[-1]*unit;require(v.denominator==1,'integer terminal capacity');prices.append(v.numerator)
     factors=[gcd(m,size) for m,a in labels]
     matches.append(tuple(sum(1<<j for j,((m,a),q) in enumerate(zip(labels,factors)) if x%q==a%q) for x in range(size)))
    core=7;require(P[:core]==(3,5,7,11,13,17,19) and all(h==1 for h in H[core:]),'exact core7 and terminal height1')
    leaf_ids=[]
    for axis in range(core,len(P)):leaf_ids.append(tuple(j for j,(m,a) in enumerate(labels) if m%P[axis]==0))
    require(sum(len(ids) for ids in leaf_ids)==76 and all(sum(i>=core for i in scope)<=1 for scope in scopes),'complete76 one-leaf labels')
    require(all(34%m!=a for m,a in labels),'actual uncovered integer34')
    require(any(4%m==a for m,a in labels),'do not reuse covered integer4')
    private=read(PRIVATE);witnesses=private['private_witnesses'];require(len(witnesses)==154 and private['window']==300000,'complete private witness inventory')
    for j,((m,a),w) in enumerate(zip(labels,witnesses)):
     require((w['modulus'],w['residue'])==(m,a) and type(w['witness']) is int and 0<=w['witness']<private['window'],'literal class/private witness correspondence')
     hits=[k for k,(n,b) in enumerate(labels) if w['witness']%n==b]
     require(hits==[j],'each integer hits its own class and no other class')
    moduli={m for m,a in labels};divisor_checks=0
    for m in moduli:
     for d in range(3,m+1,2):
      if m%d==0:require(d in moduli,'all nontrivial divisors remain in palette');divisor_checks+=1
    odd_primes=[p for p in range(3,max(P)+1,2) if all(p%d for d in range(2,int(p**.5)+1))]
    require(list(P)==odd_primes and all(any(m%p==0 for m in moduli) for p in P),'initial odd-prime segment is exact support')
    private_summary={'verified':154,'pairwise_checks':154*154,'window':private['window'],'maximum_witness':max(w['witness'] for w in witnesses),'nontrivial_divisor_checks':divisor_checks,'odd_prime_support':list(P)}
    records=[]
    for terminal in (False,True):
     counts={'actual_leaf_evaluations':0,'terminal_states':0,'terminal_incidence_checks':0,'whole_prefix':0,'children':0,'already_forbidden':0,'no_live_labels':0}
     @lru_cache(None)
     def cost(axis,active):
      if not active:counts['no_live_labels']+=1;return D[axis]
      if active&completed[axis]:counts['already_forbidden']+=1;return 0
      if terminal and axis==core:
       answer=1
       for leafaxis,ids in enumerate(leaf_ids,core):
        forbidden={labels[j][1]%P[leafaxis] for j in ids if active>>j&1};counts['terminal_incidence_checks']+=len(ids)
        allowed=P[leafaxis]-len(forbidden);answer*=min(units[leafaxis],prices[leafaxis]*allowed)
       require(0<=answer<=D[axis],'actual terminal product cover cost')
       counts['terminal_states']+=1;return answer
      require(axis<len(P),'resolved terminal state')
      children=prices[axis]*sum(cost(axis+1,active&mask) for mask in matches[axis]);counts['actual_leaf_evaluations']+=len(matches[axis])
      if children<D[axis]:counts['children']+=1;return children
      counts['whole_prefix']+=1;return D[axis]
     survival=F(cost(0,(1<<154)-1),D[0]);bad=1-survival
     row={'terminal_product':terminal,'survival_upper':str(survival),'bad_lower':str(bad),'bad_lower_decimal':float(bad),'states':cost.cache_info().currsize,'counts':counts};records.append(row);cost.cache_clear()
     reference=given['partial_cylinder' if terminal else 'old_prefix']
     require(survival==F(reference['survival_upper']) and bad==F(reference['bad_lower']) and row['states']==reference['states'],'independent exact cover bound and states')
    C,J,T=map(F,[tail['C_upper'],tail['J_upper'],tail['independent_T_lower']]);eta=1-C-(J-1)/(T-1);score=F(records[1]['bad_lower'])+C+(J-1)/(T-1)
    require(eta==F(given['eta']) and score==F(given['base_score_lower'])>1,'correctT-1 all-schedule baseline obstruction')
    require(F(records[0]['bad_lower'])<eta<F(records[1]['bad_lower']),'terminal product improvement essential here')
    require(all(records[0][k]==candidate['old_prefix'][k] for k in ('survival_upper','bad_lower','states')),'complete independent numerical-prefix comparison')
    require(F(candidate['strict_margin'])==score-1 and candidate['uncovered_witness']==34,'same exact margin and actual witness')
    result={'schema':'independent-seven-phase-global-cylinder-obstruction-v1','scope':'Same154 numerical moduli and balanced profile, seven globally fixed phase edits. All-schedule global cylinder-cap obstruction only to the fixed baseline C/J/T certificate; not coverage. Clean mathematical source has no inherited computed epsilon field. Every original class has an independently checked private integer witness.','changes':changes,'private_witness_verification':private_summary,'uncovered_integer':34,'profiles':data['profiles'],'records':records,'C_upper':str(C),'J_upper':str(J),'T_lower':str(T),'eta':str(eta),'baseline_score_lower':str(score),'baseline_score_lower_decimal':float(score),'strict_margin':str(score-1)}
    candidate_private=candidate['private_witness_verification']
    require(private_summary['verified']==candidate_private['count']==154 and private_summary['pairwise_checks']==candidate_private['class_membership_checks'] and private_summary['window']==candidate_private['bound_exclusive'] and private_summary['odd_prime_support']==candidate_private['prime_support'],'same independent private-witness and palette result')
    return ctx.finish(result)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
