"""Independent actual-leaf grouped-cap verification of all120 fixed initial-five orders."""
from collections import Counter
from itertools import permutations
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import gcd,lcm,prod
from pathlib import Path
import importlib.util
import sys
sys.dont_write_bytecode = True

_spec = importlib.util.spec_from_file_location('adaptive_phase_io', Path(__file__).with_name('adaptive_phase_io.py'))
if _spec is None or _spec.loader is None:
    raise RuntimeError('readable canonical adaptive phase IO')
_io = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require, load_module = _io.require, _io.load_module

INPUT = 'frontier/source-budgets/adaptive_phase_head_input.json'
PROFILE = 'frontier/source-budgets/balanced_profile_head_input.json'
LITERAL = 'frontier/source-budgets/capped_head_bellman.py'
TAIL = 'certificates/source_norms/source-budgets/balanced_profile_tail_verification.json'
FRONTIER = 'certificates/source_norms/source-budgets/balanced_profile_exponent_frontier.json'

CERTIFICATE = 'certificates/source_norms/source-budgets/adaptive_phase_fixed_orders_verification.json'
SOURCES = ('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/58-adaptive-initial-block-recovery-and-all-schedule-budget-obstruction.md', 'frontier/source-budgets/adaptive_phase_head_input.json', 'frontier/source-budgets/balanced_profile_head_input.json', 'frontier/source-budgets/capped_head_bellman.py', 'frontier/source-budgets/adaptive_phase_fixed_orders.py', 'frontier/source-budgets/verify_adaptive_phase_head.py', 'frontier/source-budgets/verify_balanced_profile_tail_budget.py')


def calculate(base):
    ctx = _io.Context(base, SOURCES, __file__)
    data = ctx.read(INPUT)
    profile = ctx.read(PROFILE)
    literal = load_module('adaptive_phase_original_literals', Path(base)/LITERAL)
    original = dict(labels=[list(pair) for pair in literal.counterexample_154_labels()])
    require(data['profiles'] == profile['profiles'], 'exact canonical balanced profile')
    require([n for n,a in data['labels']] == [n for n,a in original['labels']], 'all154 original numerical moduli retained')
    require([(x,y) for x,y in zip(original['labels'],data['labels']) if x!=y] == [([39,22],[39,14]),([45,43],[45,26]),([55,11],[55,28]),([63,7],[63,32])], 'exact four globally fixed phase edits')
    tail = ctx.fresh(TAIL, 'frontier/source-budgets/verify_balanced_profile_tail_budget.py')
    require(tail['profiles'] == data['profiles'] and tail['tail_stages'] == 1879 and tail['independent_T_lower'] == '326059/4', 'same complete independent tail budget')
    adaptive=ctx.fresh('certificates/source_norms/source-budgets/adaptive_phase_head_verification.json', 'frontier/source-budgets/verify_adaptive_phase_head.py')
    reference=ctx.fresh('certificates/source_norms/source-budgets/adaptive_phase_fixed_orders.json', 'frontier/source-budgets/adaptive_phase_fixed_orders.py')
    require(adaptive['labels']==data['labels'] and adaptive['profiles']==data['profiles'] and adaptive['prime_order']==data['prime_order'] and adaptive['heights']==data['heights'], 'same independently verified adaptive5 source')
    P=tuple(data['prime_order']);H=tuple(data['heights']);labels=data['labels'];profiles=[[F(x) for x in row] for row in data['profiles']]
    require(data['profiles']==tail['profiles'],'same independently verified auxiliary budget profile')
    require(len(P)==len(H)==len(profiles)==20 and len(labels)==len({n for n,a in labels})==154,'full original dimensions')
    sizes=tuple(p**h for p,h in zip(P,H));require(prod(sizes)==lcm(*(n for n,a in labels)),'complete actual CRT period')
    units=[];leaf_units=[];masks=[]
    for p,h,size,row in zip(P,H,sizes,profiles):
     require(len(row)==h+1 and row[0]==1,'full profile with root1')
     require(all(F(1,p**e)<=row[e]<=row[e-1] and row[e]==p**(h-e)*row[h] for e in range(1,h+1)),'all proper-ancestor caps exactly implied by leaf cap')
     den=row[h].denominator;units.append(den);leaf_units.append(row[h].numerator)
     qs=[gcd(n,size) for n,a in labels]
     masks.append(tuple(sum(1<<j for j,((n,a),q) in enumerate(zip(labels,qs)) if leaf%q==a%q) for leaf in range(size)))
    scopes=[sum(1<<i for i,p in enumerate(P) if n%p==0) for n,a in labels]
    @lru_cache(None)
    def completed(remaining):return sum(1<<j for j,scope in enumerate(scopes) if not scope&remaining)
    @lru_cache(None)
    def denominator(remaining):return prod(units[i] for i in range(len(P)) if remaining>>i&1)
    @lru_cache(None)
    def meta(order):
     remaining=sum(1<<i for i in order);return remaining,denominator(remaining),completed(remaining)
    counts={'row_evaluations':0,'actual_leaf_groupings':0,'distinct_cost_groups':0,'positive_group_allocations':0}
    @lru_cache(None)
    def grouped(axis,active):
     counts['actual_leaf_groupings']+=len(masks[axis]);return tuple(Counter(active&mask for mask in masks[axis]).items())
    @lru_cache(None)
    def value(order,active):
     if not active:return 0
     remaining,den,hit=meta(order)
     if active&hit:return den
     require(bool(order),'resolved terminal')
     axis=order[0];rest=order[1:]
     costs=sorted((value(rest,hits),multiplicity) for hits,multiplicity in grouped(axis,active))
     remaining_mass=units[axis];objective=0
     for cost,multiplicity in costs:
      amount=min(remaining_mass,multiplicity*leaf_units[axis]);objective+=amount*cost;remaining_mass-=amount
      if amount:counts['positive_group_allocations']+=1
      if remaining_mass==0:break
     require(remaining_mass==0,'normalized actual-leaf capped row')
     require(den==units[axis]*meta(rest)[1],'common exact value scale')
     counts['row_evaluations']+=1;counts['distinct_cost_groups']+=len(costs)
     return objective
    refs={tuple(row['prime_order']):row for row in reference['records']};require(len(refs)==len(reference['records'])==120,'120 unique reference orders')
    C,J,T=map(F,[tail['C_upper'],tail['J_upper'],tail['independent_T_lower']]);suffix=tuple(range(5,len(P)));records=[]
    for permutation in permutations(range(5)):
     order=permutation+suffix;named=tuple(P[i] for i in order);epsilon=F(value(order,(1<<len(labels))-1),prod(units));score=epsilon+C+(J-1)/(T-1)
     require(named in refs,'every intended order present');ref=refs[named]
     require(epsilon==F(ref['epsilon']) and score==F(ref['score']),'every independent exact fixed-order value matches')
     require(score>1,'this fixed initial-five order fails the stated baseline budget')
     records.append({'prime_order':list(named),'epsilon_exact':str(epsilon),'epsilon_decimal':float(epsilon),'baseline_score_exact':str(score),'baseline_score_decimal':float(score)})
    best=min(records,key=lambda row:F(row['epsilon_exact']));av=F(adaptive['records'][0]['epsilon_exact']);asc=F(adaptive['records'][0]['baseline_score_exact']);gap=F(best['epsilon_exact'])-av
    require(gap>0 and asc<1 and F(best['baseline_score_exact'])>1,'strict adaptive5 improvement crosses baseline threshold')
    require(F(best['baseline_score_exact'])-asc==gap,'same constant charge and moment cost')
    result={'schema':'adaptive-phase-fixed-orders-verification-v1','scope':'All120 permutations of the first5 named primes with the remaining15 in numerical order. Exact globally fixed weak-hit phases and balanced profile. No claim over all20! fixed orders.','count':120,'records':records,'best':best,'adaptive5_epsilon_exact':str(av),'adaptive5_baseline_score_exact':str(asc),'adaptive5_strict_gain':str(gap),'adaptive5_strict_gain_decimal':float(gap),'flat_profile_identity_verified':True,'aggregate_unique_value_states':value.cache_info().currsize,'counts':counts}
    return ctx.finish(result)

if __name__ == '__main__':
    _io.run(CERTIFICATE, calculate, __file__)
