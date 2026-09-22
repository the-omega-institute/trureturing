"""Independent actual-local-leaf verification of the global prefix-cylinder cover."""
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

CERTIFICATE = 'certificates/source_norms/source-budgets/adaptive_phase_cylinder_dual_verification.json'
SOURCES = ('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/58-adaptive-initial-block-recovery-and-all-schedule-budget-obstruction.md', 'frontier/source-budgets/adaptive_phase_head_input.json', 'frontier/source-budgets/balanced_profile_head_input.json', 'frontier/source-budgets/capped_head_bellman.py', 'frontier/source-budgets/adaptive_phase_cylinder_dual.py', 'frontier/source-budgets/verify_balanced_profile_tail_budget.py', 'frontier/source-budgets/balanced_profile_exponent_frontier.py')


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
    given=ctx.fresh('certificates/source_norms/source-budgets/adaptive_phase_cylinder_dual.json', 'frontier/source-budgets/adaptive_phase_cylinder_dual.py')
    frontier=ctx.fresh(FRONTIER, 'frontier/source-budgets/balanced_profile_exponent_frontier.py')
    require(given['original_labels']==data['labels'] and given['profiles']==data['profiles'] and given['prime_order']==data['prime_order'] and given['heights']==data['heights'], 'same actual candidate cover geometry')
    require(frontier['profiles']==data['profiles'], 'same geometric outside weight')
    budget=dict(C_upper=tail['C_upper'],J_upper=tail['J_upper'],T_lower=tail['independent_T_lower'],degree_records=frontier['records'])
    P=data['prime_order'];H=data['heights'];labels=data['labels'];R=[[F(x) for x in r] for r in data['profiles']]
    require(len(P)==len(H)==len(R)==20 and len(labels)==len({n for n,a in labels})==154,'full intended dimensions')
    require(data['changes']==[[39,14],[45,26],[55,28],[63,32]],'same four fixed edits')
    sizes=[p**h for p,h in zip(P,H)];require(prod(sizes)==lcm(*(n for n,a in labels)),'full original CRT period')
    units=[lcm(*(r.denominator for r in row)) for row in R]
    D=[prod(units[i:]) for i in range(len(P)+1)]
    terminal_units=[];matches=[];last=[]
    for n,a in labels:
     require(n>1 and n%2 and 0<=a<n and prod(sizes)%n==0,'actual original odd class')
     last.append(max(i for i,p in enumerate(P) if n%p==0))
    completed=[sum(1<<j for j,axis in enumerate(last) if axis<i) for i in range(len(P)+1)]
    for p,h,size,row,u in zip(P,H,sizes,R,units):
     require(row[0]==1 and len(row)==h+1 and all(F(1,p**e)<=row[e]<=row[e-1] for e in range(1,h+1)),'feasible full-history absolute cylinder caps')
     v=row[-1]*u;require(v.denominator==1,'integral terminal price');terminal_units.append(v.numerator)
     qs=[gcd(n,size) for n,a in labels]
     matches.append(tuple(sum(1<<j for j,((n,a),q) in enumerate(zip(labels,qs)) if x%q==a%q) for x in range(size)))
    counts={'leaf_evaluations':0,'whole_prefix':0,'children':0,'already_covered':0,'no_live_labels':0}
    @lru_cache(None)
    def capacity(axis,active):
     if not active:counts['no_live_labels']+=1;return D[axis]
     if active&completed[axis]:counts['already_covered']+=1;return 0
     require(axis<len(P),'complete terminal decision')
     total=sum(capacity(axis+1,active&mask) for mask in matches[axis]);counts['leaf_evaluations']+=len(matches[axis]);childcost=terminal_units[axis]*total
     if childcost<D[axis]:counts['children']+=1;return childcost
     counts['whole_prefix']+=1;return D[axis]
    upper=F(capacity(0,(1<<len(labels))-1),D[0]);lower=1-upper
    require(upper==F(given['survival_upper']) and lower==F(given['bad_lower']),'independent actual-leaf prefix cover exact equality')
    require(capacity.cache_info().currsize==given['states'],'same original-label suffix inventory')
    C,J,T=map(F,[budget['C_upper'],budget['J_upper'],budget['T_lower']]);E=F(next(x for x in budget['degree_records'] if x['total_degree_max']==7)['outside_weight']);eta=1-C-(J-1)/(T-1)
    strong=lower+C+E+(J-1)/(T-1);baseline=lower+C+(J-1)/(T-1)
    require(strong>1 and baseline<1 and lower>eta-E,'all-schedule fixed-D7 budget obstruction and baseline unresolved')
    require(given['period']==prod(sizes), 'candidate complete original period')
    require(F(given['budget_obstruction']['head_bad_lower'])==lower and F(given['budget_obstruction']['D7_fixed_score_lower'])==strong and F(given['budget_obstruction']['excess'])==strong-1, 'candidate all-schedule obstruction equals independent exact arithmetic')
    require(all(counts[key]==given['decisions'][key] for key in ('whole_prefix','children','already_covered','no_live_labels')), 'independent cover decision counts')
    result={'schema':'adaptive-phase-cylinder-dual-verification-v1','scope':'Upper bound on actual survivor mass for every law with the fixed original product-cylinder caps, including arbitrary adaptive read-once schedules; original weak-hit labels and balanced profile. Numerical prefix order belongs only to the covering certificate.','survival_upper':str(upper),'bad_lower':str(lower),'survival_upper_decimal':float(upper),'bad_lower_decimal':float(lower),'states':capacity.cache_info().currsize,'counts':counts,'fixed_D7_score_lower':str(strong),'fixed_D7_score_lower_decimal':float(strong),'baseline_score_lower':str(baseline),'baseline_score_lower_decimal':float(baseline),'fixed_D7_threshold':str(eta-E),'baseline_threshold':str(eta)}
    return ctx.finish(result)

if __name__ == '__main__':
    _io.run(CERTIFICATE, calculate, __file__)
