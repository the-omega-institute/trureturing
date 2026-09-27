"""Independent actual-leaf adaptive5 audit with every original ancestor cap."""
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import gcd,lcm,prod
from pathlib import Path
import importlib.util
import json
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

CERTIFICATE = 'certificates/source_norms/source-budgets/adaptive_phase_head_verification.json'
SOURCES = ('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/58-adaptive-initial-block-recovery-and-all-schedule-budget-obstruction.md', 'frontier/source-budgets/adaptive_phase_head_input.json', 'frontier/source-budgets/balanced_profile_head_input.json', 'frontier/source-budgets/capped_head_bellman.py', 'frontier/source-budgets/adaptive_phase_head.py', 'frontier/source-budgets/verify_balanced_profile_tail_budget.py', 'frontier/source-budgets/balanced_profile_exponent_frontier.py')

def factor(n):
 out={};p=2
 while p*p<=n:
  while n%p==0:out[p]=out.get(p,0)+1;n//=p
  p+=1
 if n>1:out[n]=out.get(n,0)+1
 return out

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
    profiles=tuple(tuple(F(v) for v in row) for row in data['profiles']);labels=data['labels']
    frontier=ctx.fresh(FRONTIER, 'frontier/source-budgets/balanced_profile_exponent_frontier.py')
    require(frontier['profiles'] == data['profiles'], 'same full geometric exponent budget')
    extra=next(row['outside_weight'] for row in frontier['records'] if row['total_degree_max']==7)
    factors=[factor(n) for n,a in labels];P=tuple(sorted(set().union(*(set(f) for f in factors))));H=tuple(max(f.get(p,0) for f in factors) for p in P)
    require(list(P)==data['prime_order'] and list(H)==data['heights'],'actual complete prime-power heights')
    require(len(labels)==len({n for n,a in labels})==154,'154 distinct numerical moduli')
    require(all(n>1 and n%2 and 0<=a<n for n,a in labels),'literal odd congruences')
    sizes=tuple(p**h for p,h in zip(P,H));units=tuple(lcm(*(v.denominator for v in row)) for row in profiles)
    require(prod(sizes)==lcm(*(n for n,a in labels)),'complete actual period')
    scopes=tuple(sum(1<<i for i,p in enumerate(P) if p in f) for f in factors)
    local_match=[];leaf_paths=[];initial_capacities=[]
    for p,h,size,row,den in zip(P,H,sizes,profiles,units):
     require(len(row)==h+1 and row[0]==1 and all(F(1,p**e)<=row[e]<=row[e-1] for e in range(1,h+1)),'feasible absolute depth caps')
     mods=[gcd(n,size) for n,a in labels]
     local_match.append(tuple(sum(1<<j for j,((n,a),q) in enumerate(zip(labels,mods)) if leaf%q==a%q) for leaf in range(size)))
     offsets=[];caps=[]
     for e,cap in enumerate(row):
      offsets.append(len(caps));amount=cap*den;require(amount.denominator==1,'integral capacity units');caps.extend([amount.numerator]*(p**e))
     initial_capacities.append(tuple(caps));leaf_paths.append(tuple(tuple(offsets[e]+leaf%(p**e) for e in range(h+1)) for leaf in range(size)))
    @lru_cache(None)
    def denominator(remaining):return prod(units[i] for i in range(len(P)) if remaining>>i&1)
    @lru_cache(None)
    def completed(remaining):return sum(1<<j for j,scope in enumerate(scopes) if scope&remaining==0)
    candidate=ctx.fresh('certificates/source_norms/source-budgets/adaptive_phase_head.json', 'frontier/source-budgets/adaptive_phase_head.py')
    require(candidate['labels']==labels and candidate['profiles']==data['profiles'] and candidate['prime_order']==list(P) and candidate['heights']==list(H), 'candidate actual input and coordinate inventory')
    require(F(candidate['C_upper'])==F(tail['C_upper']) and F(candidate['J_upper'])==F(tail['J_upper']) and candidate['T_lower']==tail['independent_T_lower'] and F(candidate['D7_outside_upper'])==F(extra), 'exact independent continuation constants, not coarse frontier bounds')
    expected={}
    for row in candidate['records']:
        require(row['block_size'] not in expected, 'unique block result')
        expected[row['block_size']]=(candidate,row)
    require(set(expected)=={5}, 'exact bounded adaptive5 audit')
    records=[]
    for block in (5,):
     counts=dict(states=0,nonterminal_states=0,row_evaluations=0,leaf_evaluations=0,positive_allocations=0,ancestor_subtractions=0)
     @lru_cache(None)
     def value(remaining,active):
      if not active:return 0
      if active&completed(remaining):return denominator(remaining)
      require(remaining>0,'resolved terminal')
      possible=remaining&((1<<block)-1)
      if not possible:possible=remaining&-remaining
      best=None
      while possible:
       bit=possible&-possible;possible-=bit;axis=bit.bit_length()-1;rest=remaining^bit
       costs=tuple(value(rest,active&mask) for mask in local_match[axis]);counts['leaf_evaluations']+=len(costs)
       capacities=list(initial_capacities[axis]);objective=0;selected=0
       for leaf in sorted(range(sizes[axis]),key=lambda x:(costs[x],x)):
        path=leaf_paths[axis][leaf];amount=min(capacities[node] for node in path)
        if amount:
         for node in path:
          capacities[node]-=amount;require(capacities[node]>=0,'actual leaf allocation within every ancestor');counts['ancestor_subtractions']+=1
         selected+=amount;objective+=amount*costs[leaf];counts['positive_allocations']+=1
        if capacities[0]==0:break
       require(selected==units[axis] and capacities[0]==0,'normalized actual row')
       require(denominator(remaining)==units[axis]*denominator(rest),'common exact scale across selected axes')
       counts['row_evaluations']+=1
       if best is None or objective<best:best=objective
       if best==0:break
      counts['nonterminal_states']+=1
      return best
     numerator=value((1<<len(P))-1,(1<<len(labels))-1);epsilon=F(numerator,prod(units));candidate,row=expected[block]
     require(epsilon==F(row['epsilon_exact']),'independent actual-leaf exact match')
     counts['states']=value.cache_info().currsize
     require(counts['states']==row['states'] and counts['nonterminal_states']==row['decision_states'],'same reached state inventory')
     C,J,T,E=map(F,[candidate['C_upper'],candidate['J_upper'],candidate['T_lower'],candidate['D7_outside_upper']]);baseline=epsilon+C+(J-1)/(T-1);score=baseline+E
     require(baseline==F(row['baseline_score_exact']) and score==F(row['D7_score_exact']) and baseline<1,'independent score arithmetic')
     out={'block_size':block,'epsilon_exact':str(epsilon),'epsilon_decimal':float(epsilon),'baseline_score_exact':str(baseline),'baseline_score_decimal':float(baseline),'D7_score_exact':str(score),'D7_score_decimal':float(score),'counts':counts};records.append(out);print(json.dumps(out),flush=True);value.cache_clear()
    result={'schema':'adaptive-phase-head-verification-v1','scope':'Exact optimum inside initial block5 with numerical suffix; four globally fixed residue changes, all154 moduli and balanced full-prefix caps unchanged. No full20 adaptive conclusion.','prime_order':list(P),'heights':list(H),'profiles':data['profiles'],'labels':labels,'records':records}
    return ctx.finish(result)

if __name__ == '__main__':
    _io.run(CERTIFICATE, calculate, __file__)
