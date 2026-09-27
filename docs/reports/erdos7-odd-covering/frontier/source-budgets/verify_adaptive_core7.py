"""Independent maximum-survival recurrence for arbitrary adaptive core order, then terminals."""
from collections import Counter,defaultdict
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import gcd,isqrt,lcm,prod
from pathlib import Path
import argparse
import importlib.util
import json
import sys
import time
sys.dont_write_bytecode=True
_spec=importlib.util.spec_from_file_location('adaptive_core_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require=_io.require

CERTIFICATE='certificates/source_norms/source-budgets/adaptive_core7_verification.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/64-adaptive-core-policy-and-continuous-stoploss-optima.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md', 'problem-details/62-expanded-stopping-cutoffs-for-the-seven-phase-head.md', 'problem-details/63-squared-load-stoploss-continuation.md', 'certificates/source_norms/source-budgets/square_stoploss_curve_verification.json', 'frontier/source-budgets/verify_square_stoploss_curve.py', 'certificates/source_norms/source-budgets/expanded_stop_head.json', 'frontier/source-budgets/expanded_stop_head.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    data=ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json')
    require(sha256(ctx.raw('frontier/source-budgets/uniform_phase_capacity_input.json')).hexdigest()=='ea227d216660f496ecb3a2c89dbc145605f0ad83c94e5996a7ee76d746ea712b','locked literal seven-phase input')
    allowance=ctx.fresh('certificates/source_norms/source-budgets/square_stoploss_curve_verification.json','frontier/source-budgets/verify_square_stoploss_curve.py')
    fixed=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_head.json','frontier/source-budgets/expanded_stop_head.py')
    LIMIT=2_000_000;SECONDS=300
    class ResourceStop(Exception):
        pass
    P,H,labels=data['prime_order'],data['heights'],data['labels']
    R=[list(map(F,row)) for row in data['profiles']]
    require(P[:7]==[3,5,7,11,13,17,19] and len(P)==len(H)==len(R)==20 and P==sorted(P),'exact core and terminal coordinates')
    require(len(labels)==len({m for m,a in labels})==154 and all(m>1 and m%2 and 0<=a<m for m,a in labels),'complete distinct odd original labels')
    sizes=[p**h for p,h in zip(P,H)]
    require(prod(sizes)==lcm(*(m for m,a in labels)),'complete original CRT alphabets')
    U=[r[-1].denominator for r in R]
    A=[r[-1].numerator for r in R]
    depth_checks=0
    for p,h,r in zip(P,H,R):
        require(len(r)==h+1 and r[0]==1,'complete depth profiles')
        for e in range(1,h+1):
            require(r[e]==p**(h-e)*r[h] and F(1,p**e)<=r[e]<=r[e-1],'flat uniform-feasible absolute cylinder caps')
            depth_checks+=1
    support=[sum(1<<i for i,p in enumerate(P) if m%p==0) for m,a in labels]
    core_ids=[j for j,s in enumerate(support) if s<128]
    terminal_ids=[[j for j,s in enumerate(support) if s>>i&1] for i in range(7,20)]
    require(len(core_ids)==78 and sum(map(len,terminal_ids))==76 and all(h==1 for h in H[7:]),'core78 and terminal76 geometry')
    require(all((s>>7).bit_count()<=1 for s in support),'each noncore label has exactly one terminal coordinate')
    complete=[sum(1<<j for j in core_ids if support[j]&remaining==0) for remaining in range(128)]
    terminal_units=prod(U[7:])
    denominators=[terminal_units*prod(U[i] for i in range(7) if remaining>>i&1) for remaining in range(128)]
    leaf_patterns=[]
    for axis in range(7):
        factors=[gcd(m,sizes[axis]) for m,a in labels]
        actual_masks=[sum(1<<j for j,((m,a),factor) in enumerate(zip(labels,factors)) if x%factor==a%factor)
                      for x in range(sizes[axis])]
        patterns=tuple(sorted(Counter(actual_masks).items()))
        require(sum(count for mask,count in patterns)==sizes[axis],'all actual leaves counted')
        leaf_patterns.append(patterns)

    counts={'memo_states':0,'terminal_states':0,'coordinate_actions':0,'pattern_intersections':0,
            'groups':0,'greedy_groups':0,'absorbing_bad_calls':0,'absorbing_safe_calls':0,
            'terminal_label_tests':0,'perfect_survival_shortcuts':0}
    root_actions={}
    root_choice=None
    started=time.monotonic()

    def value(remaining,active):
        if active&complete[remaining]:
            counts['absorbing_bad_calls']+=1
            return 0
        if not active:
            counts['absorbing_safe_calls']+=1
            return denominators[remaining]
        return nonconstant(remaining,active)

    @lru_cache(None)
    def nonconstant(remaining,active):
        nonlocal root_choice
        if counts['memo_states']>=LIMIT or time.monotonic()-started>=SECONDS:
            raise ResourceStop('nonconstant memo-state or wall-clock bound reached')
        counts['memo_states']+=1
        if not remaining:
            answer=1
            for axis,ids in enumerate(terminal_ids,7):
                forbidden={labels[j][1]%P[axis] for j in ids if active>>j&1}
                counts['terminal_label_tests']+=len(ids)
                answer*=min(U[axis],A[axis]*(P[axis]-len(forbidden)))
            require(0<=answer<=terminal_units,'attainable exact terminal survival')
            counts['terminal_states']+=1
            return answer
        best=-1
        choice=None
        # Descending numerical action order fixes ties without reading a candidate.
        for axis in range(6,-1,-1):
            if not remaining>>axis&1:
                continue
            following=remaining^(1<<axis)
            require(denominators[remaining]==U[axis]*denominators[following],'action-independent exact state denominator')
            groups=Counter()
            for mask,multiplicity in leaf_patterns[axis]:
                groups[active&mask]+=multiplicity
            counts['pattern_intersections']+=len(leaf_patterns[axis])
            counts['groups']+=len(groups)
            costs=sorted(((value(following,child),child,multiplicity*A[axis]) for child,multiplicity in groups.items()),reverse=True)
            unfilled=U[axis]
            answer=0
            for child_value,child,capacity in costs:
                mass=min(unfilled,capacity)
                answer+=mass*child_value
                unfilled-=mass
                counts['greedy_groups']+=1
                if not unfilled:
                    break
            require(unfilled==0 and 0<=answer<=denominators[remaining],'full exact feasible row filled')
            counts['coordinate_actions']+=1
            if remaining==127 and active==(1<<154)-1:
                root_actions[str(P[axis])]=str(F(answer,denominators[remaining]))
            if answer>best:
                best,choice=answer,axis
            if best==denominators[remaining]:
                counts['perfect_survival_shortcuts']+=1
                break
        require(best>=0 and choice is not None,'at least one remaining original coordinate')
        if remaining==127 and active==(1<<154)-1:
            root_choice=P[choice]
        return best

    numerator=value(127,(1<<154)-1)
    survival=F(numerator,denominators[127])
    epsilon=1-survival
    require(survival>=F(fixed['survival_exact']),'adaptive class contains previously attained fixed numerical order')
    records=[]
    old_epsilon=F(fixed['epsilon_exact'])
    for source in allowance['records']:
        B=source['B']
        best=source['best']
        old_baseline=F(best['baseline_score_upper'])
        old_d7=F(best['D7_score_upper'])
        base=old_baseline-old_epsilon+epsilon
        d7=old_d7-old_epsilon+epsilon
        records.append({'B':B,'t':best['t'],'tau':best['tau'],'baseline_score_upper':str(base),
                        'D7_score_upper':str(d7),'baseline_decimal':float(base),'D7_decimal':float(d7),
                        'baseline_margin_lower':str(1-base),'D7_margin_lower':str(1-d7)})
    result={'schema':'independent-adaptive-core7-survival-dp-v1','status':'complete',
            'scope':'Exact maximum attainable survival over arbitrary full-history adaptive orders among the seven core primes, then all thirteen terminal primes, with unchanged actual labels and flat balanced caps. No full20 interleaving or arbitrary-phase conclusion.',
            'survival_exact':str(survival),'epsilon_exact':str(epsilon),'epsilon_decimal':float(epsilon),
            'raw_numerator':numerator,'raw_denominator':denominators[127],'root_choice':root_choice,
            'root_action_survival':root_actions,'counts':counts,'cache_size':nonconstant.cache_info().currsize,
            'depth_cap_checks':depth_checks,'actual_leaf_pattern_counts':list(map(len,leaf_patterns)),
            'retained_square_threshold_allowances':records}
    require(result['status']=='complete','complete independent exact root')
    return ctx.finish(result)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
