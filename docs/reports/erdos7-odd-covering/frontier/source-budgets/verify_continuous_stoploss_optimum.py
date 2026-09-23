"""Independent derivative-numerator formulas and exact continuous optimum signs."""
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

CERTIFICATE='certificates/source_norms/source-budgets/continuous_stoploss_optimum_verification.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/64-adaptive-core-policy-and-continuous-stoploss-optima.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md', 'problem-details/62-expanded-stopping-cutoffs-for-the-seven-phase-head.md', 'problem-details/63-squared-load-stoploss-continuation.md', 'certificates/source_norms/source-budgets/expanded_stop_budget_verification.json', 'frontier/source-budgets/verify_expanded_stop_budget.py', 'certificates/source_norms/source-budgets/square_stoploss_curve_verification.json', 'frontier/source-budgets/verify_square_stoploss_curve.py', 'certificates/source_norms/source-budgets/expanded_stop_budget.json', 'frontier/source-budgets/expanded_stop_budget.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    tail=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_budget_verification.json','frontier/source-budgets/verify_expanded_stop_budget.py')
    square=ctx.fresh('certificates/source_norms/source-budgets/square_stoploss_curve_verification.json','frontier/source-budgets/verify_square_stoploss_curve.py')
    budget=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_budget.json','frontier/source-budgets/expanded_stop_budget.py')
    Q=tail['scale']
    require(Q==square['scale']==10**18,'same directed integer-mass grid')
    snapshots={r['B']:r for r in tail['snapshots']}
    records=[]
    for chosen in square['records']:
        B=chosen['B']
        snapshot=snapshots[B]
        weights=budget['low_product_tables'][str(B)]
        require(len(weights)==tail['retained_states']+1 and weights[0]==0 and all(type(w) is int and w>=0 for w in weights),'complete nonnegative retained mass table')
        require(sha256(json.dumps(weights,separators=(',',':')).encode()).hexdigest()==snapshot['final_low_state_digest'],'entire table previously independently verified')
        T,J=F(snapshot['T_lower']),F(snapshot['J_upper'])
        t,tau=chosen['best']['t'],chosen['best']['tau']
        require(tau==t*t and 0<tau<T,'existing interior square threshold')
        n=isqrt(T.numerator//T.denominator)
        require(n<len(weights) and n*n<=T<(n+1)**2,'all terms at and below T retained')
        # Each expression is summed independently, with no running prefix state.
        K=J-tau+sum((F((tau-d*d)*weights[d],Q) for d in range(1,t+1)),F(0))
        g_left=J-T+sum(((T-d*d)*F(weights[d],Q) for d in range(1,t)),F(0))
        g_right=J-T+sum(((T-d*d)*F(weights[d],Q) for d in range(1,t+1)),F(0))
        slope_left=-1+sum((F(weights[d],Q) for d in range(1,t)),F(0))
        slope_right=-1+sum((F(weights[d],Q) for d in range(1,t+1)),F(0))
        require(g_left==K+(T-tau)*slope_left and g_right==K+(T-tau)*slope_right,'both one-sided derivative numerators by an independent formula')
        jump=(T-tau)*F(weights[t],Q)
        require(g_right-g_left==jump and jump>0,'exact positive selected-breakpoint jump')
        K_at_T=J-T+sum(((T-d*d)*F(weights[d],Q) for d in range(1,n+1)),F(0))
        require(K==F(chosen['best']['K_upper']),'same previously independently certified envelope value')
        require(g_left<0<g_right,'strict derivative signs at existing threshold')
        require(K_at_T>0,'positive finite envelope limit numerator at T')
        records.append({'B':B,'t':t,'tau':tau,'T_lower':str(T),'J_upper':str(J),
                        'K_upper_at_tau':str(K),'g_left':str(g_left),'g_right':str(g_right),
                        'g_left_decimal':float(g_left),'g_right_decimal':float(g_right),
                        'slope_left':str(slope_left),'slope_right':str(slope_right),
                        'derivative_numerator_jump':str(jump),'K_at_T':str(K_at_T),'K_at_T_decimal':float(K_at_T),
                        'maximum_queried_state':n,'continuous_minimum':'unique at selected tau for this fixed upper envelope'})
    require([r['t'] for r in records]==[48,96,128],'complete existing selected-threshold inventory')
    result={'schema':'independent-fixed-envelope-continuous-threshold-v1','status':'PASS','scope':'Unique minimum over all real0<=tau<T of each identical fixed directed upper envelope. No optimality of an actual load law, head law, profile, cutoff or competing method.','tail_recomputations':0,'candidate_continuous_results_read':False,'records':records}
    return ctx.finish(result)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
