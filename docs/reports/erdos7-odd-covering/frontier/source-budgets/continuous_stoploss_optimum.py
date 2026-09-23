"""Exact one-sided signs and unique real-threshold minima of fixed upper envelopes."""
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

CERTIFICATE='certificates/source_norms/source-budgets/continuous_stoploss_optimum.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/64-adaptive-core-policy-and-continuous-stoploss-optima.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md', 'problem-details/62-expanded-stopping-cutoffs-for-the-seven-phase-head.md', 'problem-details/63-squared-load-stoploss-continuation.md', 'certificates/source_norms/source-budgets/square_stoploss_curve.json', 'frontier/source-budgets/square_stoploss_curve.py', 'certificates/source_norms/source-budgets/expanded_stop_budget.json', 'frontier/source-budgets/expanded_stop_budget.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    curve=ctx.fresh('certificates/source_norms/source-budgets/square_stoploss_curve.json','frontier/source-budgets/square_stoploss_curve.py')
    budget=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_budget.json','frontier/source-budgets/expanded_stop_budget.py')
    results = []
    Q = curve['scale']
    for row in curve['records']:
        weights=budget['low_product_tables'][str(row['B'])]
        snapshot=next(r for r in budget['snapshots'] if r['B']==row['B'])
        require(sha256(json.dumps(weights,separators=(',',':')).encode()).hexdigest()==snapshot['final_low_state_digest'],'complete independently bound mass table')
        require(all(isinstance(w, int) and w >= 0 for w in weights), 'nonnegative upper masses')
        T, J = F(row['T_lower']), F(row['J_upper'])
        t, tau = row['best']['t'], F(row['best']['tau'])
        require(t*t == tau and 0 < tau < T, 'interior square threshold')
        last = isqrt(T.numerator // T.denominator)
        require(last < len(weights), 'all breakpoints before T are retained')
        K = J - tau + sum((tau-d*d)*F(weights[d], Q) for d in range(1,t+1))
        require(K == F(row['best']['K_upper']), 'same directed envelope at chosen threshold')
        slope_left = -1 + sum(F(weights[d], Q) for d in range(1,t))
        slope_right = slope_left + F(weights[t], Q)
        g_left = K + (T-tau)*slope_left
        g_right = K + (T-tau)*slope_right
        K_T = J - T + sum((T-d*d)*F(weights[d], Q) for d in range(1,last+1))
        require(g_left < 0 < g_right and K_T > 0, 'strict unique continuous minimum')
        results.append(dict(B=row['B'], T_exact=str(T), tau=int(tau),
                            K_exact=str(K), slope_left_exact=str(slope_left),
                            slope_right_exact=str(slope_right),
                            derivative_numerator_left=str(g_left),
                            derivative_numerator_right=str(g_right),
                            derivative_numerator_left_decimal=float(g_left),
                            derivative_numerator_right_decimal=float(g_right),
                            K_at_T_exact=str(K_T), K_at_T_decimal=float(K_T),
                            unique_global_minimum=True))
    out=dict(schema='continuous-stoploss-ratio-minimum-v1',scope='Unique minima over every real0<=tau<T of the unchanged directed piecewise-affine upper envelopes. No optimality over actual laws, layouts, profiles or other comparisons.',records=results)
    return ctx.finish(out)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
