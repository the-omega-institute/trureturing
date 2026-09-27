"""All 120 fixed initial-five orders using the existing exact laminar solver."""
from itertools import permutations
from fractions import Fraction as F
from functools import lru_cache
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True

_spec = importlib.util.spec_from_file_location('adaptive_phase_io', Path(__file__).with_name('adaptive_phase_io.py'))
_io = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require, load_module = _io.require, _io.load_module

CERTIFICATE = 'certificates/source_norms/source-budgets/adaptive_phase_fixed_orders.json'
SOURCES = ('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/58-adaptive-initial-block-recovery-and-all-schedule-budget-obstruction.md', 'problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md', 'problem-details/56-exponent-frontiers-and-cylinder-cover-certificates.md', 'problem-details/57-balanced-depth-profile-and-degree-seven-frontier.md', 'frontier/source-budgets/adaptive_phase_head_input.json', 'frontier/source-budgets/depth_cap_bellman.py', 'certificates/source_norms/source-budgets/balanced_profile_tail_budget.json')

INPUT = 'frontier/source-budgets/adaptive_phase_head_input.json'
TAIL = 'certificates/source_norms/source-budgets/balanced_profile_tail_budget.json'

def calculate(base):
    ctx = _io.Context(base, SOURCES, __file__)
    data = ctx.read(INPUT)
    tail = ctx.fresh(TAIL, 'frontier/source-budgets/balanced_profile_tail_budget.py')
    require(data['profiles'] == tail['profiles'], 'same fixed balanced profile')
    s = load_module('adaptive_phase_fixed_solver', base/'frontier/source-budgets/depth_cap_bellman.py')
    C,J,T = F(tail['C_upper']),F(tail['J_upper']),F(tail['T_lower'])
    require(T == F(326059,4), 'existing continuation threshold')
    P,H,R = data['prime_order'],data['heights'],data['profiles']
    records=[]
    for prefix in permutations(range(5)):
        order=prefix+tuple(range(5,len(P)))
        named=[P[i] for i in order]
        problem=s.HeadProblem(named,[H[i] for i in order],data['labels'],[R[i] for i in order])
        epsilon=problem.optimum()
        score=epsilon+C+(J-1)/(T-1)
        require(score>1,'every fixed permutation of this block fails the stated sufficient budget')
        records.append(dict(prime_order=named,epsilon=str(epsilon),epsilon_float=float(epsilon),score=str(score),score_float=float(score),states=problem.value.cache_info().currsize))
        problem.value.cache_clear()
    require(len(records)==120,'all permutations of five named coordinates')
    result=dict(schema='balanced-four-phase-fixed-first-five-v1',scope='Exact fixed-order head optima for all120 permutations of the first5 primes, remaining coordinates numerical; same globally fixed four-modified154 original labels and named profiles. Every value is reproducible and separately checked by the actual-leaf integer-cap verifier. No claim about all20! fixed orders.',input=INPUT,records=records)
    return ctx.finish(result)


if __name__ == "__main__":
    _io.run(CERTIFICATE, calculate, __file__)
