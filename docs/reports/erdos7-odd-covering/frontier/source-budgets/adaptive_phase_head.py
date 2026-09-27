"""Exact adaptive ordering in the first five coordinates of a fixed 154-class head."""
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

CERTIFICATE = 'certificates/source_norms/source-budgets/adaptive_phase_head.json'
SOURCES = ('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/58-adaptive-initial-block-recovery-and-all-schedule-budget-obstruction.md', 'problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md', 'problem-details/56-exponent-frontiers-and-cylinder-cover-certificates.md', 'problem-details/57-balanced-depth-profile-and-degree-seven-frontier.md', 'frontier/source-budgets/adaptive_phase_head_input.json', 'frontier/source-budgets/balanced_profile_head_input.json', 'frontier/source-budgets/depth_cap_bellman.py', 'certificates/source_norms/source-budgets/balanced_profile_tail_budget.json', 'certificates/source_norms/source-budgets/balanced_profile_exponent_frontier.json')

INPUT = 'frontier/source-budgets/adaptive_phase_head_input.json'
TAIL = 'certificates/source_norms/source-budgets/balanced_profile_tail_budget.json'
FRONTIER = 'certificates/source_norms/source-budgets/balanced_profile_exponent_frontier.json'

def block_minimum(s,problem,block_size):
    axes=tuple(range(len(problem.primes)))
    choices={}

    @lru_cache(None)
    def value(remaining,active):
        if not active:return F(0)
        if any(all(problem.rows[j][i][0]==0 for i in remaining) for j in active):return F(1)
        permitted=tuple(i for i in remaining if i<block_size) or remaining[:1]
        best=None;selected=None
        for axis in permitted:
            rest=tuple(i for i in remaining if i!=axis)
            cost,_=s.compressed_row(problem.primes[axis],problem.heights[axis],problem.profiles[axis],
                                     problem.by_axis[axis],active,lambda hits:value(rest,hits))
            if best is None or cost<best:best=cost;selected=axis
            if best==0:break
        choices[(remaining,active)]=selected
        return best

    result=value(axes,tuple(range(len(problem.labels))))
    return result,len(choices),value.cache_info().currsize


def calculate(base):
    ctx = _io.Context(base, SOURCES, __file__)
    data = ctx.read(INPUT)
    profile = ctx.read('frontier/source-budgets/balanced_profile_head_input.json')['profiles']
    tail = ctx.fresh(TAIL, 'frontier/source-budgets/balanced_profile_tail_budget.py')
    frontier = ctx.fresh(FRONTIER, 'frontier/source-budgets/balanced_profile_exponent_frontier.py')
    require(profile == data['profiles'] == tail['profiles'] == frontier['profiles'], 'same balanced profile')
    C,J,T = F(tail['C_upper']),F(tail['J_upper']),F(tail['T_lower'])
    require(T == F(326059,4), 'existing continuation threshold')
    E = F(next(row for row in frontier['records'] if row['total_degree_max']==7)['outside_weight'])
    eta = 1-C-(J-1)/(T-1)
    s = load_module('adaptive_phase_existing_solver', base/'frontier/source-budgets/depth_cap_bellman.py')
    problem = s.HeadProblem(data['prime_order'],data['heights'],data['labels'],profile)
    epsilon,decisions,states = block_minimum(s,problem,5)
    base_score = epsilon+C+(J-1)/(T-1)
    d7 = base_score+E
    require(base_score < 1, 'adaptive first-five policy passes the fixed baseline budget')
    record = dict(block_size=5,block_primes=data['prime_order'][:5],epsilon_exact=str(epsilon),epsilon_decimal=float(epsilon),decision_states=decisions,states=states,baseline_score_exact=str(base_score),baseline_score_decimal=float(base_score),D7_score_exact=str(d7),D7_score_decimal=float(d7),baseline_threshold_gap=str(eta-epsilon),D7_threshold_gap=str(eta-E-epsilon))
    result = dict(schema='balanced-four-phase-initial-block-v1',scope='Globally fixed four-phase154 input and balanced caps. Exact optimum within the first five named coordinates with numerical suffix; an attained upper bound for the full adaptive optimum, not a full twenty-coordinate optimum.',prime_order=data['prime_order'],heights=data['heights'],profiles=profile,labels=data['labels'],C_upper=str(C),J_upper=str(J),T_lower=str(T),D7_outside_upper=str(E),records=[record])
    return ctx.finish(result)


if __name__ == "__main__":
    _io.run(CERTIFICATE, calculate, __file__)
