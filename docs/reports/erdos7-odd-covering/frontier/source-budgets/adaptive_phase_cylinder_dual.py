"""Mixed-cylinder survivor upper bound valid for every legal sampling schedule."""
from collections import defaultdict
from hashlib import sha256
from math import prod, isqrt
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

CERTIFICATE = 'certificates/source_norms/source-budgets/adaptive_phase_cylinder_dual.json'
SOURCES = ('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/58-adaptive-initial-block-recovery-and-all-schedule-budget-obstruction.md', 'problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md', 'problem-details/56-exponent-frontiers-and-cylinder-cover-certificates.md', 'problem-details/57-balanced-depth-profile-and-degree-seven-frontier.md', 'frontier/source-budgets/adaptive_phase_head_input.json', 'certificates/source_norms/source-budgets/balanced_profile_tail_budget.json', 'certificates/source_norms/source-budgets/balanced_profile_exponent_frontier.json')

INPUT = 'frontier/source-budgets/adaptive_phase_head_input.json'
TAIL = 'certificates/source_norms/source-budgets/balanced_profile_tail_budget.json'
FRONTIER = 'certificates/source_norms/source-budgets/balanced_profile_exponent_frontier.json'

def solve(raw):
    data = json.loads(raw)
    primes = tuple(data['prime_order'])
    heights = tuple(data['heights'])
    labels = tuple(tuple(x) for x in data['labels'])
    profiles = tuple(tuple(F(x) for x in r) for r in data['profiles'])
    require(len(primes) == len(heights) == len(profiles), 'coordinate shapes')
    require(tuple(sorted(set(primes))) == primes, 'numerical distinct order')
    require(all(p >= 3 and p % 2 and all(p % d for d in range(2, isqrt(p)+1))
                for p in primes), 'odd primes')
    require(all(h >= 1 for h in heights), 'positive heights')
    for p, h, r in zip(primes, heights, profiles):
        require(len(r) == h+1 and r[0] == 1, 'profile shape')
        require(all(F(1,p**e) <= r[e] <= r[e-1] for e in range(1,h+1)),
                'monotone feasible full-history cylinder caps')
    period = prod(p**h for p,h in zip(primes,heights))
    require(len({m for m,a in labels}) == len(labels), 'original distinctness')
    require(all(m > 1 and m % 2 and period % m == 0 and 0 <= a < m
                for m,a in labels), 'literal odd labels')
    requirements = []
    for m,a in labels:
        rest=m
        row=[]
        for p in primes:
            e=0
            while rest % p == 0:
                rest //= p
                e += 1
            row.append((e,a % p**e))
        require(rest == 1, 'full factorization')
        requirements.append(tuple(row))
    last = tuple(max(k for k,(e,a) in enumerate(row) if e)
                 for row in requirements)
    terminal_caps = tuple(r[-1] for r in profiles)
    decisions = {'whole_prefix':0,'children':0,'already_covered':0,'no_live_labels':0}

    def groups(axis, active):
        p,h=primes[axis],heights[axis]
        result=defaultdict(int)

        def descend(depth,inherited,pending):
            hits=inherited+tuple(j for j in pending
                                 if requirements[j][axis][0] == depth)
            deeper=tuple(j for j in pending if requirements[j][axis][0] > depth)
            if not deeper:
                result[tuple(sorted(hits))] += p**(h-depth)
                return
            children=defaultdict(list)
            for j in deeper:
                digit=(requirements[j][axis][1]//p**depth)%p
                children[digit].append(j)
            missing=p-len(children)
            result[tuple(sorted(hits))] += missing*p**(h-depth-1)
            for child in children.values():
                descend(depth+1,hits,tuple(child))

        descend(0,(),active)
        require(sum(result.values()) == p**h, 'exact full-coordinate count')
        return tuple((ids,multiplicity) for ids,multiplicity in result.items()
                     if multiplicity)

    @lru_cache(None)
    def capacity(axis,active):
        if not active:
            decisions['no_live_labels'] += 1
            return F(1)
        if any(last[j] < axis for j in active):
            decisions['already_covered'] += 1
            return F(0)
        require(axis < len(primes), 'terminal status resolved')
        children=terminal_caps[axis]*sum(
            (multiplicity*capacity(axis+1,ids)
             for ids,multiplicity in groups(axis,active)), F(0))
        if children < 1:
            decisions['children'] += 1
            return children
        decisions['whole_prefix'] += 1
        return F(1)

    bound=capacity(0,tuple(range(len(labels))))
    require(0 <= bound <= 1, 'survival upper range')
    return {
        'schema':'global-cylinder-prefix-dual-v1',
        'input_sha256':sha256(raw).hexdigest(),
        'scope':'Global product cylinder-cap weak dual; valid for every admissible adaptive read-once law. The numerical order selects the certificate tree only.',
        'prime_order':list(primes),'heights':list(heights),
        'original_labels':[list(x) for x in labels],
        'profiles':[[str(x) for x in r] for r in profiles],
        'period':period,'survival_upper':str(bound),'bad_lower':str(1-bound),
        'states':capacity.cache_info().currsize,'decisions':decisions,
    }


def calculate(base):
    ctx = _io.Context(base, SOURCES, __file__)
    result = solve(ctx.raw(INPUT))
    tail = ctx.fresh(TAIL,'frontier/source-budgets/balanced_profile_tail_budget.py')
    frontier = ctx.fresh(FRONTIER,'frontier/source-budgets/balanced_profile_exponent_frontier.py')
    require(result['profiles'] == tail['profiles'] == frontier['profiles'], 'same fixed balanced profile')
    C,J,T = F(tail['C_upper']),F(tail['J_upper']),F(tail['T_lower'])
    E = F(next(row for row in frontier['records'] if row['total_degree_max']==7)['outside_weight'])
    score = F(result['bad_lower'])+E+C+(J-1)/(T-1)
    require(score>1,'all-schedule obstruction for the fixed D7 upper-allowance score')
    result['budget_obstruction']=dict(head_bad_lower=result['bad_lower'],D7_fixed_score_lower=str(score),D7_fixed_score_lower_float=float(score),excess=str(score-1),excess_float=float(score-1),scope='Every legal adaptive read-once schedule with these fixed labels and full-history profile caps fails the stated D7 sufficient score. E7, C and J remain upper allowances; this does not imply coverage or exclude sharper joint allowances.')
    return ctx.finish(result)


if __name__ == "__main__":
    _io.run(CERTIFICATE, calculate, __file__)
