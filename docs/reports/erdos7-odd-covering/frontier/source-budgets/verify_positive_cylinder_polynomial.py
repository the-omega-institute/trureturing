"""Independent actual-leaf expansion of every fixed-cover coefficient."""
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import gcd,prod
from pathlib import Path
import importlib.util
import sys
sys.dont_write_bytecode=True

_spec=importlib.util.spec_from_file_location('positive_cylinder_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require,load_module=_io.require,_io.load_module

CERTIFICATE='certificates/source_norms/source-budgets/positive_cylinder_polynomial_verification.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/60-positive-cylinder-covers-across-head-profiles.md', 'problem-details/59-terminal-phase-elimination-and-uniform-balanced-profile-obstruction.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'frontier/source-budgets/positive_cylinder_polynomial.py', 'frontier/source-budgets/verify_uniform_phase_capacity.py', 'certificates/source_norms/source-budgets/positive_cylinder_polynomial.json', 'certificates/source_norms/source-budgets/uniform_phase_capacity_verification.json')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    data=ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json')
    require(sha256(ctx.raw('frontier/source-budgets/uniform_phase_capacity_input.json')).hexdigest()=='ea227d216660f496ecb3a2c89dbc145605f0ad83c94e5996a7ee76d746ea712b','same locked actual seven-phase geometry')
    given=ctx.fresh('certificates/source_norms/source-budgets/positive_cylinder_polynomial.json','frontier/source-budgets/positive_cylinder_polynomial.py')
    bound=ctx.fresh('certificates/source_norms/source-budgets/uniform_phase_capacity_verification.json','frontier/source-budgets/verify_uniform_phase_capacity.py')
    primes, heights, labels = data['prime_order'], data['heights'], data['labels']
    caps = [F(row[-1]) for row in data['profiles']]
    require(len(labels) == 154 and len(caps) == 20 and all(x > 0 for x in caps),
            'all actual terminal capacities are strictly positive')
    units = [x.denominator for x in caps]
    capnums = [x.numerator for x in caps]
    scale = [prod(units[i:]) for i in range(21)]
    last = [max(i for i, p in enumerate(primes) if m % p == 0) for m, a in labels]
    completed = [sum(1 << j for j, axis in enumerate(last) if axis < i) for i in range(21)]
    leaves = []
    for p, h in zip(primes, heights):
        size = p**h
        factors = [gcd(m, size) for m, a in labels]
        leaves.append(tuple(sum(1 << j for j, ((m, a), factor) in
                                enumerate(zip(labels, factors)) if x % factor == a % factor)
                            for x in range(size)))
    buckets = [tuple(j for j, (m, a) in enumerate(labels) if m % primes[i] == 0)
               for i in range(7, 20)]
    require(all(heights[i] == 1 for i in range(7, 20)) and
            all(sum(m % p == 0 for p in primes[7:]) <= 1 for m, a in labels),
            'literal product terminal geometry')
    statistics = {'cost_actual_leaf_evaluations': 0, 'coefficient_actual_leaf_evaluations': 0,
                  'coefficient_additions': 0}


    def allowed_counts(active):
        return [primes[i] - len({labels[j][1] % primes[i] for j in ids if active >> j & 1})
                for i, ids in enumerate(buckets, 7)]


    @lru_cache(None)
    def cost(axis, active):
        if not active:
            return scale[axis]
        if active & completed[axis]:
            return 0
        if axis == 7:
            return prod(min(units[i], capnums[i] * allowed)
                        for i, allowed in enumerate(allowed_counts(active), 7))
        statistics['cost_actual_leaf_evaluations'] += len(leaves[axis])
        total = capnums[axis] * sum(cost(axis + 1, active & mask) for mask in leaves[axis])
        return min(scale[axis], total)


    @lru_cache(None)
    def coefficients(axis, active):
        if active & completed[axis]:
            return ()
        if not active:
            return ((0, 1),)
        if axis == 7:
            mask, count = 0, 1
            for i, allowed in enumerate(allowed_counts(active), 7):
                if capnums[i] * allowed < units[i]:
                    mask |= 1 << i
                    count *= allowed
            return ((mask, count),) if count else ()
        if cost(axis, active) == scale[axis]:
            return ((0, 1),)
        result = {}
        statistics['coefficient_actual_leaf_evaluations'] += len(leaves[axis])
        for leafmask in leaves[axis]:
            for mask, count in coefficients(axis + 1, active & leafmask):
                require(not (mask & ((1 << (axis + 1)) - 1)),
                        'every selected coordinate occurs at most once')
                key = mask | (1 << axis)
                result[key] = result.get(key, 0) + count
                statistics['coefficient_additions'] += 1
        return tuple(sorted(result.items()))


    active = (1 << 154) - 1
    terms = [{'coordinate_mask': mask,
              'primes': [p for i, p in enumerate(primes) if mask >> i & 1],
              'coefficient': str(count)} for mask, count in coefficients(0, active)]
    require(terms == given['terms'], 'every exact nonnegative polynomial coefficient')
    require(all(int(term['coefficient']) > 0 and 0 <= term['coordinate_mask'] < 1 << 20
                for term in terms), 'positive integer coefficients and valid coordinate subsets')
    value = sum((int(term['coefficient']) * prod(caps[i] for i in range(20)
                                               if term['coordinate_mask'] >> i & 1)
                 for term in terms), F(0))
    require(value == F(cost(0, active), scale[0]) == F(given['balanced_value']) ==
            F(bound['records'][1]['survival_upper']), 'exact original balanced-price evaluation')
    expanded = sum(int(term['coefficient']) for term in terms)
    require(len(terms) == given['term_count'] == 38 and str(expanded) ==
            given['expanded_cylinders'] == '12533129880604949291',
            'complete term and expanded-cylinder inventories')
    result = dict(schema='independent-frozen-cylinder-polynomial-v1',
                  scope='The same fixed survivor set has a fixed positive cylinder cover on all20 named full-height coordinates. Its polynomial bounds survivor mass for new admissible deterministic full-history atom caps and all adaptive sampling orders. It can exceed one and does not exclude all profiles or automatically transport continuation budgets.',
                  terms=terms, term_count=len(terms), expanded_cylinders=str(expanded),
                  balanced_value=str(value), cost_states=cost.cache_info().currsize,
                  coefficient_states=coefficients.cache_info().currsize, statistics=statistics)
    return ctx.finish(result)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
