"""Exact actual-leaf numerical-order head law for the clean seven-phase input."""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import gcd,isqrt,lcm,prod
from pathlib import Path
import importlib.util
import json
import sys
sys.dont_write_bytecode=True
_spec=importlib.util.spec_from_file_location('expanded_stop_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require,load_module=_io.require,_io.load_module

CERTIFICATE='certificates/source_norms/source-budgets/expanded_stop_head.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/62-expanded-stopping-cutoffs-for-the-seven-phase-head.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'problem-details/59-terminal-phase-elimination-and-uniform-balanced-profile-obstruction.md', 'problem-details/57-balanced-depth-profile-and-degree-seven-frontier.md', 'problem-details/04b-arbitrary-star-head-residues-with-unrestricted-tails.md', 'problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md', 'frontier/source-budgets/balanced_profile_head_input.json', 'frontier/source-budgets/capped_head_bellman.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    data=ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json')
    require(sha256(ctx.raw('frontier/source-budgets/uniform_phase_capacity_input.json')).hexdigest()=='ea227d216660f496ecb3a2c89dbc145605f0ad83c94e5996a7ee76d746ea712b','exact clean seven-phase input')
    profile=ctx.read('frontier/source-budgets/balanced_profile_head_input.json')
    balanced={'records':[{'profiles':profile['profiles']}]}
    literal=load_module('expanded_original_congruences',Path(base)/'frontier/source-budgets/capped_head_bellman.py')
    original={'prime_order':profile['prime_order'],'heights':profile['heights'],'labels':[list(pair) for pair in literal.counterexample_154_labels()]}
    primes, heights, labels = data['prime_order'], data['heights'], data['labels']
    require(primes == original['prime_order'] and heights == original['heights'] and
            data['profiles'] == balanced['records'][0]['profiles'], 'same balanced profile and complete coordinates')
    require(len(labels) == len({m for m, a in labels}) == 154 and
            [m for m, a in labels] == [m for m, a in original['labels']], 'all original numerical moduli')
    changes = [{'modulus': m, 'original': a, 'new': b}
               for (m, a), (n, b) in zip(original['labels'], labels) if a != b]
    require([[r['modulus'], r['new']] for r in changes] == data['changes'] and
            [(r['modulus'], r['new']) for r in changes] ==
            [(25, 13), (39, 14), (45, 26), (55, 28), (63, 32), (189, 29), (225, 11)],
            'exact seven global phase changes')
    require(all(m > 1 and m % 2 and 0 <= a < m for m, a in labels), 'literal odd congruences')
    rows = [[F(x) for x in row] for row in data['profiles']]
    require(len(primes) == len(heights) == len(rows) == 20 and primes == sorted(primes),
            'all twenty coordinates in numerical order')
    sizes = [p**h for p, h in zip(primes, heights)]
    require(prod(sizes) == lcm(*(m for m, a in labels)), 'complete CRT period')
    units, capnums, ancestor_checks = [], [], 0
    for p, height, row in zip(primes, heights, rows):
        require(len(row) == height + 1 and row[0] == 1 and
                all(F(1, p**e) <= row[e] <= row[e - 1] for e in range(1, height + 1)),
                'uniform-feasible complete deterministic depth profile')
        for e in range(1, height + 1):
            require(row[e] == p**(height - e) * row[height],
                    'leaf caps imply each proper ancestor cap exactly')
            ancestor_checks += 1
        units.append(row[-1].denominator)
        capnums.append(row[-1].numerator)
    scale = [prod(units[i:]) for i in range(21)]
    scopes = [tuple(i for i, p in enumerate(primes) if m % p == 0) for m, a in labels]
    last = [max(s) for s in scopes]
    complete = [sum(1 << j for j, i in enumerate(last) if i < axis) for axis in range(21)]
    actual_leaves = []
    for size in sizes:
        factors = [gcd(m, size) for m, a in labels]
        actual_leaves.append(tuple(sum(1 << j for j, ((m, a), factor) in
                                       enumerate(zip(labels, factors)) if x % factor == a % factor)
                                   for x in range(size)))
    buckets = [tuple(j for j, s in enumerate(scopes) if i in s) for i in range(7, 20)]
    require(primes[:7] == [3, 5, 7, 11, 13, 17, 19] and all(h == 1 for h in heights[7:]),
            'exact core7 and terminal13 geometry')
    require(sum(map(len, buckets)) == 76 and
            sum(not any(i >= 7 for i in s) for s in scopes) == 78 and
            all(sum(i >= 7 for i in s) <= 1 for s in scopes), 'complete one-leaf label geometry')
    require(all(34 % m != a for m, a in labels), 'actual uncovered integer 34')
    records = []
    for collapsed in [False, True]:
        counts = {'actual_leaf_evaluations': 0, 'multiplicity_groups': 0,
                  'feasible_row_checks': 0, 'terminal_core_states': 0,
                  'terminal_incidence_checks': 0}

        @lru_cache(None)
        def value(axis, active):
            if not active:
                return 0
            if active & complete[axis]:
                return scale[axis]
            if collapsed and axis == 7:
                survival = 1
                for i, ids in enumerate(buckets, 7):
                    forbidden = {labels[j][1] % primes[i] for j in ids if active >> j & 1}
                    survival *= min(units[i], capnums[i] * (primes[i] - len(forbidden)))
                    counts['terminal_incidence_checks'] += len(ids)
                counts['terminal_core_states'] += 1
                require(0 <= survival <= scale[axis], 'attainable terminal product survival')
                return scale[axis] - survival
            require(axis < 20, 'literal event fully resolved')
            groups = Counter(active & mask for mask in actual_leaves[axis])
            counts['actual_leaf_evaluations'] += len(actual_leaves[axis])
            counts['multiplicity_groups'] += len(groups)
            costs = sorted((value(axis + 1, child), multiplicity * capnums[axis])
                           for child, multiplicity in groups.items())
            remaining, answer = units[axis], 0
            for cost, available in costs:
                mass = min(remaining, available)
                answer += mass * cost
                remaining -= mass
                if not remaining:
                    break
            require(remaining == 0 and 0 <= answer <= scale[axis],
                    'normalized exact greedy row has enough actual leaf capacity')
            counts['feasible_row_checks'] += 1
            return answer

        epsilon = F(value(0, (1 << 154) - 1), scale[0])
        records.append(dict(terminal_product=collapsed, epsilon_exact=str(epsilon),
                            survival_exact=str(1 - epsilon), epsilon_decimal=float(epsilon),
                            states=value.cache_info().currsize, counts=counts))
        value.cache_clear()
    require(records[0]['epsilon_exact'] == records[1]['epsilon_exact'],
            'independent full20 and terminal-collapsed7 recurrence agreement')
    result = dict(schema='independent-seven-phase-fixed-numerical-order-head-v1',
                  scope='Exact attainable minimum bad mass among full-history laws in the fixed numerical order 3 through 73 with unchanged balanced depth caps and the actual seven-phase input. No optimum over other orders or adaptive coordinate selections is claimed.',
                  prime_order=primes, heights=heights, profiles=data['profiles'], labels=labels,
                  changes=changes, uncovered_integer=34, ancestor_cap_checks=ancestor_checks,
                  records=records, epsilon_exact=records[0]['epsilon_exact'],
                  survival_exact=records[0]['survival_exact'])
    return ctx.finish(result)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
