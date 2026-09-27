"""Independent actual-leaf audit of the two numerical-order phase reductions."""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
import importlib.util
from math import gcd, lcm, prod
from pathlib import Path
import sys
sys.dont_write_bytecode = True

_spec = importlib.util.spec_from_file_location(
    'terminal_phase_verification_io', Path(__file__).with_name('adaptive_phase_io.py'))
_io = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require, load_module = _io.require, _io.load_module

CERTIFICATE = 'certificates/source_norms/source-budgets/terminal_phase_reduction_verification.json'
CANDIDATE = 'certificates/source_norms/source-budgets/terminal_phase_reduction.json'
PRODUCER = 'frontier/source-budgets/terminal_phase_reduction.py'
SOURCES = (
    'certificate_io.py',
    'frontier/source-budgets/adaptive_phase_io.py',
    'problem-details/59-terminal-phase-elimination-and-uniform-balanced-profile-obstruction.md',
    'frontier/source-budgets/capped_head_bellman.py',
    'frontier/source-budgets/balanced_profile_head_input.json',
    'frontier/source-budgets/adaptive_phase_head_input.json',
)


def literal_inventory(primes, heights, labels):
    """Evaluate original congruences at every actual local coordinate value."""
    sizes = [p**h for p, h in zip(primes, heights)]
    require(prod(sizes) == lcm(*(m for m, a in labels)), 'complete original CRT period')
    scopes = [tuple(i for i, p in enumerate(primes) if m % p == 0) for m, a in labels]
    require(all(scopes), 'every original modulus has a coordinate')
    last = [max(scope) for scope in scopes]
    completed = [sum(1 << j for j, axis in enumerate(last) if axis < i)
                 for i in range(len(primes) + 1)]
    matches = []
    for size in sizes:
        factors = [gcd(m, size) for m, a in labels]
        matches.append(tuple(sum(1 << j for j, ((m, a), q) in
                                 enumerate(zip(labels, factors)) if x % q == a % q)
                             for x in range(size)))
    buckets = [tuple(j for j, scope in enumerate(scopes) if i in scope)
               for i in range(7, len(primes))]
    require(sum(not any(i >= 7 for i in scope) for scope in scopes) == 78,
            'all 78 core-only original labels')
    require(sum(map(len, buckets)) == 76 and
            all(sum(i >= 7 for i in scope) <= 1 for scope in scopes),
            'all 76 labels have exactly one terminal coordinate')
    require(all(len(ids) <= primes[i] and all(labels[j][0] % (primes[i]**2) != 0
                                            for j in ids)
                for i, ids in enumerate(buckets, 7)), 'injective height-one leaf buckets')
    return completed, matches, buckets


def exact_value(primes, labels, units, capnums, inventory, collapsed):
    """Minimize literal bad mass using only actual leaves and exact integer masses."""
    completed, matches, buckets = inventory
    denominators = [prod(units[i:]) for i in range(len(primes) + 1)]
    counts = {'actual_leaf_evaluations': 0, 'multiplicity_groups': 0,
              'terminal_core_states': 0, 'terminal_incidence_checks': 0}

    @lru_cache(None)
    def value(axis, active):
        if not active:
            return 0
        if active & completed[axis]:
            return denominators[axis]
        if collapsed and axis == 7:
            survival = 1
            for i, ids in enumerate(buckets, 7):
                residues = {labels[j][1] % primes[i] for j in ids if active >> j & 1}
                counts['terminal_incidence_checks'] += len(ids)
                survival *= min(units[i], capnums[i] * (primes[i] - len(residues)))
            counts['terminal_core_states'] += 1
            require(0 <= survival <= denominators[axis], 'bounded terminal survival')
            return denominators[axis] - survival
        require(axis < len(primes), 'all literal events resolved by the last coordinate')
        groups = Counter(active & mask for mask in matches[axis])
        counts['actual_leaf_evaluations'] += len(matches[axis])
        counts['multiplicity_groups'] += len(groups)
        offers = sorted((value(axis + 1, child), multiplicity * capnums[axis])
                        for child, multiplicity in groups.items())
        remaining, answer = units[axis], 0
        for cost, capacity in offers:
            mass = min(remaining, capacity)
            answer += mass * cost
            remaining -= mass
            if remaining == 0:
                break
        require(remaining == 0 and 0 <= answer <= denominators[axis],
                'feasible exact row minimum with total mass one')
        return answer

    result = F(value(0, (1 << len(labels)) - 1), denominators[0])
    stats = dict(states=value.cache_info().currsize, **counts)
    value.cache_clear()
    return result, stats


def calculate(base):
    ctx = _io.Context(base, SOURCES, __file__)
    candidate = ctx.fresh(CANDIDATE, PRODUCER)
    weak = ctx.read('frontier/source-budgets/adaptive_phase_head_input.json')
    profile = ctx.read('frontier/source-budgets/balanced_profile_head_input.json')
    source = load_module('terminal_verification_original_inventory',
                         Path(base) / 'frontier/source-budgets/capped_head_bellman.py')
    original = [list(pair) for pair in source.counterexample_154_labels()]
    primes, heights = profile['prime_order'], profile['heights']
    rows = [[F(x) for x in row] for row in profile['profiles']]
    require(len(primes) == len(heights) == len(rows) == 20 and
            primes[:7] == [3, 5, 7, 11, 13, 17, 19] and
            all(h == 1 for h in heights[7:]), 'exact core7/leaf13 partition')
    require(all(weak[k] == profile[k] == candidate[k]
                for k in ['prime_order', 'heights', 'profiles']), 'same complete balanced profiles')
    require(candidate['original_labels'] == original and
            candidate['four_change_labels'] == weak['labels'], 'literal original input inventories')
    require([(a, b) for a, b in zip(original, weak['labels']) if a != b] ==
            [([39, 22], [39, 14]), ([45, 43], [45, 26]),
             ([55, 11], [55, 28]), ([63, 7], [63, 32])], 'exact four global phase edits')
    units, capnums = [], []
    ancestor_checks = 0
    for p, h, row in zip(primes, heights, rows):
        require(len(row) == h + 1 and row[0] == 1 and
                all(F(1, p**e) <= row[e] <= row[e-1] for e in range(1, h+1)),
                'full feasible deterministic transcript caps')
        for e in range(1, h + 1):
            require(row[e] == p**(h-e) * row[h],
                    'each proper ancestor cap is the sum of its leaf caps')
            ancestor_checks += 1
        units.append(row[h].denominator)
        capnums.append(row[h].numerator)
    require(len(candidate['records']) == 2, 'exact two candidate diagnostics')
    records = []
    for (name, labels), given in zip([('original', original), ('four-change', weak['labels'])],
                                   candidate['records']):
        require(given['input'] == name and len(labels) == len({m for m, a in labels}) == 154
                and all(m > 1 and m % 2 == 1 and 0 <= a < m for m, a in labels),
                '154 distinct literal odd original classes')
        inventory = literal_inventory(primes, heights, labels)
        buckets = inventory[2]
        targets = {j: (primes[i], t) for i, ids in enumerate(buckets, 7)
                   for t, j in enumerate(ids)}
        injected = []
        for j, (m, a) in enumerate(labels):
            if j not in targets:
                injected.append([m, a])
                continue
            q, target = targets[j]
            cofactor = m // q
            possible = [x for x in range(m) if x % q == target and
                        x % cofactor == a % cofactor]
            require(len(possible) == 1, 'unique CRT phase preserving the entire core cofactor')
            injected.append([m, possible[0]])
        counts = {str(primes[i]): len(ids) for i, ids in enumerate(buckets, 7)}
        require(injected == given['injected_labels'] and counts == given['leaf_label_counts'],
                'all injected literal labels and complete bucket counts match')
        injected_inventory = literal_inventory(primes, heights, injected)
        require(all(len({injected[j][1] % primes[i] for j in ids}) == len(ids)
                    for i, ids in enumerate(buckets, 7)), 'simultaneous full-bucket injection')
        values, stats = {}, {}
        for prefix, current, inv in [('literal', labels, inventory),
                                     ('worst_leaf', injected, injected_inventory)]:
            for collapsed in [False, True]:
                key = prefix + ('_collapsed7' if collapsed else '_full20')
                v, statistics = exact_value(primes, current, units, capnums, inv, collapsed)
                require(v == F(given[key]), 'independent exact candidate value: ' + key)
                values[key], stats[key] = str(v), statistics
        require(values['literal_full20'] == values['literal_collapsed7'] and
                values['worst_leaf_full20'] == values['worst_leaf_collapsed7'],
                'both literal and globally injected full20/core7 equalities')
        gap = F(values['worst_leaf_full20']) - F(values['literal_full20'])
        require(gap == F(given['gap']) and gap >= 0, 'exact nonnegative terminal-phase gap')
        records.append(dict(input=name, **values, gap=str(gap), injected_labels=injected,
                            leaf_label_counts=counts, independent_statistics=stats))
    return ctx.finish(dict(
        schema='independent-terminal-phase-reduction-verification-v1',
        scope='Two fixed numerical-order diagnostics, each with literal and globally injected labels. Actual-leaf integer-cap row minimization independently verifies all eight values; no adaptive-core optimum or uniform arbitrary-core bound claimed.',
        prime_order=primes, heights=heights, profiles=profile['profiles'],
        ancestor_cap_checks=ancestor_checks, core_only_labels=78, leaf_labels=76,
        records=records))


if __name__ == '__main__':
    _io.run(CERTIFICATE, calculate, __file__)
