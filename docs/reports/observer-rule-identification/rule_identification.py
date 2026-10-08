# SPDX-License-Identifier: Apache-2.0
"""Compare passive rule identification with known post-operation permutations."""
import argparse
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, product


def trace(rule, q, state, depth):
    values = [q[state]]
    for _ in range(depth):
        state = rule[state]
        values.append(q[state])
    return tuple(values)


def passive_equal(first, second, q):
    """Exact infinite trace equality, stopping only at a repeated joint state."""
    for initial in range(len(q)):
        x = y = initial
        seen = set()
        while (x, y) not in seen:
            if q[x] != q[y]:
                return False
            seen.add((x, y))
            x, y = first[x], second[y]
    return True


def minimal_fixed_probes(n, zeros):
    allowed = list(combinations(range(n), zeros))
    for size in range(1, len(allowed) + 1):
        for family in combinations(allowed, size):
            codes = [tuple(int(x not in test) for test in family) for x in range(n)]
            if len(set(codes)) == n:
                permutations = []
                for test in family:
                    permutation = [0] * n
                    for destination, source in enumerate(list(test) +
                                                          [x for x in range(n) if x not in test]):
                        permutation[source] = destination
                    permutations.append(tuple(permutation))
                return family, codes, permutations
    raise AssertionError('Nonconstant observation permutation family must separate states')


def census(n, zeros):
    q = (0,) * zeros + (1,) * (n - zeros)
    rules = list(product(range(n), repeat=n))
    horizon = n * n
    signatures = {rule: tuple(trace(rule, q, x, horizon) for x in range(n))
                  for rule in rules}
    groups = defaultdict(list)
    for rule, signature in signatures.items():
        groups[signature].append(rule)
    for first in rules:
        for second in rules:
            assert (signatures[first] == signatures[second]) == passive_equal(first, second, q)
    baseline = len(rules) * (len(rules) - 1)
    residual = sum(len(group) * (len(group) - 1) for group in groups.values())
    fixedpoint_residual = 0
    for group in groups.values():
        positive = sum(any(x == rule[x] for x in range(n)) for rule in group)
        fixedpoint_residual += 2 * positive * (len(group) - positive)
    probes, codes, permutations = minimal_fixed_probes(n, zeros)
    decoded = {code: x for x, code in enumerate(codes)}
    for rule in rules:
        responses = [tuple(q[permutation[rule[x]]] for permutation in permutations)
                     for x in range(n)]
        assert tuple(decoded[response] for response in responses) == rule
    rate = Fraction(residual, baseline)
    return {'n': n, 'q': list(q), 'rules': len(rules),
            'passive_trace_classes': len(groups),
            'passively_exactly_identified_rules': sum(len(group) == 1 for group in groups.values()),
            'exactly_identified_but_state_blind_rules': sum(len(group) == 1 and len(set(signatures[group[0]])) < n for group in groups.values()),
            'passive_exact_rule_residual_ordered_pairs': residual,
            'baseline_ordered_distinct_rule_pairs': baseline,
            'passive_exact_rule_residual_fraction': [rate.numerator, rate.denominator],
            'passive_fixedpoint_target_residual_ordered_pairs': fixedpoint_residual,
            'minimum_fixed_output_probes': len(probes),
            'probe_zero_sets': [list(test) for test in probes],
            'probe_permutations': [list(p) for p in permutations],
            'active_rule_reconstruction_checks': len(rules),
            'nonadaptive_reset_protocol_rule_calls': n * len(probes),
            'active_exact_rule_residual_ordered_pairs': 0}


def main():
    if not __debug__:
        raise SystemExit('Run without -O: independent checks are required.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-states', type=int, choices=(3, 4), default=4)
    args = parser.parse_args()
    output = {'scope': {'min_states': 3, 'max_states': args.max_states,
                        'target': 'exact labelled total unary rule',
                        'passive': 'all reset states and arbitrary iteration depths',
                        'active': 'reset, same unknown rule, known permutation, fixed binary readout'},
              'census': [census(n, zeros) for n in range(3, args.max_states + 1)
                         for zeros in range(1, n) if zeros <= n - zeros]}
    q = (0, 0, 1, 1)
    identity = (0, 1, 2, 3)
    swap = (1, 0, 3, 2)
    probe = (0, 2, 1, 3)
    assert passive_equal(identity, swap, q)
    assert any(identity[x] == x for x in range(4))
    assert not any(swap[x] == x for x in range(4))
    assert q[probe[identity[0]]] != q[probe[swap[0]]]
    output['permanent_passive_witness'] = {
        'q': list(q), 'F': list(identity), 'G': list(swap),
        'probe_permutation': list(probe), 'reset_state': 0,
        'active_outputs': [q[probe[identity[0]]], q[probe[swap[0]]]]}
    import json
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
