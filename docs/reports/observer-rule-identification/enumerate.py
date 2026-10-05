# SPDX-License-Identifier: Apache-2.0
"""Exhaust finite unary rules under fixed noninjective binary observations."""
import argparse
import itertools
import json


def relations(rule, q):
    n = len(rule)
    current = tuple(q[x] == q[y] for x in range(n) for y in range(n))
    result = [current]
    for _ in range(n):
        current = tuple(q[x] == q[y] and current[rule[x] * n + rule[y]]
                        for x in range(n) for y in range(n))
        result.append(current)
    return tuple(result)


def direct_relations(rule, q):
    n = len(rule)
    histories = [(q[x],) for x in range(n)]
    outputs = [tuple(histories[x] == histories[y]
                     for x in range(n) for y in range(n))]
    state = list(range(n))
    for _ in range(n):
        state = [rule[x] for x in state]
        histories = [histories[x] + (q[state[x]],) for x in range(n)]
        outputs.append(tuple(histories[x] == histories[y]
                             for x in range(n) for y in range(n)))
    return tuple(outputs)


def canonical(rule, q):
    n = len(rule)
    images = []
    for p in itertools.permutations(range(n)):
        if any(q[p[x]] != q[x] for x in range(n)):
            continue
        conjugate = [0] * n
        for x in range(n):
            conjugate[p[x]] = p[rule[x]]
        images.append(tuple(conjugate))
    return min(images)


def history(rule, q, state, depth):
    result = [q[state]]
    for _ in range(depth):
        state = rule[state]
        result.append(q[state])
    return tuple(result)


def census(n, zeros):
    q = (0,) * zeros + (1,) * (n - zeros)
    groups = {}
    discrete = tuple(x == y for x in range(n) for y in range(n))
    observable = 0
    recovered = 0
    for rule in itertools.product(range(n), repeat=n):
        profile = relations(rule, q)
        assert profile == direct_relations(rule, q)
        assert profile[-1] == profile[-2]
        if profile[-1] != discrete:
            continue
        observable += 1
        depth = next(k for k, relation in enumerate(profile) if relation == discrete)
        labels = {history(rule, q, x, depth): x for x in range(n)}
        recovered_rule = tuple(labels[history(rule, q, x, depth + 1)[1:]]
                               for x in range(n))
        assert recovered_rule == rule
        recovered += 1
        groups.setdefault(profile, {}).setdefault(canonical(rule, q), rule)
    ambiguous = [g for g in groups.values() if len(g) > 1]
    return {'n': n, 'q': list(q), 'rules': n ** n,
            'eventually_discrete_rules': observable, 'one_extra_depth_reconstruction_checks': recovered,
            'labelled_partition_profiles': len(groups),
            'profiles_with_nonconjugate_rules': len(ambiguous),
            'observation_preserving_conjugacy_classes': len({key for group in groups.values() for key in group})}


def main():
    if not __debug__:
        raise SystemExit('Run without -O: cross-check assertions are required.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-states', type=int, choices=(3, 4, 5), default=4)
    args = parser.parse_args()
    data = {'scope': {'min_states': 3, 'max_states': args.max_states, 'rules': 'total unary', 'observations': 'canonical nonconstant noninjective binary splits'},
            'census': [census(n, zeros) for n in range(3, args.max_states + 1)
                       for zeros in range(1, n) if zeros <= n - zeros],
            'witness': {'q': [0, 0, 1], 'F': [0, 2, 0], 'G': [1, 2, 0]}}
    q = tuple(data['witness']['q'])
    f, g = tuple(data['witness']['F']), tuple(data['witness']['G'])
    assert relations(f, q) == relations(g, q)
    assert canonical(f, q) != canonical(g, q)
    data['witness']['ordered_offdiagonal_residual_counts'] = [
        sum(r[x * 3 + y] for x in range(3) for y in range(3) if x != y)
        for r in relations(f, q)]
    data['witness']['same_depth1_responses'] = [list(history(f, q, x, 1)) for x in range(3)]
    assert all(history(f, q, x, 1) == history(g, q, x, 1) for x in range(3))
    data['witness']['F_fixed_points'] = [x for x in range(3) if f[x] == x]
    data['witness']['G_fixed_points'] = [x for x in range(3) if g[x] == x]
    data['witness']['state0_length2_outputs'] = [q[f[f[0]]], q[g[g[0]]]]
    print(json.dumps(data, indent=2))


if __name__ == '__main__':
    main()
