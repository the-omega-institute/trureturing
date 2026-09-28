#!/usr/bin/env python3
"""Exact diagnostics for operation-dependent completion boundaries.

Independent minimizer uses only gcd readouts and concrete modular transitions.
No third-party dependencies; writes only the explicitly requested output path.
"""
import sys

sys.dont_write_bytecode = True
if not __debug__:
    raise SystemExit("Run without -O: exact diagnostics require assertions.")

import argparse
from collections import Counter, defaultdict, deque
from functools import lru_cache
import hashlib
import json
from math import gcd
from pathlib import Path


def factor(n):
    out = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            h = 0
            while n % p == 0:
                n //= p
                h += 1
            out.append((p, h))
        p += 1
    if n > 1:
        out.append((n, 1))
    return tuple(out)


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def phi(n):
    ans = n
    for p, _ in factor(n):
        ans = ans // p * (p - 1)
    return ans


def depth(x, p, h):
    if x == 0:
        return h
    r = 0
    while r < h and x % p == 0:
        x //= p
        r += 1
    return r


def local_encode(x, p, h, e):
    modulus = p ** h
    x %= modulus
    small_modulus = p ** (h - e)
    r = depth(x, p, h)
    if r < e:
        return (0, r, (x // p ** r) % small_modulus)
    return (1, (x // p ** e) % small_modulus)


def encode(x, H, d):
    return tuple(local_encode(x, p, h, depth(d, p, h))
                 for p, h in factor(H))


def predicted_count(H, d):
    answer = 1
    for p, h in factor(H):
        e = depth(d, p, h)
        m = p ** (h - e)
        answer *= m + e * phi(m)
    return answer


def local_add(state, c, p, h, e):
    assert c % (p ** e) == 0
    m = p ** (h - e)
    delta = c // p ** e
    if state[0] == 1:
        return (1, (state[1] + delta) % m)
    _, r, u = state
    return (0, r, (u + p ** (e - r) * delta) % m)


def local_scalar(state, a, p, h, e):
    assert a > 0
    m = p ** (h - e)
    if state[0] == 1:
        return (1, a * state[1] % m)
    _, r, u = state
    s = 0
    v = a
    while v % p == 0:
        v //= p
        s += 1
    if r + s < e:
        return (0, r + s, v * u % m)
    return (1, p ** (r + s - e) * v * u % m)


def local_product(left, right, p, h, e):
    m = p ** (h - e)
    if left[0] == right[0] == 1:
        return (1, p ** e * left[1] * right[1] % m)
    if left[0] == 1:
        left, right = right, left
    if right[0] == 1:
        return (1, p ** left[1] * left[2] * right[1] % m)
    r = left[1] + right[1]
    u = left[2] * right[2] % m
    if r < e:
        return (0, r, u)
    return (1, p ** (r - e) * u % m)


def label_partition(keys):
    lookup = {}
    colors = []
    for key in keys:
        if key not in lookup:
            lookup[key] = len(lookup)
        colors.append(lookup[key])
    return colors


@lru_cache(maxsize=None)
def multiplication_generators(H):
    """Generate all units greedily, plus primes dividing H; verify full monoid."""
    group = {1}
    units = []
    for u in range(1, H):
        if gcd(u, H) != 1 or u in group:
            continue
        units.append(u)
        old_group = tuple(group)
        v = u
        while v not in group:
            group.update(a * v % H for a in old_group)
            v = v * u % H
    assert group == {u for u in range(H) if gcd(u, H) == 1}
    generators = tuple(sorted(set(units + [p for p, _ in factor(H)])))
    reached = {1}
    todo = deque([1])
    while todo:
        x = todo.popleft()
        for a in generators:
            y = x * a % H
            if y not in reached:
                reached.add(y)
                todo.append(y)
    assert len(reached) == H
    return generators


def independent_refine(H, d):
    """Moore refinement, with no use of encode or predicted_count."""
    ops = [('mul', a) for a in multiplication_generators(H)]
    ops.append(('add', d))
    transitions = []
    for kind, a in ops:
        transitions.append([(x * a if kind == 'mul' else x + a) % H
                            for x in range(H)])
    history = [label_partition([gcd(x, H) for x in range(H)])]
    scans = 0
    while True:
        previous = history[-1]
        colors = label_partition((previous[x],) +
                                 tuple(previous[t[x]] for t in transitions)
                                 for x in range(H))
        scans += H * len(ops)
        if max(colors) == max(previous):
            assert colors == previous
            break
        history.append(colors)
    return history, ops, transitions, scans


def distinguishing_word(x, y, history, ops, transitions):
    """Recover an actual suffix solely from refinement partitions."""
    level = len(history) - 1
    assert history[level][x] != history[level][y]
    word = []
    while history[0][x] == history[0][y]:
        while level > 0 and history[level - 1][x] != history[level - 1][y]:
            level -= 1
        assert level > 0
        for j, t in enumerate(transitions):
            if history[level - 1][t[x]] != history[level - 1][t[y]]:
                word.append(ops[j])
                x, y = t[x], t[y]
                level -= 1
                break
        else:
            raise AssertionError('refinement witness missing')
    return word


def run_word(x, word, H):
    for kind, a in word:
        x = (x * a if kind == 'mul' else x + a) % H
    return x


def affine_witness(x, y, H, d):
    """Explicit global d-translation realizing a local separating probe."""
    if gcd(x, H) != gcd(y, H):
        return 1, 0
    for p, h in factor(H):
        e = depth(d, p, h)
        if local_encode(x, p, h, e) == local_encode(y, p, h, e):
            continue
        r = depth(x, p, h)
        a = p ** (e - r) if r < e else 1
        m = p ** (h - e)
        assert m > 1
        unit = d // p ** e
        b = (-(a * x // p ** e) * pow(unit, -1, m)) % m
        assert gcd(a * x + d * b, H) != gcd(a * y + d * b, H)
        return a, b
    raise AssertionError('equal local encodings unexpectedly require witness')


def verify_model(H, d, counters, digest, retain=False):
    history, ops, transitions, scans = independent_refine(H, d)
    theoretical = [encode(x, H, d) for x in range(H)]
    assert label_partition(theoretical) == history[-1]
    count = max(history[-1]) + 1
    assert count == predicted_count(H, d)
    counters['source_residue_partition_comparisons'] += H
    counters['refinement_transition_scans'] += scans
    reps = {}
    for x, c in enumerate(history[-1]):
        reps.setdefault(c, x)
    by_output = defaultdict(list)
    for x in reps.values():
        by_output[gcd(x, H)].append(x)
    max_fiber = max(map(len, by_output.values()))
    assert max_fiber == phi(H // d)
    assert len(by_output[1]) == max_fiber
    counters['max_record_fiber_checks'] += 1
    for group in by_output.values():
        for x, y in zip(group, group[1:]):
            word = distinguishing_word(x, y, history, ops, transitions)
            assert gcd(run_word(x, word, H), H) != gcd(run_word(y, word, H), H)
            a, b = affine_witness(x, y, H, d)
            assert gcd(a * x + d * b, H) != gcd(a * y + d * b, H)
            counters['distinguishing_suffixes'] += 1
            counters['global_affine_witnesses'] += 1
            counters['witness_word_operations'] += len(word)
            counters['witness_max_length'] = max(counters['witness_max_length'], len(word))
            digest.update(json.dumps([H, d, x, y, word, a, b], separators=(',', ':')).encode())
    row = {'H': H, 'd': d, 'states': count,
           'proper_refinement_rounds': len(history) - 1,
           # Distinct values of one finite record map decoded jointly with gcd.
           'max_extra_record_alphabet': max_fiber,
           'operation_generator_count': len(ops)}
    return row, theoretical if retain else None


def local_checks(counters):
    models = []
    for p in [2, 3, 5, 7, 11]:
        h = 1
        while p ** h <= 256:
            for e in range(h + 1):
                models.append((p, h, e))
            h += 1
    for p, h, e in models:
        P = p ** h
        states = [local_encode(x, p, h, e) for x in range(P)]
        for x in range(P):
            # All scalar residues, using P as the positive representative of zero.
            for y in range(P):
                a = y if y else P
                expected = local_encode(x * a, p, h, e)
                assert local_scalar(states[x], a, p, h, e) == expected
                assert local_product(states[x], states[y], p, h, e) == expected
                counters['local_scalar_updates'] += 1
                counters['two_abstract_operand_products'] += 1
            for c in range(0, P, p ** e):
                assert local_add(states[x], c, p, h, e) == local_encode(x + c, p, h, e)
                counters['local_allowed_addition_updates'] += 1
        for a in [P * p, P * p + 1]:
            for x in [0, 1, P - 1]:
                assert local_scalar(states[x], a, p, h, e) == local_encode(x * a, p, h, e)
                counters['large_positive_scalar_edge_checks'] += 1
    counters['local_update_models'] = len(models)
    return models


def joint_checks(H, codes, counters):
    ds = sorted(codes)
    for i, d in enumerate(ds):
        for e in ds[i:]:
            joint = list(zip(codes[d], codes[e]))
            assert label_partition(joint) == label_partition(codes[gcd(d, e)])
            counters['same_source_join_models'] += 1
            counters['same_source_join_source_checks'] += H


def addition_library_checks(counters):
    for H in range(2, 49):
        for additives in [[], [2], [3], [7], [10], [2, 5], [4, 6], [H // 2, H]]:
            d = H
            for c in additives:
                d = gcd(d, c)
            reached = {0}
            queue = deque([0])
            while queue:
                x = queue.popleft()
                for c in additives:
                    y = (x + c) % H
                    if y not in reached:
                        reached.add(y)
                        queue.append(y)
            assert reached == set(range(0, H, d))
            counters['addition_library_closure_models'] += 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    counters = Counter()
    witness_digest = hashlib.sha256()
    local_models = local_checks(counters)
    rows = []
    for p, h, e in local_models:
        row, _ = verify_model(p ** h, p ** e, counters, witness_digest)
        rows.append(row)
    counters['local_behavior_models'] = len(rows)
    small_rows = []
    for H in range(2, 97):
        if len(factor(H)) < 2:
            continue
        for d in divisors(H):
            row, _ = verify_model(H, d, counters, witness_digest)
            small_rows.append(row)
    counters['small_composite_behavior_models'] = len(small_rows)
    primary_rows = []
    codes = {}
    for d in divisors(5040):
        row, code = verify_model(5040, d, counters, witness_digest, retain=True)
        primary_rows.append(row)
        codes[d] = code
    counters['template_5040_behavior_models'] = len(primary_rows)
    joint_checks(5040, codes, counters)
    addition_library_checks(counters)
    for x in range(5040):
        q = gcd(x, 5040)
        r = depth(q, 2, 4)
        q_next = q if r < 3 else 2 * q if r == 3 else q // 2
        assert q_next == gcd(x + 2520, 5040)
        counters['addition_2520_coarse_updates'] += 1
    assert len(set(codes[7])) == 1440
    assert len(set(codes[10])) == 1512
    assert len(set(zip(codes[7], codes[10]))) == 5040
    assert len(set(codes[2520])) == 60
    # A macro boundary cannot generally expose +2 as an individual operation.
    macro_witness = None
    first = {}
    for x, code in enumerate(codes[7]):
        if code in first:
            y = first[code]
            if encode(x + 2, 5040, 7) != encode(y + 2, 5040, 7):
                macro_witness = {'x': y, 'y': x,
                                 'same_plus_7_macro_state': True,
                                 'different_states_after_plus_2': True}
                break
        else:
            first[code] = x
    assert macro_witness is not None
    output = {
        'schema': 'fib-operation-resolution-exact-diagnostics-v1',
        'claim_scope': 'Finite diagnostic evidence for paper theorems; no Lean or RH claim.',
        'method': {
            'independent_minimizer': 'Moore refinement of concrete modular transitions and gcd outputs; does not call local encoding or count formulas.',
            'multiplication_generators': 'Greedy unit-group generators plus prime divisors; independently verifies the generated multiplicative monoid contains every residue.',
            'template_5040_multipliers': list(multiplication_generators(5040)),
            'witness_selection': 'Adjacent final-class representatives within each original gcd-output fiber; two separately constructed legal distinguishing suffixes per selected pair.',
            'joint_scope': 'Every unordered pair with repetition of divisors of 5040; equality of partitions, not only cardinality.'},
        'counts': dict(sorted(counters.items())),
        'witness_sha256': witness_digest.hexdigest(),
        'macro_exposure_counterexample': macro_witness,
        'examples': [{'addends': a, 'd': d, 'states': predicted_count(5040, d),
                      'max_extra_record_alphabet': phi(5040 // d)}
                     for a, d in [([], 5040), ([2], 2), ([3], 3), ([5], 5),
                                  ([7], 7), ([10], 10), ([13], 1),
                                  ([2520], 2520), ([2, 5], 1)]],
        'all_5040_models': primary_rows,
        'local_model_dimensions': rows,
        'small_composite_summary': {'minimum_H': 2, 'maximum_H': 96,
                                    'distinct_windows': len(set(r['H'] for r in small_rows)),
                                    'maximum_proper_refinement_rounds': max(r['proper_refinement_rounds'] for r in small_rows)}
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(output, ensure_ascii=False, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    print(json.dumps({'status': 'pass', 'out': str(args.out), 'counts': output['counts']}, sort_keys=True))


if __name__ == '__main__':
    main()
