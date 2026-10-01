"""Exact selected-prefix matching and the free-45 phase classification.

This consumer applies existing common-tree and selected-null interfaces.
It does not solve an LP, recompute the Report 822 atlas, or verify Lean.
All checks remain active under python -O. Paths are explicit or adjacent.
"""
import argparse
from collections import defaultdict
from itertools import combinations
import json
from pathlib import Path

SELECTED = (15, 21, 45, 33, 35, 39, 63, 51, 57, 55, 105, 75,
            69, 65, 99, 77, 85, 117, 95, 165, 91, 147, 225)
PRIMES = (3, 5, 7, 11, 13, 17, 19, 23)


def depth(m, p):
    result = 0
    while m % p == 0:
        result += 1
        m //= p
    return result


def prefix_partitions(family):
    out = {}
    for p in PRIMES:
        layers = {}
        for r in range(1, max(depth(m, p) for m in family) + 1):
            groups = {}
            for m, a in sorted(family.items()):
                if depth(m, p) >= r:
                    groups.setdefault(str(a % (p ** r)), []).append(m)
            layers[str(r)] = groups
        out[str(p)] = layers
    return out


def first_obstruction(left, right):
    """Return the first shared-precision mismatch, or None for equal tries."""
    if left.keys() != right.keys():
        raise ValueError('selected numerical inventories differ')
    for p in PRIMES:
        for m, n in combinations(sorted(left), 2):
            for r in range(1, min(depth(m, p), depth(n, p)) + 1):
                modulus = p ** r
                if ((left[m] - left[n]) % modulus == 0) != ((right[m] - right[n]) % modulus == 0):
                    return {'prime': p, 'depth': r, 'labels': [m, n],
                            'source_prefixes': [left[m] % modulus, left[n] % modulus],
                            'target_prefixes': [right[m] % modulus, right[n] % modulus]}
    return None


def fixed_signature(a, fixed):
    """Relations of the variable45 prefix to every fixed named prefix."""
    return tuple((a - b) % (p ** r) == 0
                 for p in (3, 5)
                 for m, b in sorted(fixed.items())
                 for r in range(1, min(depth(45, p), depth(m, p)) + 1))


def compute(certificate):
    checks = 0

    def require(condition, message):
        nonlocal checks
        checks += 1
        if not condition:
            raise ValueError(message)

    require(certificate['schema'] == 'e7-common-prefix-phase-classes-v1', 'schema')
    records = certificate['actual_family']
    source = dict(records)
    require(len(records) == len(source) == 25, 'distinct25 numerical labels')
    require(set(source) == {3, 9, *SELECTED}, 'literal selected inventory')
    require(tuple(certificate['primes']) == PRIMES, 'prime coordinates')
    for m, a in source.items():
        require(type(m) is int and type(a) is int and m > 1 and m % 2 and 0 <= a < m,
                'legal original')
        if m in (3, 9, 45):
            require(a == {3: 0, 9: 1, 45: 11}[m], 'literal anchor/opposing phase')
        else:
            e = depth(m, 3)
            n = m // (3 ** e)
            require(a % n == 0, 'shared complete nonternary zero prefix')
            require(e in (0, 1, 2), 'selected ternary height')
            if e:
                require(a % (3 ** e) == (1 if e == 1 else 4), 'literal ternary role')
    partitions = prefix_partitions(source)
    require(partitions == certificate['expected_prefix_partitions'], 'complete first/second prefix partitions')
    require(partitions['5']['2'] == {'0': [75, 225]}, 'shared deep5 prefix')
    require(partitions['7']['2'] == {'0': [147]}, 'deep7 label precision')
    require(partitions['3']['2'] == {'1': [9], '2': [45], '4': [63, 99, 117, 225]},
            'all shared deep3 roles')

    swap_from, swap_to = certificate['tree_leaf_swap']
    require((swap_from, swap_to) == (4, 7), 'declared common non-affine control')

    def leaf_swap(x):
        r = x % 9
        return x + ({swap_from: swap_to, swap_to: swap_from}.get(r, r) - r)

    def transport(m, a):
        e = depth(m, 3)
        if e < 2:
            return a
        n = m // (3 ** e)
        modulus = 3 ** e
        target = leaf_swap(a % modulus)
        return (a + n * (((target - a) * pow(n, -1, modulus)) % modulus)) % m

    tree_target = {m: transport(m, a) for m, a in source.items()}
    changed = {str(m): [source[m], a] for m, a in tree_target.items() if a != source[m]}
    require(changed == {'63': [49, 7], '99': [22, 88], '117': [13, 52], '225': [175, 25]},
            'simultaneous CRT phase images')
    require(first_obstruction(source, tree_target) is None, 'common tree profile preserved')
    require(tree_target[9] == 1 and tree_target[45] % 9 == 2 and tree_target[63] % 9 == 7,
            'fixed1/2 versus moved4 affine obstruction')
    for height in (1, 2, 3):
        size = 3 ** height
        require(len({leaf_swap(x) for x in range(size)}) == size, 'tree bijection')
        for x in range(size):
            require(leaf_swap(x) % 3 == x % 3, 'first prefix preserved')
            require(leaf_swap(leaf_swap(x)) == x, 'tree inverse')
            require(leaf_swap(x) // 9 == x // 9, 'higher suffix retained')

    deep = dict(source)
    deep[225] = certificate['deep_control_phase']
    require(type(deep[225]) is int and 0 <= deep[225] < 225, 'canonical deep-control phase')
    deep_obstruction = first_obstruction(source, deep)
    require(deep_obstruction == {'prime': 5, 'depth': 2, 'labels': [75, 225],
                                'source_prefixes': [0, 0], 'target_prefixes': [0, 5]},
            'nonorbit deep5 obstruction')
    require(all(source[m] % p == deep[m] % p for m in source for p in PRIMES if m % p == 0),
            'deep control keeps every first digit')
    require(deep[225] % 9 == 4 and deep[225] % 5 == 0, 'deep control remains core-null')

    root = dict(source)
    root[15] = certificate['core_failure_phase']
    require(type(root[15]) is int and 0 <= root[15] < 15, 'canonical root-control phase')
    root_obstruction = first_obstruction(source, root)
    require(root_obstruction == {'prime': 3, 'depth': 1, 'labels': [9, 15],
                                'source_prefixes': [1, 1], 'target_prefixes': [1, 2]},
            'nonorbit first-root obstruction')
    require(5 % 3 == root[15] % 3 and 1 == root[15] % 5, 'one common core-intersection witness')

    fixed = {m: a for m, a in source.items() if m != 45}
    orbits = defaultdict(list)
    for a in range(45):
        orbits[fixed_signature(a, fixed)].append(a)
    orbit_list = sorted(orbits.values(), key=lambda values: min(values))
    require(orbit_list == certificate['expected_stabilizer_orbits'], 'exact fixed24 orbit list')
    require(len(orbit_list) == 10, 'ten strict stabilizer orbits')
    groups = [
        ('dead ternary leaf', None, [a for a in range(45) if a % 9 in (0, 1, 3, 6)]),
        ('leaf4 zero5', 40, [40]),
        ('leaf7 zero5', 25, [25]),
        ('root2 nonzero5', 11, [a for a in range(45) if a % 9 in (2, 5, 8) and a % 5 != 0]),
        ('root2 zero5', 20, [a for a in range(45) if a % 9 in (2, 5, 8) and a % 5 == 0]),
        ('leaf4 nonzero5', 31, [a for a in range(45) if a % 9 == 4 and a % 5 != 0]),
        ('leaf7 nonzero5', 16, [a for a in range(45) if a % 9 == 7 and a % 5 != 0])]
    require([len(g[2]) for g in groups] == certificate['expected_reuse_group_counts'] == [20, 1, 1, 12, 3, 4, 4],
            'seven reuse group counts')
    require(sorted(a for _, _, values in groups for a in values) == list(range(45)), 'disjoint exhaustive45 partition')
    require(len({fixed_signature(a, fixed) for a in groups[0][2]}) == 4, 'dead group combines four strict orbits')
    for _, representative, values in groups[1:]:
        require(representative in values, 'representative membership')
        require(len({fixed_signature(a, fixed) for a in values}) == 1, 'one nondead orbit per reuse group')
    require(all(a % 15 == 10 for a in (25, 40)), 'selected15 contains both zero5 short leaves')
    require(all(a % 3 == 0 or a % 9 == 1 for a in groups[0][2]), 'anchor containment')
    require(fixed_signature(31, fixed) != fixed_signature(16, fixed), 'deep selected leaf4 blocks leaf4/7 interchange')
    covered = sorted(a for _, _, values in groups[:4] for a in values)
    residual = sorted(a for _, _, values in groups[4:] for a in values)
    require(len(covered) == certificate['expected_reusable_phase_count'] == 34, '34 directly reusable phases')
    require(len(residual) == 11, '11 residual phases')

    # Explicit maps in the common stabilizer, one for each member of the
    # transported808 group. No actual original other than45 is rephased alone.
    for a in groups[3][2]:
        leaf, digit = a % 9, a % 5
        perm3 = lambda t: {leaf: 2, 2: leaf}.get(t, t)
        perm5 = lambda t: {digit: 1, 1: digit}.get(t, t)
        require(perm3(leaf) == 2 and perm5(digit) == 1, 'variable45 maps to11')
        for m, b in fixed.items():
            e3, e5 = depth(m, 3), depth(m, 5)
            if e3:
                require((perm3(b % 9) if e3 >= 2 else b % 3) == b % (3 ** e3), 'fixed ternary label')
            if e5:
                require(perm5(b % 5) == b % 5, 'fixed quinary root')
                if e5 == 2:
                    require(b % 25 == 0, 'designated quinary child remains fixed')

    return {'schema': certificate['schema'], 'checks': checks,
            'prefix_partitions': partitions,
            'common_tree_nonaffine_control': {'changed_phases': changed, 'matching': True,
                'affine_obstruction': 'Selected leaves1 and2 fixed implies u=1,v=0 mod9, so leaf4 cannot move to7.'},
            'deep_nonorbit_control': {'changed225': [source[225], deep[225]], 'obstruction': deep_obstruction,
                                      'first_digits_unchanged': True, 'core_null_preserved': True},
            'root_nonorbit_control': {'changed15': [source[15], root[15]], 'obstruction': root_obstruction,
                                      'core_hit': {'ternary_leaf': 5, 'all_nonternary_roots': 1}},
            'strict_stabilizer_orbits': orbit_list,
            'reuse_groups': [{'name': name, 'representative': rep, 'phases': values, 'count': len(values)} for name, rep, values in groups],
            'reusable_phases_subject_to_report822': covered,
            'residual_phases': residual, 'residual_representatives': [20, 31, 16],
            'scope': 'Fixed other22 mixed phases and both anchors; conditional reuse of completed Report822 all-pure atlas with its source normalizations and full support/tail contract. No LP or Lean verification.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    local = Path(__file__).resolve().parent
    parser.add_argument('--certificate', type=Path, default=local / 'common_prefix_phase_classes_certificate.json')
    parser.add_argument('--result', type=Path, default=local / 'common_prefix_phase_classes.json')
    parser.add_argument('--write-result', type=Path)
    args = parser.parse_args()
    result = compute(json.loads(args.certificate.read_text()))
    if args.write_result is None:
        if result != json.loads(args.result.read_text()):
            raise ValueError('retained result mismatch')
    else:
        args.write_result.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'checks': result['checks'], 'strict_orbits': 10, 'reuse_groups': 7,
                      'reusable_phases': 34, 'residual_phases': 11}, sort_keys=True))


if __name__ == '__main__':
    main()
