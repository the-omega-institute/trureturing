#!/usr/bin/env python3
"""Exact one-child/group Hall obstructions on the actual HSW p=11 seed.

Reads the sibling literal parameterized-family reconstruction. Verifies
private CYLINDERS against every represented label, including all heights,
without materializing 19 million APs or sampling the enormous CRT period.
The map check is pointwise in the common retained cofactor coordinates:
the same bounds hold for cofactor-dependent root choices/permutations,
although their uncovered sets need not be fixed arithmetic cylinders.
The obstruction concerns this specified transducer, not all transforms.
"""
import argparse
import importlib.util
from fractions import Fraction as F
from itertools import combinations, permutations
from math import gcd, prod
from pathlib import Path
import json


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def crt(residues):
    a, modulus = 0, 1
    for r, m in residues:
        require(gcd(modulus, m) == 1, 'noncoprime CRT factors')
        a += modulus*(((r-a)*pow(modulus, -1, m)) % m)
        modulus *= m
        a %= modulus
    return a, modulus


def audit_complete_tree(family, root, closing, height, power_primes):
    """Structural coverage: each complete path ends in a containing AP.

    At a power node every nonzero coordinate has a unique height/digit;
    a zero coordinate is covered by one of the present closing classes.
    This is a finite tree certificate, not exhaustive period enumeration.
    """
    rows = family['normal_families']
    require(root not in power_primes and closing not in power_primes
            and root != closing and len(set(power_primes)) == len(power_primes),
            'repeated or overlapping prime roles')
    expected_period_factors = {str(p): (height if p in power_primes else 1)
                              for p in (root, closing, *power_primes)}
    require(family['period_factorization'] == expected_period_factors,
            'incorrect full original period factorization')
    require(family['period'] == prod(int(p)**e for p, e in expected_period_factors.items()),
            'incorrect full original period')
    canonical = {
        (tuple(row['primes']), tuple(int(row['digits'][str(p)]) for p in row['primes']))
        for row in rows
    }
    support_counts = {}
    for row in rows:
        shape = tuple(row['primes'])
        require(shape and shape == tuple(sorted(set(shape)))
                and set(shape) <= {root, *power_primes}, 'invalid normal modulus support')
        require(set(row['digits']) == {str(p) for p in shape}
                and set(row['exponent_ranges']) == {str(p) for p in shape},
                'normal coordinate keys do not match the modulus')
        require(all((0 if p == root else 1) <= int(row['digits'][str(p)]) < p
                    for p in shape), 'invalid literal normal residue digit')
        require(row['expanded_label_count'] == height**sum(p != root for p in shape),
                'incorrect normal family label count')
        support_counts.setdefault(shape, []).append(row)
        for p in shape:
            require(row['exponent_ranges'][str(p)] == ([1, 1] if p == root else [1, height]),
                    'unexpected literal exponent range')
    require(all(len(v) == 1 or (key == (root,) and len(v) == 7)
                for key, v in support_counts.items()), 'unallowed repeated numerical modulus shape')
    require({int(row['digits'][str(root)]) for row in support_counts[(root,)]} == set(range(4, 11)),
            'incorrect seven pure-root residues')
    require(family['pure11_roots'] == list(range(4, 11))
            and family['nonpure_roots'] == list(range(4)), 'incorrect root partition metadata')
    closing_map = {row['prime']: row for row in family['closing_families']}
    require(len(family['closing_families']) == len(power_primes)
            and set(closing_map) == set(power_primes), 'missing or repeated closing family')
    for row in closing_map.values():
        require(row['exponent_range'] == [1, height] and height == closing-1,
                'incomplete closing exponent range')
        require(row['p_residue'] == 0 and row['q_residue'] == 'j'
                and row['modulus'] == f'{closing}*p^j', 'incorrect literal closing AP')
    require(family['shared_closing_class'] == [0, closing], 'missing shared closing class')
    leaves = nodes = 0

    def walk(node, digits):
        nonlocal leaves, nodes
        if node['kind'] == 'power':
            p = node['prime']
            require(p in power_primes and p not in digits and len(node['tail']) == p-1,
                    'incomplete or repeated-coordinate power node')
            nodes += 1
            for digit, child in enumerate(node['tail'], 1):
                walk(child, {**digits, p: digit})
        else:
            require(node['kind'] == 'leaf', 'unknown tree node')
            m = node['modulus']
            shape = tuple(p for p in sorted(digits) if m % p == 0)
            require(prod(shape) == m and m > 1, 'leaf modulus is not a subset of path primes')
            key = (shape, tuple(digits[p] for p in shape))
            require(key in canonical, 'path cylinder has no containing canonical AP family')
            leaves += 1

    tree = family['tree']
    require(tree['kind'] == 'root' and tree['prime'] == root
            and len(tree['children']) == root, 'incomplete root partition')
    for r, child in enumerate(tree['children']):
        walk(child, {root: r})
    count = sum(height**sum(p != root for p in row['primes']) for row in rows)
    count += 1+height*len(power_primes)
    require(count == family['expanded_original_label_count'], 'literal label count mismatch')
    return dict(symbolic_nonzero_leaf_paths=leaves, power_nodes=nodes,
                represented_original_labels=count)


def private_cylinder(family, coords, target, power_primes, all_primes, height):
    require(all(0 < coords[p] < p for p in power_primes), 'higher heights may meet this cylinder')
    require(coords[23] == 1, 'closing residues are not excluded')
    a, W = crt([(coords[p], p) for p in all_primes])
    require(family['period'] % W == 0, 'private cylinder does not divide full original period')
    active = []
    high_excluded = 0
    for row in family['normal_families']:
        # Only the all-height-one instance can meet this ENTIRE cylinder:
        # every other instance requires divisibility by one power prime.
        high_excluded += row['expanded_label_count']-1
        residue, modulus = crt([(int(row['digits'][str(p)]), p) for p in row['primes']])
        if (a-residue) % modulus == 0:
            active.append((row['id'], residue, modulus))
        for p in row['primes']:
            if p != 11:
                require(a % p != 0, 'a higher-height normal label was not uniformly excluded')
    closing_excluded = 1
    require(a % 23 != 0, 'shared closing class meets the cylinder')
    for row in family['closing_families']:
        p = row['prime']
        for j in range(1, height+1):
            # Every closing class includes x=0 mod p^j.
            require(a % p != 0, 'closing family may meet the cylinder')
            closing_excluded += 1
    require(len(active) == 1 and active[0][1:] == (1, target),
            f'not private for literal 1 mod{target}: {active}')
    require(high_excluded+len(family['normal_families'])+closing_excluded
            == family['expanded_original_label_count'], 'not every original label was accounted for')
    return dict(root=coords[11], residue=a, modulus=W, density=str(F(1, W)),
                coordinates=coords, active_original=list(active[0]),
                all_higher_normal_labels_excluded=high_excluded,
                all_closing_labels_excluded=closing_excluded)


def hall_check(family, q, witnesses, all_primes):
    source_roots = tuple(family['nonpure_roots'])
    k = min(q, len(source_roots))
    by_root = {w['root']: w for w in witnesses}
    W = witnesses[0]['modulus']
    image_modulus = q*W//11
    require(all(w['modulus'] == W for w in witnesses), 'incompatible source-cylinder periods')
    require(len(by_root) == len(witnesses) and set(by_root) <= set(source_roots),
            'duplicate or ineligible private roots')
    require(all(all(w['coordinates'][p] == witnesses[0]['coordinates'][p]
                    for p in all_primes if p != 11) for w in witnesses),
            'private witnesses do not share one cofactor cylinder')
    expected_group = q*q
    maps = 0
    minimum_uncovered = None
    for chosen in combinations(source_roots, k):
        for target_digits in permutations(range(q), k):
            mapping = dict(zip(chosen, target_digits))
            images = []
            for r in chosen:
                if r not in by_root:
                    continue
                coords = by_root[r]['coordinates']
                b = mapping[r]
                conditions = [(b+q*coords[q], q*q)]
                conditions += [(coords[p], p) for p in all_primes if p not in (11, q)]
                a, modulus = crt(conditions)
                require(modulus == image_modulus and a % q == b,
                        'incorrect literal image cylinder')
                require((a//q) % q == coords[q], 'old q first digit was not retained')
                require((a-(b+q)) % expected_group == 0,
                        'literal 1 mod q does not produce its claimed child')
                images.append((r, a, modulus, b))
            require(len({b for _, _, _, b in images}) == len(images),
                    'different root demands were identified')
            # Every source point in each cylinder belongs ONLY to 1 mod q.
            # Thus all witnesses have singleton support {output modulus q^2}.
            # That group's one AP fixes one lowest q digit and serves at most one.
            # All private witnesses have the SAME cofactor coordinates. Every
            # allowed map is checked here, so this deficit holds separately at
            # each cofactor, even when the choice of map depends on it. Summing
            # those fibres gives the same mass; it need not leave fixed AP holes.
            demands = len(images)
            require(demands >= 3 and demands > 1, 'Hall deficit not certified')
            uncovered = F(demands-1, image_modulus)
            minimum_uncovered = uncovered if minimum_uncovered is None else min(minimum_uncovered, uncovered)
            maps += 1
    return dict(q=q, selected_root_count=k, private_root_count=len(witnesses),
                output_modulus_group=expected_group, group_capacity=1,
                root_maps_checked=maps, image_cylinder_modulus=image_modulus,
                uncovered_density_lower_bound=str(minimum_uncovered),
                scope='one complete source-branch child per output-modulus group; no arbitrary new APs',
                cofactor_dependent_maps='same pointwise deficit; uncovered sets need not be AP cylinders')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--family', type=Path, default=Path(__file__).with_name('hsw11_family.py'))
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('hsw_literal_family', args.family)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    family = module.build_family()
    all_primes = tuple(sorted((3, 5, 7, 11, 13, 17, 19, 23)))
    power_primes = (3, 5, 7, 13, 17, 19)
    tree = audit_complete_tree(family, 11, 23, 22, power_primes)
    witnesses3 = [private_cylinder(family,
                    {3:1, 5:2, 7:2, 13:2, 17:2, 19:1, 23:1, 11:r},
                    3, power_primes, all_primes, 22) for r in range(4)]
    witnesses5 = [private_cylinder(family,
                    {3:2, 5:1, 7:3, 13:3, 17:3, 19:1, 23:1, 11:r},
                    5, power_primes, all_primes, 22) for r in (1, 2, 3)]
    results = [hall_check(family, 3, witnesses3, all_primes),
               hall_check(family, 5, witnesses5, all_primes)]
    require(results[0]['uncovered_density_lower_bound'] == '2/30421755', 'q3 density mismatch')
    require(results[1]['uncovered_density_lower_bound'] == '2/50702925', 'q5 density mismatch')
    print(json.dumps(dict(success=True, tree_certificate=tree,
                          normal_family_count=len(family['normal_families']),
                          private_cylinders_q3=witnesses3, private_cylinders_q5=witnesses5,
                          hall_results=results,
                          source='HSW arXiv:2104.00602v1 Figures18--22 reconstructed literal family',
                          verification='finite structural tree and exact all-height cylinder proof; no full-period enumeration or Lean claim'),
                     sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
