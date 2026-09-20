#!/usr/bin/env python3
"""Exact private-region obstruction for a reserved HSW transport palette.

Allows one standard modulus-9 image and arbitrarily many other sound
descendants, with all heights on the original prime support. Other new
moduli must avoid the entire standard candidate pool, including candidates
not selected in a particular map. This is not unrestricted noncoverage.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from pathlib import Path
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
P0 = (3, 5, 7, 11, 13, 17, 19, 23)
COFACTORS = (5, 7, 13, 17, 19)
HEIGHT = 22


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def load_family():
    path = Path(__file__).resolve().with_name('hsw11_family.py')
    spec = importlib.util.spec_from_file_location('literal_hsw11_family', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.build_family()


def validate_literal_interface(family):
    rows = family['normal_families']
    require(family['nonpure_roots'] == [0, 1, 2, 3], 'wrong available root set')
    for row in rows:
        shape = row['primes']
        require(23 not in shape and set(shape) <= set(P0), 'normal support changed')
        require(all(row['exponent_ranges'][str(p)] == ([1,1] if p == 11 else [1,HEIGHT])
                    for p in shape), 'literal height box changed')
        if 3 in shape:
            expected_digit = 1 if shape == [3] else 2
            require(row['digits']['3'] == expected_digit, 'other 3-bearing label meets 1 mod3')
    require(sum(row['primes'] == [3] for row in rows) == 1, 'private source label not unique')
    closing = family['closing_families']
    require(len(closing) == 6 and {r['prime'] for r in closing} == {3, *COFACTORS},
            'wrong closing-prime family')
    require(all(r['exponent_range'] == [1,HEIGHT] and r['p_residue'] == 0
                and r['q_residue'] == 'j' and r['modulus'] == '23*p^j' for r in closing),
            'literal closing AP changed')
    require(family['shared_closing_class'] == [0,23], 'shared closing AP changed')


def private_digit_masks(family):
    # A digit means the FIRST NONZERO digit, at any height 1,...,22.
    # At 23-coordinate j, closing avoidance requires every height <=j.
    # Each possible nonzero digit has the same summed-height probability.
    patterns = []
    for root in range(4):
        patterns.append([
            tuple((COFACTORS.index(p), row['digits'][str(p)])
                  for p in row['primes'] if p != 11)
            for row in family['normal_families']
            if 3 not in row['primes']
            and (11 not in row['primes'] or row['digits']['11'] == root)
        ])
    hist = Counter()
    for digits in product(*(range(1,p) for p in COFACTORS)):
        mask = 0
        for root in range(4):
            if not any(all(digits[k] == value for k,value in pattern)
                       for pattern in patterns[root]):
                mask |= 1 << root
        hist[mask] += 1
    require(sum(hist.values()) == 82944, 'not every nonzero digit tuple was counted')
    root_counts = [sum(count for mask,count in hist.items() if mask & (1 << r))
                   for r in range(4)]
    require(root_counts == [34758,17844,28000,25465], 'private root counts changed')
    require(dict(sorted(hist.items())) ==
            {0:48186,1:1159,3:876,5:5078,7:2180,9:1837,11:2886,13:8840,15:11902},
            'joint private-root mask counts changed')
    # Every local three-of-four choice is allowed. The one standard-9 AP
    # may be placed on any selected private root: this grants the best
    # possible choice even under cofactor-dependent root injections.
    demand_count = 0
    for mask,count in hist.items():
        possible = []
        for selected in combinations(range(4),3):
            k = sum(bool(mask & (1 << r)) for r in selected)
            possible.append(max(k-1,0))
        residual = min(possible)
        require(residual == max(mask.bit_count()-2,0), 'adaptive root accounting failed')
        demand_count += count * residual
    require(demand_count == 37710, 'residual private demand count changed')
    return hist, root_counts, demand_count


def geometric_positive(p, height):
    return (1-F(1,p**height))/(p-1)


def standard_reserved_pool(family):
    # Only candidate moduli divisible by9 can be sound for source 1 mod3.
    # An original G modulus m produces3m; an 11-bearing modulus11m
    # produces3m too. Merge these numerical shapes before summing.
    shapes = sorted({tuple(p for p in row['primes'] if p != 11)
                     for row in family['normal_families'] if 3 in row['primes']})
    require(len(shapes) == 24 and (3,) in shapes, 'wrong normalized candidate shapes')
    require(all(3 in shape and 11 not in shape and 23 not in shape for shape in shapes),
            'normal candidate and closing supports overlap')
    q_factor = geometric_positive(3,HEIGHT)/3  # exponents2,...,23
    normal = q_factor * sum((prod((geometric_positive(p,HEIGHT)
                                  for p in shape if p != 3), start=F(1))
                             for shape in shapes), F(0))
    g = lambda p: geometric_positive(p,HEIGHT)
    require(normal == q_factor*(1+g(5))*(1+g(7))*(1+g(19))*(1+g(13)+g(17)),
            'factored normal-pool polynomial changed')
    # The only closing source with a3 factor has modulus23*3^j,
    # and hence candidate modulus23*3^(j+1).
    closing = q_factor/23
    count = sum(HEIGHT**len(shape) for shape in shapes) + HEIGHT
    require(count == 12045352, 'reserved numerical modulus count changed')
    return shapes, count, normal+closing


def bracket(value, digits=18):
    scale = 10**digits
    lower = value.numerator*scale//value.denominator
    return dict(lower_numerator=lower, upper_numerator=lower+1, denominator=scale)


def result():
    family = load_family()
    validate_literal_interface(family)
    hist, roots, demand_count = private_digit_masks(family)
    # 23=0 is covered by the shared closing AP. For23=j>0 every
    # cofactor prime must have its first nonzero digit at height<=j.
    digit_mass = sum((prod((geometric_positive(p,j) for p in COFACTORS), start=F(1))
                      for j in range(1,HEIGHT+1)), F(0))/23
    required = F(demand_count,9)*digit_mass
    shapes, pool_count, reserved_mass = standard_reserved_pool(family)
    all_supported_mass = prod((F(p,p-1) for p in P0 if p != 3), start=F(1))/6
    require(all_supported_mass == F(676039,1990656), 'full-support Euler mass changed')
    vacant_capacity = all_supported_mass-reserved_mass
    gap = required-vacant_capacity
    require(required > F(47175,1000000) and vacant_capacity < F(38387,1000000),
            'displayed rational comparison failed')
    require(F(47175-38387,1000000) > F(1,120), 'rational final threshold failed')
    require(gap > F(1,120), 'complete private-region gap not certified')
    fresh_threshold = (required+reserved_mass)/all_supported_mass
    require(F(41,40) < fresh_threshold < F(29,28), 'fresh-prime boundary changed')
    numbers = dict(common_digit_mass=digit_mass, required_after_one_mod9=required,
                   reserved_pool_reciprocal_mass=reserved_mass,
                   all_supported_reciprocal_mass=all_supported_mass,
                   vacant_capacity=vacant_capacity, strict_hole_lower=gap,
                   necessary_fresh_euler_threshold=fresh_threshold)
    return dict(success=True, nonzero_digit_tuples=sum(hist.values()),
                private_root_counts=roots, private_root_masks=dict(sorted(hist.items())),
                residual_demands_after_adaptive_selection_and_one_mod9=demand_count,
                reserved_normal_shapes=shapes, reserved_numerical_moduli=pool_count,
                original_height_range=[1,HEIGHT], descendant_height_bound=None,
                allowed_descendant_support=list(P0),
                exact={k:str(v) for k,v in numbers.items()},
                rational_brackets={k:bracket(v) for k,v in numbers.items()},
                certified_global_hole_lower='1/120',
                scope='One whole-AP-sound standard modulus9 image is allowed; all other descendants avoid every standard candidate modulus, selected or unselected. Each AP is bound to a fixed original source label. No general odd-cover or palette-reallocation exclusion.')


if __name__ == '__main__':
    print(json.dumps(result(), sort_keys=True, indent=2))
