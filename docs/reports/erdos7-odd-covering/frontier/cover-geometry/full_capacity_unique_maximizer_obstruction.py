#!/usr/bin/env python3
"""Exact arithmetic for an actual full-capacity hinge obstruction.

The inventory is given by a finite divisor rule, not enumerated. The proof
supplies entropy stability of its exact minimizer; no optimizer is run.
All query heights are retained by exact geometric tails.
"""
import argparse
import json
from fractions import Fraction as F
from hashlib import sha256
from math import gcd, prod
from pathlib import Path

PRIMES = (3, 5, 7, 11, 13, 17, 19)
RESIDUES = (2, 8, 14, 4, 7, 13, 11, 16, 17, 19, 22, 23,
            26, 28, 29, 31, 32, 34, 37, 38, 41, 43, 44)
DECISIVE = (3, 5, 9, 15, 45)


def encode(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, dict):
        return {str(k): encode(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [encode(v) for v in x]
    return x


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = ap.parse_args()
    checks = {}

    def require(name, condition):
        if not condition:
            raise ArithmeticError(name)
        checks[name] = True

    height = 64
    alpha = F(7235955529, 6075000000000)
    target = alpha * F(320713, 392000)
    euler = prod(F(p, p - 1) for p in PRIMES)
    kappa = prod(F(p - 1, p) for p in PRIMES if p not in (3, 5))
    untouched = kappa / 45
    loss = sum((F(1, 3**i) for i in range(1, 24)), F())
    mass = untouched * (24 - loss)
    require('all_nonpreferred_units', set(RESIDUES) ==
            {r for r in range(45) if gcd(r, 45) == 1 and r != 1})
    labels = [45 * 3**i for i in range(1, 24)]
    require('distinct_exceptional_numerical_labels', len(set(labels)) == 23)
    require('all_exceptional_labels_divide_period', all(prod(PRIMES)**height % d == 0 for d in labels))
    require('fixed_phases_are_valid_units', all(0 < r < d and gcd(r, d) == 1 for r, d in zip(RESIDUES, labels)))
    require('disjoint_exceptional_cylinders', all(
        (RESIDUES[i] - RESIDUES[j]) % gcd(labels[i], labels[j]) != 0
        for i in range(23) for j in range(i + 1, 23)))
    require('source_factor', kappa == F(207360, 323323))
    require('full_euler_factor', euler == F(323323, 110592) < 3)
    require('untouched_mass', untouched == F(4608, 323323))
    require('complete_cut_sum', loss == (1 - F(1, 3**23)) / 2)
    require('complete_survivor_mass', mass == F(2304, 323323) * (47 + F(1, 3**23)) > F(1, 3))
    gamma = untouched * F(1, 3**23) / mass
    require('uniform_phase_gap', gamma == F(2, 47 * 3**23 + 1) > F(1, 24 * 3**23))
    rows = []
    for g in DECISIVE:
        phi = sum(gcd(s, g) == 1 for s in range(g))
        unnormalized = []
        first = {}
        for s in range(g):
            hits = [i for i, r in enumerate(RESIDUES, 1) if r % g == s]
            first[s] = min(hits) if hits else None
            value = untouched * (F(24, phi) - sum((F(1, 3**i) for i in hits), F())) if gcd(s, g) == 1 else F()
            unnormalized.append(value)
        require(f'complete_cylinder_partition_{g}', sum(unnormalized, F()) == mass)
        gap = min((unnormalized[1] - unnormalized[s]) / mass for s in range(g) if s != 1)
        require(f'unique_maximum_{g}', gap >= gamma > 0)
        rows.append(dict(label=g,phi=phi,first_cut_by_residue=first,
                         complete_survivor_cylinder_masses=unnormalized,minimum_normalized_gap=gap))

    # Exact omitted-label reciprocal mass: complement of the FULL divisor box.
    tail = euler * (1 - prod(1 - F(1, p**(height+1)) for p in PRIMES))
    tail_bound = F(21, 3**65)
    entropy_bound = F(63, 3**65)
    delta_bound = F(1, 3**30)
    require('entire_unused_tail', 0 < tail < tail_bound)
    require('entropy_comparison', tail / mass < entropy_bound)
    require('Pinsker_radius', entropy_bound / 2 < delta_bound**2)
    require('maximizers_stable_under_entropy_perturbation', 2 * delta_bound < gamma)
    require('potential_normalizer', entropy_bound < F(1, 2) and mass / 2 > F(1, 6) > alpha)
    require('hinge_target_refuted', target < alpha < F(1, 800) < F(1, 100) < untouched)
    a = euler - 1
    coefficients = prod(F(height) + F(p, p-1) for p in PRIMES) - 1
    require('complete_gcd_coefficient_sum', coefficients < 66**7 < 3**28)
    rp_bound = 3*a + F(1, 9)
    require('same_minimizer_query_bound', delta_bound * coefficients < F(1, 9)
            and rp_bound == F(650481, 110592) < 6 < F(566, 49))
    # Only the hinge statement is asserted uniformly for K >= 64;
    # the displayed RP<6 estimate is for K=64.
    result = dict(schema='full-capacity-unique-maximizer-obstruction-v1',
        inventory=dict(primes=PRIMES,height=height,period=f'{prod(PRIMES)}^{height}',
            occupied_label_count=(height+1)**7-1,
            rule='Every nonunit divisor of the period is occupied; phase 0 except for the listed exceptional labels.',
            exceptional=[dict(label=d,phase=r) for d,r in zip(labels,RESIDUES)]),
        survivor=dict(kappa=kappa,haar_mass=mass,untouched_cylinder='W intersect [1] mod45',untouched_mass=untouched),
        maximizers=dict(decisive_labels=DECISIVE,preferred_phase=1,rows=rows,uniform_gap=gamma),
        entropy=dict(full_unused_reciprocal_tail=tail,tail_upper=tail_bound,
            relative_entropy_upper=entropy_bound,total_variation_upper=delta_bound,
            normalizer_strict_lower=F(1,6)),
        consequence=dict(hinge_lower=untouched,rejected_hinge_target=target,
            complete_gcd_coefficient_sum=coefficients,same_minimizer_query_upper=rp_bound,
            same_minimizer_query_strict_upper=6,
            scope='Actual redundant finite original family, full unused capacities, unique maximizing phases of the exact minimizer. Refutes the universal sufficient hinge bound, not Erdos7 or an irredundant-only/high-query-norm assertion.'),
        checks=checks,producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),new_lean_verification=False)
    args.output.write_text(json.dumps(encode(result),indent=2)+'\n')
    print(json.dumps(encode(dict(checks=len(checks),survivor_mass=mass,hinge_lower=untouched,
                               gap=gamma,same_minimizer_query_upper=rp_bound))))


if __name__ == '__main__':
    main()
