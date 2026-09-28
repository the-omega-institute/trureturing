#!/usr/bin/env python3
"""Independent finite audit; standard library, not a Lean/kernel certificate."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd, lcm, prod
from pathlib import Path
import argparse
import hashlib
import json


def exp_bounds(x, terms=24):
    x = F(x)
    term = F(1)
    lower = term
    for k in range(1, terms + 1):
        term *= x / k
        lower += term
    first_omitted = term * x / (terms + 1)
    assert 0 <= x < terms + 2
    upper = lower + first_omitted / (1 - x / (terms + 2))
    return lower, upper


def reduced_log_bounds(x, terms=24):
    x = F(x)
    assert 1 <= x <= 2
    t = (x - 1) / (x + 1)
    lower = 2 * sum((t ** (2*k + 1) / (2*k + 1)
                     for k in range(terms)), F(0))
    upper = lower + 2*t**(2*terms+1)/((2*terms+1)*(1-t*t))
    return lower, upper


def log_bounds(x):
    x = F(x)
    assert x >= 1
    k = 0
    while x >= 2:
        x /= 2
        k += 1
    a, b = reduced_log_bounds(x)
    a2, b2 = reduced_log_bounds(2)
    return a + k*a2, b + k*b2


def sigma_sieve(limit):
    sig = [0] * (limit + 1)
    for d in range(1, limit + 1):
        for n in range(d, limit + 1, d):
            sig[n] += d
    return sig


def geometric(p, a):
    return sum((F(1, p**j) for j in range(a+1)), F(0))


def common_residue_checks():
    tuple_checks = 0
    cases = 0
    for mods in product(range(2, 9), repeat=3):
        L = lcm(*mods)
        raw_image = {tuple(x % m for m in mods) for x in range(L)}
        for ys in product(*(range(m) for m in mods)):
            compatible = all((ys[i]-ys[j]) % gcd(mods[i], mods[j]) == 0
                             for i, j in combinations(range(3), 2))
            assert (ys in raw_image) == compatible
            tuple_checks += 1
        for N in range(0, 17):
            counts = Counter(tuple(N*x % m for m in mods) for x in range(L))
            d = gcd(N, L)
            assert len(counts) == L // d
            assert set(counts.values()) == {d}
            effective = tuple(m // gcd(N, m) for m in mods)
            assert lcm(*effective) == L // d
            permitted = {ys for ys in raw_image
                         if all(y % gcd(N,m) == 0 for y,m in zip(ys,mods))}
            assert set(counts) == permitted
            for i, j in combinations(range(3), 2):
                mi, mj = mods[i], mods[j]
                pair_image = {(ys[i], ys[j]) for ys in counts}
                size_i = mi // gcd(N, mi)
                size_j = mj // gcd(N, mj)
                mi_factor = F(size_i * size_j, len(pair_image))
                assert mi_factor == gcd(effective[i], effective[j])
                assert mi_factor == F(gcd(mi,mj), gcd(N,gcd(mi,mj)))
            cases += 1
    example = Counter((14*x % 8, 14*x % 12) for x in range(24))
    assert len(example) == 12 and set(example.values()) == {2}
    assert (1,1) not in example and (1-1) % gcd(8,12) == 0
    independent = {(2*x % 6, 2*x % 10) for x in range(30)}
    assert len(independent) == 15
    assert independent == set(product(range(0,6,2), range(0,10,2)))
    return {'modulus_triples': 343, 'raw_tuple_checks': tuple_checks,
            'multiplication_cases': cases, 'N14_m8_m12_image': sorted(example),
            'N14_m8_m12_multiplicity': 2, 'N14_m8_m12_MI': 'log(2)',
            'N2_m6_m10_independent_image_size': len(independent)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    sig = sigma_sieve(46188)
    eligible = [r for r in range(1,46189) if gcd(r,210) == 1]
    largest = max(F(sig[r],r) for r in eligible)
    maximizers = [r for r in eligible if F(sig[r],r) == largest]
    smaller = [r for r in eligible if r <= 4181]
    smaller_largest = max(F(sig[r],r) for r in smaller)
    smaller_maximizers = [r for r in smaller if F(sig[r],r) == smaller_largest]
    assert largest == F(33516,26741) and maximizers == [26741]
    assert smaller_largest == F(3024,2431) and smaller_maximizers == [2431]
    patterns = [(2,1,1),(1,2,1),(1,1,2)]
    pattern_bounds = [prod(geometric(p,a) for p,a in zip((11,13,17),pat))
                      for pat in patterns]
    assert max(pattern_bounds) == largest
    assert F(143,120) < largest
    assert 11**5 > 46189
    assert 11*13*17*19 == 46189
    core = F(sig[5040],5040)
    assert core == F(403,105)
    original = core * F(11,10)*F(13,12)*F(17,16)
    strong = core * largest
    assert original == F(979693,201600)
    assert strong == F(49476,10285)
    assert 3329*5040 > 2**24
    assert 833*5040 > 2**22
    assert log_bounds(2)[0] > F(69,100)
    assert exp_bounds(F(14,5))[1] < F(33,2) < 24*F(69,100)
    assert exp_bounds(F(271,100))[1] < F(151,10) < 22*F(69,100)
    # H_1000 - log(1001) < gamma is the classical elementary lower sequence.
    harmonic = sum((F(1,k) for k in range(1,1001)),F(0))
    gamma_lower = harmonic - log_bounds(1001)[1]
    assert gamma_lower > F(5767,10000)
    assert exp_bounds(F(5767,10000))[0] > F(89,50)
    original_margin = F(89,50)*F(14,5)-original
    strong_margin = F(89,50)*F(14,5)-strong
    lower_endpoint_margin = F(89,50)*F(271,100)-strong
    assert original_margin == F(125407,1008000)
    assert strong_margin == F(44611,257125)
    assert lower_endpoint_margin > 0
    out = {
        'eligible_R_count_1_through_46188': len(eligible),
        'eligible_R_count_3329_through_46188': sum(r>=3329 for r in eligible),
        'exact_max_sigma_R_over_R': str(largest), 'maximizers': maximizers,
        'exact_max_R_le_4181': str(smaller_largest),
        'maximizers_R_le_4181': smaller_maximizers,
        'exponent_pattern_bounds': dict(zip(map(str,patterns),map(str,pattern_bounds))),
        'original_Z_bound': str(original), 'strong_Z_bound': str(strong),
        'original_margin': str(original_margin), 'strong_margin': str(strong_margin),
        'family_833_le_R_lt_46189_margin': str(lower_endpoint_margin),
        'analytic_rational_checks': 'all passed using series bounds',
        'gamma_lower_bound': 'H_1000 - log(1001) > 5767/10000',
        'common_residues': common_residue_checks(),
        'status': 'passed; independent Python finite audit, no Lean claim',
        'script_path': Path(__file__).name,
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'limitations': ['Exact finite enumeration and rational series checks; not a Lean theorem.',
                        'Entropy equalities require a uniform common source; support checks do not certify arbitrary source laws.']
    }
    (args.out/'results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))


if __name__ == '__main__':
    main()
