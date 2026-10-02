"""Exact, fixed-schedule common-source comparison at primes 43 and 47.

Only Python's standard library is used. No author results or old producer
are imported. Low atoms are stored through 96; moments retain the full
infinite auxiliary tails. This is arithmetic, not Lean verification.
"""

import argparse
from fractions import Fraction as F
import json
from math import factorial, prod
from pathlib import Path


LIMIT = 96
PRIMES = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
D0 = F(1816999451688960000, 36518862868606981)
CHECKS = 0


def require(condition, message):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise ArithmeticError(message)


def cap_atom(q, cap, value):
    if value == 1:
        return 1 - cap / q
    return cap * F(q - 1, q ** value)


def append_coordinate(atoms, q, cap):
    """Exact atoms of z*(1+J) through LIMIT, using positive integer factors."""
    require(0 <= cap <= q, 'capped comparison probability domain')
    out = [F(0) for _ in range(LIMIT + 1)]
    for z in range(1, LIMIT + 1):
        if not atoms[z]:
            continue
        for value in range(1, LIMIT // z + 1):
            out[z * value] += atoms[z] * cap_atom(q, cap, value)
    require(all(x >= 0 for x in out), 'convolution atoms nonnegative')
    return out


def snapshot(mass, first, second, atoms):
    low = [sum((z ** k * atoms[z] for z in range(1, LIMIT + 1)), F(0))
           for k in range(3)]
    tails = [mass - low[0], first - low[1], second - low[2]]
    require(all(t >= 0 for t in tails), 'complete tail moments nonnegative')
    require(tails[1] >= (LIMIT + 1) * tails[0], 'tail first moment support')
    require(tails[2] >= (LIMIT + 1) * tails[1], 'tail second moment support')
    return {
        'mass': str(mass), 'first': str(first), 'second': str(second),
        'mean': str(first / mass), 'normalized_second': str(second / mass),
        'low_atoms': {str(z): str(atoms[z]) for z in range(1, LIMIT + 1)
                      if atoms[z]},
        'tail_mass_above_limit': str(tails[0]),
        'tail_first_above_limit': str(tails[1]),
        'tail_second_above_limit': str(tails[2]),
    }


def upper_mass_trim(mass, first, second, atoms, target):
    require(0 < target <= mass, 'positive legal target mass')
    remaining = mass - target
    removed_first = F(0)
    removed_second = F(0)
    result = atoms[:]
    cutoff = 0
    for z in range(1, LIMIT + 1):
        removed = min(remaining, result[z])
        result[z] -= removed
        remaining -= removed
        removed_first += z * removed
        removed_second += z * z * removed
        if remaining == 0:
            cutoff = z
            break
    require(remaining == 0, 'trim resolved within retained exact atom inventory')
    require(all(x >= 0 for x in result), 'trimmed atoms nonnegative')
    # The atom at cutoff is split; all strictly smaller atoms were removed.
    require(all(result[z] == 0 for z in range(1, cutoff)), 'upper-mass support')
    certificate = {
        'cutoff': cutoff, 'removed_mass': str(mass - target),
        'removed_first': str(removed_first),
        'removed_second': str(removed_second),
        'retained_cutoff_atom': str(result[cutoff]),
    }
    return first - removed_first, second - removed_second, result, certificate


def main(output):
    atoms = [F(0) for _ in range(LIMIT + 1)]
    atoms[1] = F(1)
    for p in PRIMES:
        atoms = append_coordinate(atoms, p, F(1))
    full_first = prod(F(p, p - 1) for p in PRIMES)
    full_second = prod(F(p * (p + 1), (p - 1) ** 2) for p in PRIMES)
    require(full_second == F(17517439415203, 525533184000),
            'full twelve-prime Haar second moment')
    require(D0 < 50, 'source density cap below fifty')
    full = snapshot(F(1), full_first, full_second, atoms)
    mass = 1 / D0
    require(mass > F(1, 50), 'initial source mass exceeds one over fifty')
    first, second, atoms, initial_trim = upper_mass_trim(
        F(1), full_first, full_second, atoms, mass)
    require(initial_trim['cutoff'] == 16, 'initial common-mass cutoff')
    initial = snapshot(mass, first, second, atoms)
    stages = []
    for q, expected_cutoff in ((43, 18), (47, 24)):
        before = snapshot(mass, first, second, atoms)
        threshold = F(q - 1, 2)
        require(threshold <= LIMIT, 'stop-loss threshold resolved exactly')
        low_correction = sum(((threshold - z) * atoms[z]
                              for z in range(1, LIMIT + 1) if z < threshold), F(0))
        stop_loss = first - threshold * mass + low_correction
        require(stop_loss >= 0, 'stop-loss nonnegative')
        charge = stop_loss / threshold
        charge_bound = F(617 if q == 43 else 569, 100000)
        require(charge < charge_bound, 'short rational stage charge certificate')
        new_mass = mass - charge
        require(new_mass > 0, 'positive common live mass')
        appended_atoms = append_coordinate(atoms, q, F(2))
        appended_first = first * (1 + F(2, q - 1))
        appended_second = second * (1 + F(2 * (3 * q - 1), (q - 1) ** 2))
        appended = snapshot(mass, appended_first, appended_second, appended_atoms)
        first, second, atoms, trim = upper_mass_trim(
            mass, appended_first, appended_second, appended_atoms, new_mass)
        require(trim['cutoff'] == expected_cutoff, 'fixed-schedule upper-mass cutoff')
        mass = new_mass
        after = snapshot(mass, first, second, atoms)
        stages.append({
            'prime': q, 'delta': '1/2', 'conditional_cap': '2',
            'threshold': str(threshold), 'before': before,
            'low_correction': str(low_correction), 'stop_loss': str(stop_loss),
            'deletion_charge': str(charge), 'appended': appended,
            'trim': trim, 'after': after,
        })
    require(mass > F(1, 125), 'two-prime live mass exceeds one over 125')
    require(second < F(96, 5), 'same-source complete second moment below 96/5')
    require(first < 41 * mass, 'same-source query mean below 41')
    require(F(4) / mass < 500, 'normalized full-Haar density below 500')
    require(mass / 4 > F(1, 500), 'actual core Haar survivor exceeds one over 500')
    b, ell = 10000, 8
    require(b >= 286 and ell >= 4 and 3 ** ell <= b, 'fixed analytic tail domain')
    polynomial = sum((F(factorial(7), factorial(7 - j) * ell ** j)
                      for j in range(8)), F(0))
    allowance = F(129, 127) ** 7 / b * F(b, b - 3) ** 2 * polynomial
    coarse_reserve = F(1, 125) - F(96, 5) * allowance
    require(coarse_reserve > F(1, 1000), 'inherited fixed-tail reserve')
    require(mass - second * allowance > coarse_reserve, 'exact reserve dominates coarse')
    data = {
        'scope': 'FC159 restricted old core, then arbitrary 43/47-touching originals',
        'evidence': 'ordinary source/comparison premises and exact arithmetic; no Lean claim',
        'primes': PRIMES, 'D0': str(D0), 'atom_limit': LIMIT,
        'complete_Haar_comparison': full,
        'initial_trim': initial_trim, 'initial': initial, 'stages': stages,
        'final_density_cap_unnormalized': '4',
        'final_normalized_density_cap': str(4 / mass),
        'actual_Haar_survivor_lower': str(mass / 4),
        'fixed_tail_conditional_on_SH11': {
            'B': b, 'ell': ell, 'tau7': str(allowance),
            'exact_reserve': str(mass - second * allowance),
            'coarse_reserve': str(coarse_reserve),
            'coarse_mass_lower': '1/125', 'coarse_second_upper': '96/5',
        },
        'exact_checks': CHECKS,
    }
    output.write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps({'exact_checks': CHECKS, 'output': str(output),
                      'cutoffs': [16, 18, 24], 'final_mass': float(mass),
                      'final_second': float(second),
                      'coarse_tail_reserve_gt_1_over_1000': True}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    main(args.output)
