"""Exact arithmetic for one Schroeder source's full capped query profile.

Schroeder edition 1.0.1 supplies one physical survivor source, its initial
pure-anchor restrictions, six full conditional caps, and mass >=1/33750.
The source proof and analytic prime-product bound are attributed premises;
this consumer certifies rational consequences, not those proofs or Lean.
"""
import argparse
from fractions import Fraction as F
import json
from math import factorial, prod
from pathlib import Path

FACTORS = ((3, F(1, 2), F(1)), (5, F(3, 4), F(1)),
           (7, F(1), F(3, 2)), (11, F(1), F(5, 3)),
           (13, F(1), F(3, 2)), (17, F(1), F(2)),
           (19, F(1), F(9, 5)), (23, F(1), F(11, 5)))
SOURCE_MASS = F(1, 33750)
ATOM_LIMIT = 192


def need(condition, message):
    if not condition:
        raise ValueError(message)


def validate_factors(factors):
    need(len(factors) > 0, 'Nonempty factor list')
    for p, mass, cap in factors:
        need(type(p) is int and p > 1 and 0 < cap <= p
             and cap / p <= mass <= 1,
             'Nonnegative finite comparison factor and zero atom')


def total_mass(factors=FACTORS):
    validate_factors(factors)
    return prod(mass for p, mass, cap in factors)


def full_fourth(factors=FACTORS):
    validate_factors(factors)
    closed = prod(mass + cap * (F(p**4 + 11*p**3 + 11*p*p + p, (p-1)**4) - 1)
                  for p, mass, cap in factors)
    increments = prod(mass + cap * (15*F(1, p-1) + 50*F(1, (p-1)**2)
                                   + 60*F(1, (p-1)**3) + 24*F(1, (p-1)**4))
                      for p, mass, cap in factors)
    need(closed == increments, 'Closed geometric and tail-increment fourth moments agree')
    return closed


def finite_atoms(limit, factors=FACTORS):
    need(type(limit) is int and limit > 0, 'Positive integer comparison window')
    validate_factors(factors)
    atoms = {1: F(1)}
    for p, mass, cap in factors:
        weights = [F(0), mass-cap/p]
        weights.extend(cap*F(p-1, p**r) for r in range(2, limit+1))
        out = {}
        for n, weight in atoms.items():
            for r in range(1, limit//n+1):
                out[n*r] = out.get(n*r, F(0)) + weight*weights[r]
        atoms = out
    return atoms


def upper_fourth(atoms, mass, factors=FACTORS):
    available = total_mass(factors)
    need(0 < mass <= available, 'Positive target mass within available comparison mass')
    need(all(type(n) is int and n >= 1 and value >= 0 for n, value in atoms.items()),
         'Nonnegative integer-load atoms')
    need(sum(atoms.values(), F(0)) <= available, 'Finite atoms do not exceed complete mass')
    left = available - mass
    removed_fourth = F(0)
    cutoff = None
    removed_cutoff = None
    for n, value in sorted(atoms.items()):
        take = min(left, value)
        left -= take
        removed_fourth += n**4*take
        if left == 0:
            cutoff, removed_cutoff = n, take
            break
    need(left == 0 and cutoff is not None, 'Finite comparison window resolves upper quantile')
    fourth = full_fourth(factors)-removed_fourth
    threshold = (full_fourth(factors) + cutoff**4*(mass-available)
                 + sum(((cutoff**4-n**4)*value
                        for n, value in atoms.items() if n < cutoff), F(0)))
    above = available-sum((value for n, value in atoms.items() if n <= cutoff), F(0))
    at_least = above+atoms[cutoff]
    need(above <= mass <= at_least, 'Exact upper-mass cutoff bracket')
    need(fourth == threshold, 'Split-atom and threshold-fourth formulas agree')
    need(fourth >= mass*cutoff**4, 'Upper comparison retains the declared minimum load')
    return {'mass': mass, 'cutoff': cutoff, 'removed_cutoff_mass': removed_cutoff,
            'cutoff_atom_mass': atoms[cutoff], 'tail_strictly_above_cutoff': above,
            'tail_at_least_cutoff': at_least, 'complete_fourth_moment': fourth}


def tail_allowance(bound, ell):
    need(type(bound) is int and type(ell) is int and bound >= 286 and ell >= 4
         and 3**ell <= bound and 4*ell >= 25,
         'Inherited analytic quartic tail domain')
    return (F(5625, 6144)*F(2*ell*ell+1, 2*ell*ell-1)**25
            * F(bound, (bound-1)**4)
            * sum((F(factorial(25), factorial(25-j)*(3*ell)**j)
                   for j in range(26)), F(0)))


def calculate():
    atoms = finite_atoms(ATOM_LIMIT)
    upper = upper_fourth(atoms, SOURCE_MASS)
    need(total_mass() == F(3, 8), 'Two actual pure-anchor comparison factors')
    need(full_fourth() == F(1284839019649471672399, 1788455116800000),
         'Declared complete source fourth moment')
    need(upper['cutoff'] == 192, 'Declared upper-mass cutoff')
    bound = F(590500)
    need(0 < upper['complete_fourth_moment'] < bound,
         'One source serves all complete fourth queries below590500')
    coefficients = (F(1), F(25), F(250, 3), F(100), F(40))
    need(all(coefficients[j] <= F(factorial(25), factorial(j)*factorial(25-j))
             for j in range(5)), 'Quartic growth coefficientwise dominated by(1+t)^25')
    cutoff, ell = 6561, 8
    allowance = tail_allowance(cutoff, ell)
    margin = SOURCE_MASS-bound*allowance
    exact_margin = SOURCE_MASS-upper['complete_fourth_moment']*allowance
    need(exact_margin > margin > F(1, 150000),
         'Strict positive reserve for every finite prime tail above6561')
    return {
        'scope': 'Finite pairwise-distinct odd numerical moduli>1, one original fixed phase per '
                 'modulus, at most8 support primes<=6561, arbitrary finite larger support and '
                 'all original finite heights. No missing-prime or prescribed dictionary condition.',
        'source_premise': 'Schroeder edition1.0.1 actual construction: nu mass>=1/33750, '
                          'initial H|A with A inside P3^c times P5^c, pure masses1/2 and3/4, '
                          'same normalized full conditional kernels with stated six caps, '
                          'kernels defined also on deleted histories. Not replayed here.',
        'reference_factors': [{'prime': p, 'mass': mass, 'cap': cap} for p, mass, cap in FACTORS],
        'source_mass': SOURCE_MASS, 'comparison_total_mass': total_mass(),
        'comparison_complete_fourth_moment': full_fourth(),
        'atom_limit': ATOM_LIMIT, 'reconstructed_atom_count': len(atoms),
        'upper_mass_comparison': upper, 'safe_fourth_moment_bound': bound,
        'tail': {'cutoff': cutoff, 'ell': ell, 'moment_order': 4, 'delta': F(2, 5),
                 'growth_exponent': 25, 'loss_coefficient': F(5625, 2048),
                 'complete_allowance': allowance, 'loss_upper': bound*allowance,
                 'final_distorted_mass_lower': margin, 'strict_simple_lower': F(1, 150000),
                 'exact_fourth_final_margin': exact_margin},
        'infinite_auxiliary_moments_retained': True,
        'source_geometry_theorem_reexecuted': False,
        'analytic_prime_product_theorem_reexecuted': False,
        'lean_verification': False,
    }


def self_test():
    atoms = finite_atoms(ATOM_LIMIT)
    cases = [
        ('zero target mass', lambda: upper_fourth(atoms, F(0))),
        ('target above comparison mass', lambda: upper_fourth(atoms, F(1, 2))),
        ('unresolved cutoff', lambda: upper_fourth({n: v for n, v in atoms.items() if n < 192}, SOURCE_MASS)),
        ('negative atom', lambda: upper_fourth({1: F(-1)}, SOURCE_MASS)),
        ('invalid factor zero atom', lambda: finite_atoms(10, ((3, F(1, 5), F(1)),))),
        ('invalid atom limit', lambda: finite_atoms(0)),
        ('analytic ell above domain', lambda: tail_allowance(6561, 9)),
        ('analytic ell below growth domain', lambda: tail_allowance(6561, 6)),
    ]
    rejected = []
    for name, function in cases:
        try:
            function()
        except ValueError:
            rejected.append(name)
        else:
            raise ValueError('Invalid computation accepted: '+name)
    return rejected


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--write-result', type=Path)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate(), default=str))
    if args.self_test:
        print(json.dumps({'invalid_computations_rejected': self_test()}))
    if args.write_result:
        args.write_result.write_text(json.dumps(result, separators=(',', ':'))+'\n')
    else:
        need(result == json.loads(Path(__file__).with_suffix('.json').read_text()),
             'Retained result equals exact recomputation')
    print(json.dumps({'cutoff': result['tail']['cutoff'], 'source_mass': result['source_mass'],
                      'fourth_moment_bound': result['safe_fourth_moment_bound'],
                      'strict_final_distorted_mass_lower': result['tail']['strict_simple_lower'],
                      'lean_verification': False}, indent=2))


if __name__ == '__main__':
    main()
