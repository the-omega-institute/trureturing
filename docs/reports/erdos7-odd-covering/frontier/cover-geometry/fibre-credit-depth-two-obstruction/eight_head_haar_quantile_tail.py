"""Exact upper-mass Haar comparison for an arbitrary eight-prime head.

The eight-prime survivor-density theorem and the all-prime analytic tail
are stated ordinary premises. This arithmetic does not replay either proof
or provide Lean verification. Infinite comparison moments remain exact.
"""
import argparse
from fractions import Fraction as F
import json
from math import factorial, prod
from pathlib import Path

PRIMES = (3, 5, 7, 11, 13, 17, 19, 23)
SOURCE_MASS = F(1, 1002375)
ATOM_LIMIT = 288


def need(condition, message):
    if not condition:
        raise ValueError(message)


def finite_atoms(limit):
    need(type(limit) is int and limit > 0, 'Positive integer comparison window')
    atoms = {1: F(1)}
    for p in PRIMES:
        weights = [F(0), F(p - 1, p)]
        for r in range(2, limit + 1):
            weights.append(weights[-1] / p)
        out = {}
        for n, weight in atoms.items():
            for r in range(1, limit // n + 1):
                out[n * r] = out.get(n * r, F(0)) + weight * weights[r]
        atoms = out
    return atoms


def upper_moments(atoms, mass):
    need(0 < mass <= 1, 'Positive target mass at most Haar mass')
    remaining = 1 - mass
    removed = {0: F(0), 4: F(0)}
    cutoff = None
    split = None
    for n in sorted(atoms):
        take = min(remaining, atoms[n])
        remaining -= take
        for k in (0, 4):
            removed[k] += n ** k * take
        if remaining == 0:
            cutoff, split = n, take
            break
    need(remaining == 0 and cutoff is not None, 'Stored atoms resolve the complete upper quantile')
    fourth = raw_fourth() - removed[4]
    tail_above = 1 - sum((w for n, w in atoms.items() if n <= cutoff), F(0))
    tail_at_least = tail_above + atoms[cutoff]
    need(tail_above <= mass <= tail_at_least, 'Cutoff brackets the prescribed upper mass')
    # An independent algebraic expression for the same thresholded cost.
    threshold_fourth = (cutoff ** 4 * mass + raw_fourth() - cutoff ** 4
                        + sum(((cutoff ** 4 - n ** 4) * w
                               for n, w in atoms.items() if n < cutoff), F(0)))
    need(fourth == threshold_fourth, 'Threshold-fourth and split-atom expressions agree')
    need(fourth >= cutoff ** 4 * mass, 'Upper submeasure has the declared minimum load')
    return {'mass': mass, 'cutoff': cutoff, 'removed_cutoff_mass': split,
            'cutoff_atom_mass': atoms[cutoff], 'tail_strictly_above_cutoff': tail_above,
            'tail_at_least_cutoff': tail_at_least, 'complete_fourth_moment': fourth}


def raw_fourth():
    return prod(F(p ** 4 + 11 * p ** 3 + 11 * p ** 2 + p, (p - 1) ** 4)
                for p in PRIMES)


def tail_allowance(cutoff, ell):
    need(type(cutoff) is int and type(ell) is int and cutoff >= 286
         and ell >= 4 and 3 ** ell <= cutoff and 4 * ell >= 25,
         'Inherited analytic quartic tail domain')
    # Report734: k=4, delta=2/5, growth exponent25.
    return (F(5625, 2048 * 3) * F(2 * ell * ell + 1, 2 * ell * ell - 1) ** 25
            * F(cutoff, (cutoff - 1) ** 4)
            * sum((F(factorial(25), factorial(25 - j) * (3 * ell) ** j)
                   for j in range(26)), F(0)))


def calculate():
    atoms = finite_atoms(ATOM_LIMIT)
    upper = upper_moments(atoms, SOURCE_MASS)
    need(upper['cutoff'] == 288, 'Declared exact upper-mass cutoff')
    bound = F(44100)
    need(0 < upper['complete_fourth_moment'] < bound, 'Same-law fourth moment below44100')
    need(raw_fourth() == F(16379878645983125, 190768545792), 'Inherited complete Haar fourth moment')
    # Explicit coefficient dominance for1+(5/3)A4(t) <= (1+t)^25.
    growth = [F(1), F(25), F(250, 3), F(100), F(40)]
    need(all(growth[j] <= F(factorial(25), factorial(j) * factorial(25 - j))
             for j in range(5)), 'Complete quartic growth-polynomial domination')
    cutoff, ell = 8000, 8
    tau = tail_allowance(cutoff, ell)
    loss = bound * tau
    margin = SOURCE_MASS - loss
    need(margin > F(1, 20000000), 'General eight-prime head with unrestricted larger tail')
    exact_margin = SOURCE_MASS - upper['complete_fourth_moment'] * tau
    need(exact_margin > margin, 'Rounded-up fourth-moment bound is conservative')
    return {
        'scope': 'Finite pairwise-distinct odd numerical moduli>1. At most8 support primes<=8000; '
                 'arbitrary finite larger support, all finite heights and fixed phases. '
                 'No missing-small-prime or phase-dictionary condition.',
        'source_premise': 'Schroeder edition1.0.1 cor:uncovered-density, attributed via Report734: '
                          'eight-prime uncovered Haar density>=1/1002375. Not replayed here.',
        'reference_primes': list(PRIMES), 'source_mass': SOURCE_MASS,
        'atom_limit': ATOM_LIMIT, 'reconstructed_atom_count': len(atoms),
        'comparison_total_mass': F(1), 'comparison_complete_fourth_moment': raw_fourth(),
        'upper_mass_comparison': upper, 'safe_fourth_moment_bound': bound,
        'tail': {'cutoff': cutoff, 'ell': ell, 'moment_order': 4, 'delta': F(2, 5),
                 'growth_exponent': 25, 'loss_coefficient': F(5625, 2048),
                 'complete_allowance': tau, 'loss_upper': loss,
                 'final_distorted_mass_lower': margin, 'strict_simple_lower': F(1, 20000000),
                 'exact_fourth_final_margin': exact_margin},
        'infinite_auxiliary_moments_retained': True,
        'source_density_theorem_reexecuted': False,
        'analytic_prime_product_theorem_reexecuted': False,
        'lean_verification': False,
    }


def self_test():
    atoms = finite_atoms(ATOM_LIMIT)
    cases = [
        ('zero mass', lambda: upper_moments(atoms, F(0))),
        ('mass above available Haar', lambda: upper_moments(atoms, F(2))),
        ('unresolved cutoff', lambda: upper_moments({n: w for n, w in atoms.items() if n < 288}, SOURCE_MASS)),
        ('invalid atom limit', lambda: finite_atoms(0)),
        ('invalid analytic ell', lambda: tail_allowance(8000, 9)),
    ]
    rejected = []
    for name, function in cases:
        try:
            function()
        except ValueError:
            rejected.append(name)
        else:
            raise ValueError('Invalid computation accepted: ' + name)
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
        args.write_result.write_text(json.dumps(result, separators=(',', ':')) + '\n')
    else:
        need(result == json.loads(Path(__file__).with_suffix('.json').read_text()),
             'Retained result equals exact recomputation')
    print(json.dumps({'head_size': 8, 'cutoff': result['tail']['cutoff'],
                      'strict_final_distorted_mass_lower': result['tail']['strict_simple_lower'],
                      'fourth_moment_bound': result['safe_fourth_moment_bound'], 'lean_verification': False}, indent=2))


if __name__ == '__main__':
    main()
