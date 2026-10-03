"""Same-source ninth-prime271 bridge followed by an arbitrary large tail.

Reuse and freshly check the779 arithmetic and retained result. The source-construction and analytic-tail
proofs are explicit premises. Every comparison moment includes its infinite
geometric tail. Large exact intermediate fractions are consumed in memory;
retained rational intervals are outward bounds verified against those values.
"""
import argparse
from fractions import Fraction as F
import json
from math import prod
from pathlib import Path
import runpy

LIMIT = 640
M8 = F(1, 33750)
M9 = F(1, 2500000)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def load_base(path):
    base = runpy.run_path(str(path))
    verify_base_interface(base)
    fresh = json.loads(json.dumps(base['calculate'](), default=str))
    need(fresh == json.loads(path.with_suffix('.json').read_text()),
         'Fresh779 calculation matches its retained data result')
    return base


def verify_base_interface(base):
    expected = ((3, F(1, 2), F(1)), (5, F(3, 4), F(1)),
                (7, F(1), F(3, 2)), (11, F(1), F(5, 3)),
                (13, F(1), F(3, 2)), (17, F(1), F(2)),
                (19, F(1), F(9, 5)), (23, F(1), F(11, 5)))
    need(base['FACTORS'] == expected, 'Declared actual anchor and conditional-cap factors')
    need(base['SOURCE_MASS'] == M8, 'Same guaranteed eight-prime source mass')


def interval(value, scale=10**15):
    need(type(scale) is int and scale > 0, 'Positive interval denominator')
    low = F((value*scale).numerator//(value*scale).denominator, scale)
    high = low+F(1, scale)
    need(low <= value < high, 'Outward rational interval encloses exact value')
    return {'lower_inclusive': str(low), 'upper_exclusive': str(high)}


def factor_moment(p, mass, cap, order):
    t = F(1, p-1)
    polynomials = {1: t, 2: 3*t+2*t*t, 4: 15*t+50*t*t+60*t**3+24*t**4}
    need(order in polynomials, 'Declared complete moment order')
    return mass+cap*polynomials[order]


def trim(atoms, mass, moments, target):
    need(0 < target <= mass, 'Positive prescribed mass within comparison mass')
    need(all(type(n) is int and n >= 1 and v >= 0 for n, v in atoms.items()),
         'Nonnegative atoms on integer loads')
    need(sum(atoms.values(), F(0)) <= mass, 'Stored atoms respect total comparison mass')
    left = mass-target
    out = {}
    removed = {k: F(0) for k in moments}
    cutoff = None
    for n, value in sorted(atoms.items()):
        take = min(left, value)
        left -= take
        out[n] = value-take
        for k in moments:
            removed[k] += n**k*take
        if cutoff is None and left == 0:
            cutoff = n
    need(left == 0 and cutoff is not None, 'Stored low atoms resolve complete upper quantile')
    final = {k: moments[k]-removed[k] for k in moments}
    above = mass-sum((v for n, v in atoms.items() if n <= cutoff), F(0))
    at_least = above+atoms[cutoff]
    need(above <= target <= at_least, 'Upper-mass cutoff brackets exact prescribed mass')
    for k in moments:
        alternate = (moments[k]+cutoff**k*(target-mass)
                     + sum(((cutoff**k-n**k)*v for n, v in atoms.items() if n < cutoff), F(0)))
        need(final[k] == alternate, 'Threshold and split-atom complete moments agree')
        need(final[k] >= target*cutoff**k, 'Retained mass has declared minimum load')
    return out, final, {'cutoff': cutoff, 'tail_strictly_above': interval(above),
                        'tail_at_least': interval(at_least)}


def stoploss(atoms, mass, first, threshold):
    need(0 <= threshold <= LIMIT, 'Stop-loss threshold resolved by stored atoms')
    return first-threshold*mass+sum(((threshold-n)*v for n, v in atoms.items() if n < threshold), F(0))


def append_cap(atoms, moments, prime, cap):
    need(type(prime) is int and prime > 1 and 0 < cap <= prime,
         'Normalized nonnegative conditional comparison factor')
    weights = [F(0), 1-cap/prime]
    weights.extend(cap*F(prime-1, prime**r) for r in range(2, LIMIT+1))
    out = {}
    for n, value in atoms.items():
        if value:
            for r in range(1, LIMIT//n+1):
                out[n*r] = out.get(n*r, F(0))+value*weights[r]
    return out, {k: v*factor_moment(prime, F(1), cap, k) for k, v in moments.items()}


def calculate(base):
    verify_base_interface(base)
    factors = base['FACTORS']
    raw = {k: prod(factor_moment(p, a, c, k) for p, a, c in factors) for k in (1, 2, 4)}
    need(raw[4] == base['full_fourth'](), '779 complete fourth moment is reused exactly')
    initial_atoms = base['finite_atoms'](LIMIT)
    a8, moments8, cut8 = trim(initial_atoms, F(3, 8), raw, M8)
    need(cut8['cutoff'] == 192, 'Inherited eight-head upper-mass cutoff')
    mean8 = moments8[1]/M8
    need(268 < mean8 < 270, 'Same-comparator prime269 fails and prime271 passes the mean gate')
    q, delta, cap = 271, F(32, 45), F(45, 13)
    threshold = delta*(q-1)
    need(threshold == 192 and cap == 1/(1-delta) and cap <= q,
         'Legal271 normalized clipping kernel')
    hinge = stoploss(a8, M8, moments8[1], threshold)
    need(hinge == moments8[1]-192*M8, 'Cutoff192 stop loss has no lower-load contribution')
    loss = hinge/((1-delta)*(q-1))
    actual_lower = M8-loss
    need(actual_lower > M9, 'One actual restricted source can be scaled to the common ninth mass')
    a_product, moments_product = append_cap(a8, moments8, q, cap)
    a9, moments9, cut9 = trim(a_product, M8, moments_product, M9)
    need(cut9['cutoff'] == 640, 'Ninth-head upper-mass cutoff')
    bound = F(450000)
    need(0 < moments9[4] < bound, 'One ninth source bounds every fourth query below450000')
    tail_cutoff, ell = 20000, 9
    allowance = base['tail_allowance'](tail_cutoff, ell)
    margin = M9-bound*allowance
    need(margin > F(1, 50000000), 'Positive source through every finite tail above20000')
    return {
        'scope': 'Finite distinct odd numerical moduli>1 with fixed original phases and all finite heights; '
                 'at most8 original support primes<271 and at most9 support primes<=20000; '
                 'arbitrary finite support above20000. No missing-small-prime or phase-dictionary condition.',
        'premises': ['779 actual eight-prime source and simultaneous full-query comparison',
                     '771 normalized clipping and complete-label Jensen continuation',
                     '773 repeated common-mass selection and upper-quantile comparison',
                     '734 complete quartic continuation and analytic prime-product bound'],
        'source_arithmetic_and_retained_data_freshly_checked': True,
        'atom_limit': LIMIT, 'reconstructed_initial_atom_count': len(initial_atoms),
        'initial_comparison_mass': F(3, 8), 'initial_source_mass': M8,
        'initial_upper_cutoff': cut8,
        'initial_complete_moments': {str(k): interval(v) for k, v in moments8.items()},
        'initial_normalized_mean': interval(mean8),
        'ninth': {'reference_prime': q, 'delta': delta, 'cap': cap, 'threshold': threshold,
                  'stop_loss': interval(hinge), 'loss_upper': interval(loss),
                  'actual_survivor_mass_lower': interval(actual_lower), 'prescribed_mass': M9,
                  'untrimmed_complete_fourth': interval(moments_product[4]),
                  'upper_cutoff': cut9,
                  'complete_moments': {str(k): interval(v) for k, v in moments9.items()},
                  'safe_fourth_bound': bound},
        'tail': {'cutoff': tail_cutoff, 'ell': ell, 'delta': F(2, 5), 'growth_exponent': 25,
                 'complete_allowance': allowance, 'loss_upper': bound*allowance,
                 'final_distorted_mass_lower': margin, 'strict_simple_lower': F(1, 50000000)},
        'all_infinite_auxiliary_moments_retained': True,
        'large_intermediate_fractions_consumed_exactly': True,
        'retained_intervals_have_outward_rational_endpoints': True,
        'source_geometry_theorem_reexecuted': False,
        'analytic_prime_product_theorem_reexecuted': False,
        'lean_verification': False,
    }


def self_test(base, source):
    cases = [
        ('wrong source factors', lambda: verify_base_interface(dict(base, FACTORS=()))),
        ('wrong source mass', lambda: verify_base_interface(dict(base, SOURCE_MASS=F(1)))),
        ('zero target mass', lambda: trim({1:F(1)}, F(1), {1:F(1)}, F(0))),
        ('target larger than available', lambda: trim({1:F(1)}, F(1), {1:F(1)}, F(2))),
        ('unresolved quantile', lambda: trim({1:F(1,4)}, F(1), {1:F(2)}, F(1,4))),
        ('negative atom', lambda: trim({1:F(-1)}, F(1), {1:F(1)}, F(1,2))),
        ('cap above prime', lambda: append_cap({1:F(1)}, {1:F(1)}, 271, F(272))),
        ('unresolved stop loss', lambda: stoploss({}, F(1), F(1), LIMIT+1)),
        ('invalid interval scale', lambda: interval(F(1), 0)),
        ('invalid analytic range', lambda: base['tail_allowance'](20000, 10)),
    ]
    rejected = []
    for name, operation in cases:
        try:
            operation()
        except ValueError:
            rejected.append(name)
        else:
            raise ValueError('Invalid computation accepted: '+name)
    return rejected


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source', type=Path, default=Path(__file__).with_name('capped_anchor_quantile_tail.py'))
    parser.add_argument('--write-result', type=Path)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    base = load_base(args.source)
    result = json.loads(json.dumps(calculate(base), default=str))
    if args.self_test:
        print(json.dumps({'invalid_computations_rejected': self_test(base, args.source)}))
    if args.write_result:
        args.write_result.write_text(json.dumps(result, separators=(',', ':'))+'\n')
    else:
        need(result == json.loads(Path(__file__).with_suffix('.json').read_text()),
             'Retained outward bounds and exact terminal margin match recomputation')
    print(json.dumps({'ninth_reference_prime': result['ninth']['reference_prime'],
                      'tail_cutoff': result['tail']['cutoff'],
                      'safe_fourth_bound': result['ninth']['safe_fourth_bound'],
                      'strict_final_distorted_mass_lower': result['tail']['strict_simple_lower'],
                      'lean_verification': False}, indent=2))


if __name__ == '__main__':
    main()
