#!/usr/bin/env python3
"""A physical CRT counterexample to a proposed compressed prime-step state.

Use the unchanged PG1 low law, pure17 forbidden residue0, and the actual
normalized clipped kernel with delta7/15. Two distinct original21-class
families have identical forbidden row densities, natural caps, charges,
old test loads, and all pre-kernel fixed-test marginals. Their common
complete24-label test nevertheless has different post-kernel squares.

All classes and test labels are evaluated literally modulo5355. This is
a finite counterexample to sufficiency of those observations, and to a
universally positive mixed-event overlap for the new square increment.
The full square has a nonzero old baseline; its overlap is not zero.
No supremum over tests, unrestricted covering claim, or later-prime
continuation is established. Uses only Python's standard library.

Default operation checks source hashes and replays the entire certificate.
--write regenerates this certificate only. Checks remain active under -O.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import argparse
import json

HERE = Path(__file__).resolve().parent
SCHEMA = 'erdos7-pg1-physical-overlap-v1'
SOURCE = 'certificates/mod3_conditioned_geometry_certificate.json'
LOW_PERIOD, PRIME, PERIOD = 315, 17, 5355
DELTA = F(7, 15)
MIXED_COFACTORS = (3, 5, 7, 9, 15, 21, 35, 45, 315)
X0, TEST_ROOT = 2, 10


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def crt(d, a, root):
    """Literal CRT class in [0,17*d), with no symbolic class substitution."""
    require(LOW_PERIOD % d == 0 and 0 <= a < d and 0 <= root < PRIME,
            'admissible low and prime residues')
    solutions = [a+d*k for k in range(PRIME) if (a+d*k) % PRIME == root]
    require(len(solutions) == 1, 'unique literal CRT residue')
    return solutions[0]


def label(d, a):
    return {'modulus': d, 'residue': a}


def hits(z, labels):
    return sum(z % row['modulus'] == row['residue'] for row in labels)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {key: encode(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(item) for item in value]
    return value


def evaluate(directory, expected_hashes=None):
    raw = read_artifact_bytes(directory/SOURCE)
    hashes = {SOURCE: sha256(raw).hexdigest()}
    if expected_hashes is not None:
        require(hashes == expected_hashes, 'unchanged source PG1 certificate')
    source = json.loads(raw)
    require(source['schema'] == 'erdos7-mod3-conditioned-geometry-v1', 'PG1 source schema')
    cases = [case for case in source['cases'] if case['name'] == 'PG1']
    require(len(cases) == 1, 'unique PG1 law')
    case = cases[0]
    points, weights, den = case['points'], case['weight_numerators'], case['weight_denominator']
    old_family = [label(d, a) for d, a in case['family']]
    require(len(old_family) == 11 and len({r['modulus'] for r in old_family}) == 11
            and all(1 < r['modulus'] and r['modulus'] % 2 and
                    LOW_PERIOD % r['modulus'] == 0 and 0 <= r['residue'] < r['modulus']
                    for r in old_family), 'eleven distinct odd original low moduli')
    require(points == [x for x in range(LOW_PERIOD) if hits(x, old_family) == 0]
            and len(points) == len(weights) == 75 and den == 1000000007
            and all(type(w) is int and w >= 0 for w in weights) and sum(weights) == den,
            'unchanged exact PG1 probability on its actual survivor carrier')
    mu = {x: F(w, den) for x, w in zip(points, weights)}
    require(mu.get(X0, F()) == F(13119398, 1000000007) > 0, 'positive PG1 witness row')
    require(DELTA == F(8-1, PRIME-2) and LOW_PERIOD*PRIME == PERIOD,
            'physical17/T8 threshold and complete period')
    divisors = [d for d in range(1, LOW_PERIOD+1) if LOW_PERIOD % d == 0]
    old_test = [label(d, X0 % d) for d in divisors]
    new_test = [label(PRIME*d, crt(d, X0 % d, TEST_ROOT)) for d in divisors]
    test = old_test+new_test
    require(len(test) == len({r['modulus'] for r in test}) == 24 and
            {r['modulus'] for r in test} == {d for d in range(1, PERIOD+1) if PERIOD % d == 0},
            'one fixed complete24-label test')
    families = {}
    for name, shift in (('A', 0), ('B', 1)):
        mixed = [label(PRIME*d, crt(d, X0 % d, i+shift))
                 for i, d in enumerate(MIXED_COFACTORS, 1)]
        all_classes = old_family+[label(PRIME, 0)]+mixed
        require(len(all_classes) == len({r['modulus'] for r in all_classes}) == 21
                and all(1 < r['modulus'] and r['modulus'] % 2 and PERIOD % r['modulus'] == 0
                        and 0 <= r['residue'] < r['modulus'] for r in all_classes),
                'twenty-one distinct admissible original forbidden classes')
        families[name] = {'mixed': mixed, 'original_classes': all_classes}
    require(families['A']['original_classes'] != families['B']['original_classes'],
            'different actual forbidden families')
    prior = {z: mu[z % LOW_PERIOD]/16 for z in range(PERIOD)
             if z % LOW_PERIOD in mu and z % PRIME != 0}
    require(len(prior) == 1200 and sum(prior.values(), F()) == 1
            and all(hits(z, old_family+[label(PRIME, 0)]) == 0 for z in prior),
            'complete supported low times uniform pure17 survivor probability')
    rows, post = [], {name: {} for name in families}
    kernels = {}
    pair_labels = [next(r for r in new_test if r['modulus'] == d) for d in (17, 5355)]
    for x in points:
        active = [d for d in MIXED_COFACTORS if x % d == X0 % d]
        alpha = F(len(active), 16)
        clipped = min(alpha, DELTA)
        g = 1/(1-clipped)
        h = clipped/(alpha*(1-clipped)) if alpha else F()
        cap = F(16, 15)*g
        charge = max(F(), alpha-DELTA)/(1-DELTA)
        old_load = hits(x, old_test)
        require(g-h*alpha == 1 and 0 <= charge <= 1 and g <= F(15, 8)
                and cap <= 2 and old_load >= 1, 'normalized physical kernel and natural cap')
        kernels[x] = (g, h)
        common_pre = None
        row = {'low_residue': x, 'low_probability': mu[x], 'active_mixed_cofactors': active,
               'alpha': alpha, 'g': g, 'h': h, 'natural_cap': cap, 'charge': charge,
               'old_test_load': old_load, 'families': {}}
        for name, shift in (('A', 0), ('B', 1)):
            mixed = families[name]['mixed']
            bad = [t for t in range(1, PRIME) if hits(crt(LOW_PERIOD, x, t), mixed)]
            expected_bad = [i+shift for i, d in enumerate(MIXED_COFACTORS, 1) if d in active]
            require(bad == sorted(expected_bad) and F(len(bad), 16) == alpha,
                    'literal original mixed union has the proposed row density')
            density = [g-h*int(t in bad) for t in range(1, PRIME)]
            require(sum(density, F())/16 == 1 and min(density) >= 0
                    and all(r/16 <= cap/PRIME for r in density),
                    'normalized nonnegative physical kernel and actual prefix cap')
            loads, increments, pairs = [], [], []
            individual = [F() for _ in test]
            direct_mean = direct_square = direct_increment = direct_pair = F()
            actual_charge = F()
            for t, rho in enumerate(density, 1):
                z = crt(LOW_PERIOD, x, t)
                require(z in prior and prior[z] == mu[x]/16, 'literal complete-period prior')
                old = hits(z, old_test)
                new = hits(z, new_test)
                full = hits(z, test)
                pair = int(hits(z, pair_labels) == 2)
                increment = full*full-old*old
                require(old == old_load and new == old_load*int(t == TEST_ROOT)
                        and full == old+new and increment == 3*old_load**2*int(t == TEST_ROOT),
                        'literal original24-label test and nonconstant square increment')
                loads.append(full)
                increments.append(increment)
                pairs.append(pair)
                for at, item in enumerate(test):
                    individual[at] += F(int(z % item['modulus'] == item['residue']), 16)
                post[name][z] = prior[z]*rho
                direct_mean += F(full, 16)*rho
                direct_square += F(full*full, 16)*rho
                direct_increment += F(increment, 16)*rho
                direct_pair += F(pair, 16)*rho
                actual_bad = int(hits(z, families[name]['original_classes']) > 0)
                require(actual_bad == int(t in bad), 'full original forbidden family on actual support')
                actual_charge += F(actual_bad, 16)*rho
            require(actual_charge == charge, 'direct original-family violation equals clipped charge')
            moments = {'mean': F(sum(loads), 16), 'square': F(sum(v*v for v in loads), 16),
                       'square_increment': F(sum(increments), 16), 'pair': F(sum(pairs), 16),
                       'individual_test_marginals': individual}
            require(moments['mean'] == F(17*old_load, 16)
                    and moments['square'] == F(19*old_load**2, 16), 'pre-kernel complete-test moments')
            if common_pre is None:
                common_pre = moments
            require(moments == common_pre, 'all pre-kernel test marginals and moments unchanged')
            overlap = {'mean': F(sum(v for t, v in enumerate(loads, 1) if t in bad), 16),
                       'square': F(sum(v*v for t, v in enumerate(loads, 1) if t in bad), 16),
                       'square_increment': F(sum(v for t, v in enumerate(increments, 1) if t in bad), 16),
                       'pair': F(sum(v for t, v in enumerate(pairs, 1) if t in bad), 16)}
            direct = {'mean': direct_mean, 'square': direct_square,
                      'square_increment': direct_increment, 'pair': direct_pair}
            require(all(direct[key] == g*moments[key]-h*overlap[key] for key in direct),
                    'direct moments equal the physical kernel identity')
            require(direct_square == old_load**2+g*moments['square_increment']
                    -h*overlap['square_increment'], 'old baseline is preserved, not assigned zero overlap')
            require(sum(post[name][crt(LOW_PERIOD, x, t)] for t in range(1, PRIME)) == mu[x],
                    'every complete low-history marginal is preserved')
            row['families'][name] = {'bad_high_roots': bad, 'densities': density,
                                     'pre_kernel_overlap': overlap, 'post_kernel_moments': direct}
        row['pre_kernel_moments'] = common_pre
        require(row['families']['A']['pre_kernel_overlap']['square_increment'] == 0
                and row['families']['A']['pre_kernel_overlap']['pair'] == 0,
                'family A has zero overlap with the nonconstant increment and chosen pair')
        require((TEST_ROOT in row['families']['B']['bad_high_roots']) == (x == X0),
                'family B hits the test high root exactly at the full315 witness row')
        gap = row['families']['A']['post_kernel_moments']['square']-row['families']['B']['post_kernel_moments']['square']
        require(gap == (42 if x == X0 else 0), 'all row square differences are explicit')
        row['post_kernel_square_difference_A_minus_B'] = gap
        rows.append(row)
    global_data = {}
    old_marginals = {d: [sum((mass for x, mass in mu.items() if x % d == a), F())
                         for a in range(d)] for d in divisors}
    for name in families:
        law = post[name]
        require(set(law) == set(prior) and min(law.values()) >= 0 and sum(law.values(), F()) == 1,
                'global physical law is a normalized nonnegative probability')
        # Iterate the physical period independently of the row-moment formula.
        direct = {'mean': F(), 'square': F(), 'square_increment': F(), 'pair': F(), 'charge': F()}
        overlap = {key: F() for key in ('full_square', 'square_increment', 'pair')}
        pre_square = weighted_square_formula = F()
        for z in range(PERIOD):
            before, after = prior.get(z, F()), law.get(z, F())
            old, full = hits(z, old_test), hits(z, test)
            bad = int(hits(z, families[name]['original_classes']) > 0)
            pair = int(hits(z, pair_labels) == 2)
            increment = full*full-old*old
            direct['mean'] += after*full
            direct['square'] += after*full*full
            direct['square_increment'] += after*increment
            direct['pair'] += after*pair
            direct['charge'] += after*bad
            overlap['full_square'] += before*bad*full*full
            overlap['square_increment'] += before*bad*increment
            overlap['pair'] += before*bad*pair
            pre_square += before*full*full
            if before:
                g, h = kernels[z % LOW_PERIOD]
                weighted_square_formula += before*(g-h*bad)*full*full
        require(direct['square'] == weighted_square_formula and
                all(direct[key] == sum((r['low_probability']*r['families'][name]['post_kernel_moments'][key]
                                       for r in rows), F()) for key in ('mean', 'square', 'square_increment', 'pair')),
                'global literal period sums agree with both kernel and row identities')
        require(direct['charge'] == sum((r['low_probability']*r['charge'] for r in rows), F()),
                'global actual violation charge equals its identical row expectation')
        for d, expected in old_marginals.items():
            observed = [F() for _ in range(d)]
            for z, mass in law.items():
                observed[z % d] += mass
            require(observed == expected, 'all original low-divisor cylinder marginals preserved')
        require(overlap['full_square'] > 0, 'full-square overlap includes the positive old baseline')
        global_data[name] = {'post_kernel_moments': direct, 'pre_kernel_square': pre_square,
                             'pre_kernel_overlap': overlap, 'total_mass': sum(law.values(), F()),
                             'positive_support_count': sum(mass > 0 for mass in law.values())}
    witness = next(row for row in rows if row['low_residue'] == X0)
    require((witness['old_test_load'], witness['alpha'], witness['g'], witness['h'],
             witness['charge'], witness['natural_cap']) == (12, F(9, 16), F(15, 8), F(14, 9), F(23, 128), 2),
            'exact physical witness-row constants')
    require(witness['families']['A']['post_kernel_moments']['square'] == F(1557, 8)
            and witness['families']['B']['post_kernel_moments']['square'] == F(1221, 8),
            'exact unequal witness-row fixed-test squares')
    gap = global_data['A']['post_kernel_moments']['square']-global_data['B']['post_kernel_moments']['square']
    require(gap == 42*mu[X0] > 0 and
            global_data['A']['post_kernel_moments']['charge'] == global_data['B']['post_kernel_moments']['charge'],
            'same global charge and strictly different fixed-test squares')
    require(global_data['A']['pre_kernel_overlap']['square_increment'] == 0
            and global_data['A']['pre_kernel_overlap']['pair'] == 0
            and global_data['B']['pre_kernel_overlap']['square_increment'] == 27*mu[X0]
            and global_data['B']['pre_kernel_overlap']['pair'] == mu[X0]/16,
            'zero versus positive nonconstant-increment and pair overlap')
    return encode({'schema': SCHEMA, 'source_sha256': hashes, 'result': {
        'source_case': 'PG1', 'low_period': LOW_PERIOD, 'prime': PRIME, 'period': PERIOD,
        'threshold': 8, 'delta': DELTA, 'witness_low_residue': X0, 'test_high_root': TEST_ROOT,
        'mixed_cofactors': MIXED_COFACTORS, 'pure_forbidden_class': label(PRIME, 0),
        'source_weight_denominator': den, 'witness_low_probability': mu[X0],
        'original_families': {name: value['original_classes'] for name, value in families.items()},
        'complete_test': test, 'chosen_new_label_pair': pair_labels,
        'prior_support_count': len(prior), 'rows': rows, 'global': global_data,
        'post_kernel_square_difference_A_minus_B': gap,
        'identical_observations': ['actual low probability', 'pure17 survivor law',
            'original modulus set', 'row forbidden density', 'row natural cap',
            'row and global assigned charge', 'all old test loads',
            'all pre-kernel fixed-test label marginals and complete-test moments'],
        'separating_observation': 'Mixed-forbidden-event overlap with the fixed new test labels.',
        'scope': 'Two actual21-class finite families and one fixed complete24-label test. '
            'Counterexample to sufficiency of the listed compressed observations for the next fixed-test square, '
            'and to universal strictly positive overlap for the nonconstant square increment or chosen pair. '
            'Full-square overlap is positive in both families. No test-supremum bound, '
            'unrestricted odd-covering conclusion, or arbitrary-height continuation.'}})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path, default=HERE/'certificates/pg1_physical_overlap_certificate.json')
    parser.add_argument('--source-directory', type=Path, default=HERE)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    expected = None if args.write else json.loads(read_artifact_text(args.certificate))
    if expected is not None:
        require(expected['schema'] == SCHEMA, 'physical overlap certificate schema')
    actual = evaluate(args.source_directory, None if expected is None else expected['source_sha256'])
    if args.write:
        write_certificate_text(args.certificate, json.dumps(actual, indent=2)+'\n')
    else:
        require(actual == expected, 'complete deterministic physical-overlap certificate equality')
    print(json.dumps({'status': 'written' if args.write else 'verified',
        'post_kernel_square_difference_A_minus_B': actual['result']['post_kernel_square_difference_A_minus_B'],
        'same_charge': actual['result']['global']['A']['post_kernel_moments']['charge']}))


if __name__ == '__main__':
    main()
