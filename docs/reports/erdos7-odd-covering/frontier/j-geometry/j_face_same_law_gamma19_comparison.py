#!/usr/bin/env python3
"""Replay complete299 same-law Gamma19 scalar envelopes using exact arithmetic.

Every positive integer load, full auxiliary tail, original source observation,
normalization and fixed-witness method bound is checked. No optimizer is loaded.
"""
import argparse
from fractions import Fraction as Q
from hashlib import sha256
from itertools import product
from pathlib import Path
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-geometry/j_face_same_law_gamma19_comparison.json'
SOURCE299 = 'certificates/source_norms/j-geometry/j_face_heavy_positive175189_complete_moment_cost_comparison.json'
SCHEMA = 'erdos7-j-face-same-law-gamma19-comparison-v1'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    SOURCE299: '4c0fe07b96685b510627df37cae3e297118e055496568767d7d082042e3376ab',
    'verify_pg1_scalar_schedule.py': 'ff5c6d067f417ed2bfd66d034a8e6cab13fadc3ca3ed4cd6e239c7c2964325e9',
    'profile-notes/001-064/35-ap45-layout-costs-and-complete-core-tails.md': '5b7569bc8a8ac2c03287e8cba51140c390327405126ea2291d7b3073e14f1c20',
    'profile-notes/001-064/07-a-common-weighted-low-layout-and-a-nonnegative-tail-correction.md': '1ae70b104e326431601e769bc8f77c8721c694368fdab53a0854e8bc88058281',
    'profile-notes/001-064/20-genuine-current-kernels-and-positive-charge.md': '2a66a59fc7e533de30dc997db4a998dbab42f67e3b5dd63754a300cbee62da58',
    'profile-notes/001-064/22-comparing-the-two-killed-steps.md': '47102f0efcde817f783dd7792c6d1ad515720f3c659df594e17817a748c5a225',
    'profile-notes/001-064/23-actual-maximizing-tests-constrain-the-killed-pair-matrix.md': 'f0aae4d2d22ee1be5d6c4ba3a6f3bafd29dcf45bcab124be8dc5057845251835',
    'profile-notes/001-064/25-eliminating-current-heights-with-a-common-old-test-distance-profile.md': '93312eb13ebae22e00c5b1b5994c92d878abcb722d2d30ff3fbaf7301a38ee36',
    'problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md': 'e7bfef78a6774051abee44bc1888fa27be24ad3786eeca0bb8f91ff57a440dc7',
}
SAME_LAW = {
    'source_domain': 'Complete299 saturated limiting357 source observations, or any finite actual source satisfying all the same complete premises; no finite family attaining the exact infinite-saturation face is asserted.',
    'source_mass': '3/20',
    'physical_prefix_thresholds': [[11, 4], [13, 5]],
    'prefix_Haar_caps': ['5/3', '12/7'],
    'prefix_normalization': 'One conditioning after13 on that same actual survivor set.',
    'later_physical_thresholds': [[17, 8], [19, 8]],
    'input19': 'Normalized physical nu13 K17; no killed or conditioned17 substitution.',
    'final_measure': 'nu13 K17^- K19^-; normalize only after joint killing.',
    'original_domain': 'Arbitrary finite later-prime heights resolving future-ending moduli; every original distinct forbidden label and every independent complete divisor-test label, including the unit.',
    'test_policy': 'Each auxiliary product1..7 has a separate uniformly bounded original test load; no common optimizer is asserted.',
    'complete_tail': 'All products at least8 use their exact full probability and first moment, with the full source mean.',
    'signed_floor': 'Shift h17 by h17(1), and the physical17-transferred h19 by E_N17 h19(N17), before13 normalization.',
}
SCOPE = ('Conditional same-law transfer from all34 complete299 observations, exact raw mass3/20 and its AP13 survival lower. '
         'The source may be a saturated limiting357 source or a finite actual source satisfying those same complete premises; no finite exact-saturation existence is asserted. '
         'AP(4,5), supported13, physical17/T8 then physical19/T8, joint killing and one final normalization retain all original labels, arbitrary finite later heights and complete auxiliary tails. '
         'The fixed-witness lower bound concerns only the separately bounded original-load scalar-envelope method. Witnesses need not be actual families or mutually compatible. '
         'No obstruction to the299 joint comparison or richer same-law correlations, no unrestricted continuation and no new Lean result is asserted.')


def require(value, message):
    if not value:
        raise ValueError(message)


def encode(value):
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Unique JSON object key: '+key)
        result[key] = value
    return result


def reject_float(value):
    raise ValueError('Exact certificate numbers must be integers or rational strings: '+value)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable pinned mathematical interface')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def reader(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned canonical reader before import')
    return module('same_law_gamma19_io', base/'certificate_io.py')


def calculate(base, probe, io):
    raw = io.read_artifact_bytes(base/SOURCE299)
    source_hash = sha256(raw).hexdigest()
    require(source_hash == PINS[SOURCE299] == probe['source299_logical_sha256'], 'Completed299 logical source')
    source = json.loads(raw, object_pairs_hook=unique, parse_float=reject_float)
    pins = dict(source['source_sha256'])
    for path, expected in PINS.items():
        require(path not in pins or pins[path] == expected, 'Consistent source closure pin: '+path)
        pins[path] = expected
    for path, expected in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == expected, 'Logical mathematical source: '+path)
    generic = module('same_law_gamma19_generic', base/'verify_pg1_scalar_schedule.py')
    basis = source['basis']
    names = [r['name'] for r in basis]
    require(len(names) == len(set(names)) == 34 and names[:3] == ['mass', 'mean', 'square'], 'All34 original observations')
    bounds = [Q(r['upper']) for r in basis]
    polynomials = [tuple(map(Q, r['tail_polynomial'])) for r in basis]
    heads = [list(map(Q, r['low_load_values'])) for r in basis]
    mass = Q(3, 20)
    require(bounds[0] == mass and Q(source['survivor_mass']) == mass
            and Q(source['geometry']['survivor_mass']) == mass
            and all(len(row) == 8 for row in heads)
            and all(len(row) == 3 for row in polynomials), 'Original mass and complete basis shapes')

    def poly_value(poly, n):
        c, b, a = poly
        return (a*n+b)*n+c

    def moment_function(i, n):
        return heads[i][n-1] if n <= 8 else poly_value(polynomials[i], n)

    def integer_tail_minimum(poly):
        c, b, a = poly
        require(a >= 0, 'Quadratic tail cannot decrease to minus infinity')
        if a == 0:
            require(b >= 0, 'Affine tail cannot decrease to minus infinity')
            candidates = [9]
        else:
            # Derivative changes sign at -b/(2a); nearest integers and boundary exhaust the minimum.
            vertex = -b/(2*a)
            left = vertex.numerator//vertex.denominator
            candidates = sorted(set([9, max(9, left), max(9, left+1)]))
        values = [poly_value(poly, n) for n in candidates]
        return min(values), candidates, values

    moment_checks = low_checks = tail_checks = 0
    def audit_row(row, target, tail, original_proof=None):
        nonlocal moment_checks, low_checks, tail_checks
        require(set(row) == {'name', 'upper', 'method_lower', 'duality_gap', 'coefficients',
                            'finite_moment_witness', 'low_gaps', 'tail_gap_polynomial',
                            'tail_minimum', 'tail_test_integers', 'tail_test_values', 'witness_moments'},
                'Exact certificate row fields')
        require(set(row['coefficients']) <= set(names), 'Every multiplier has an original name')
        prices = [Q(row['coefficients'].get(name, '0')) for name in names]
        require(all(v >= 0 for v in prices[1:]), 'Only exact mass may have a negative price')
        gaps = [sum(prices[i]*moment_function(i, n) for i in range(34))-target(n) for n in range(1, 9)]
        difference = tuple(sum(prices[i]*polynomials[i][k] for i in range(34))-tail[k] for k in range(3))
        minimum, points, values = integer_tail_minimum(difference)
        require(min(gaps) >= 0 and minimum >= 0, 'Every positive integer is covered: '+row['name'])
        require(all(k == str(int(k)) and int(k) >= 1 for k in row['finite_moment_witness']),
                'Canonical positive integer witness keys')
        witness = {int(k): Q(v) for k, v in row['finite_moment_witness'].items()}
        require(witness and min(witness) >= 1 and min(witness.values()) > 0 and sum(witness.values()) == mass, 'Original positive exact witness mass')
        moments = [sum(weight*moment_function(i, n) for n, weight in witness.items()) for i in range(34)]
        require(moments[0] == mass and all(v <= cap for v, cap in zip(moments[1:], bounds[1:])), 'All34 witness constraints')
        upper = sum(price*bound for price, bound in zip(prices, bounds))
        lower = sum(weight*target(n) for n, weight in witness.items())
        require(lower <= upper, 'Exact scalar weak duality')
        require((upper, lower, upper-lower) == tuple(Q(row[k]) for k in ['upper', 'method_lower', 'duality_gap']), 'Published scalar values')
        require(encode(gaps) == row['low_gaps'] and encode(difference) == row['tail_gap_polynomial']
                and str(minimum) == row['tail_minimum'] and points == row['tail_test_integers']
                and encode(values) == row['tail_test_values'] and encode(dict(zip(names, moments))) == row['witness_moments'], 'Every recorded exact gap and moment')
        if original_proof is not None:
            require(row['coefficients'] == original_proof['coefficients'] and row['finite_moment_witness'] == original_proof['finite_moment_witness'], 'Exact reuse of original299 certificate')
        low_checks += 8
        tail_checks += 1
        moment_checks += 34
        return upper, lower, witness

    original_proofs = {r['name']: r for r in source['proof_data']}
    original_results = {r['name']: r for r in source['results']}
    reused = {}
    for name, row in probe['reused_exact_envelopes'].items():
        require(name in ('mean', 'square') and row['name'] == name, 'Only mean and square reused')
        i = names.index(name)
        upper, lower, witness = audit_row(row, lambda n, i=i: moment_function(i, n), polynomials[i], original_proofs[name])
        require(upper == Q(original_results[name]['upper']) and lower == Q(original_results[name]['independent_moment_lower']), 'Original published299 mean/square')
        reused[name] = (upper, lower, witness)
    require(set(reused) == {'mean', 'square'}, 'Both original envelopes present')

    # Independent reconstruction of both AP denominator endpoints from299 itself.
    external = ['mean', 'hinge4']+['AP11-'+str(i) for i in range(4)]
    upper_observations = {name: Q(original_results[name]['upper']) for name in external}
    lower_observations = {}
    denominator_witness_checks = 0
    for name in external:
        i = names.index(name)
        require(all(k == str(int(k)) and int(k) >= 1 for k in original_proofs[name]['finite_moment_witness']),
                'Canonical original denominator witness keys')
        witness = {int(k): Q(v) for k, v in original_proofs[name]['finite_moment_witness'].items()}
        require(min(witness) >= 1 and min(witness.values()) > 0 and sum(witness.values()) == mass, '299 denominator witness exact mass')
        moments = [sum(weight*moment_function(j, n) for n, weight in witness.items()) for j in range(34)]
        require(moments[0] == mass and all(v <= cap for v, cap in zip(moments[1:], bounds[1:])), '299 denominator witness all34 moments')
        lower_observations[name] = moments[i]
        require(moments[i] == Q(original_results[name]['independent_moment_lower']), '299 independent denominator scalar lower')
        denominator_witness_checks += 34

    def denominator(observations):
        full_count = (observations['mean']-mass)/7986+mass/87846
        require(full_count >= 0, 'Complete original count tail nonnegative')
        return mass-observations['hinge4']/6-(sum(observations['AP11-'+str(i)] for i in range(4))+full_count)/7

    E, Ehi = denominator(upper_observations), denominator(lower_observations)
    require(0 < E <= Ehi < mass and E == Q(source['comparison_upper']['denominator'])
            and Ehi == Q(source['independent_moment_method_lower']['denominator'])
            and E == Q(probe['AP13_survival_lower']) and Ehi == Q(probe['independent_method_AP13_survival_upper']), 'Both AP denominator endpoints independently reconstructed')

    def multiply(values):
        result = Q(1)
        for value in values:
            result *= value
        return result

    def distribution(factors):
        # Direct finite tuple enumeration, independent of the producer's recursive convolution.
        weights = {}
        for choices in product(range(1, 8), repeat=len(factors)):
            k = multiply(choices)
            if k >= 8:
                continue
            probability = multiply((1-cap/p if n == 1 else cap*(p-1)/p**n) for (p, cap), n in zip(factors, choices))
            weights[int(k)] = weights.get(int(k), Q(0))+probability
        mean = multiply(1+cap/(p-1) for p, cap in factors)
        square = multiply(1+cap*Q(3*p-1, (p-1)**2) for p, cap in factors)
        tail_mass = 1-sum(weights.values())
        tail_mean = mean-sum(k*w for k, w in weights.items())
        require(tail_mass >= 0 and tail_mean >= 8*tail_mass, 'Full infinite probability and mean tails')
        original_atoms, original_mean, original_tail_mass, original_tail_mean = generic.auxiliary(factors, 8)
        require((weights, mean, tail_mass, tail_mean) ==
                (original_atoms, original_mean, original_tail_mass, original_tail_mean),
                'Direct tuple enumeration equals the pinned complete generic auxiliary interface')
        return dict(factors=factors, low_atoms=weights, mean=mean, square=square, tail_mass=tail_mass, tail_mean=tail_mean)

    factors = [(11, Q(5, 3)), (13, Q(12, 7)), (17, Q(2))]
    prefix = {17: distribution(factors[:2]), 19: distribution(factors)}
    prior = {17: distribution([]), 19: distribution(factors[2:])}
    for reconstructed, published in [(prefix, probe['prefix_complete_distributions']), (prior, probe['post13_complete_distributions'])]:
        require(set(published) == {'17', '19'}, 'Both prime product laws present')
        for p, law in reconstructed.items():
            saved = published[str(p)]
            require(saved['factors'] == encode(law['factors']) and {int(k): Q(v) for k, v in saved['low_atoms'].items()} == law['low_atoms']
                    and all(Q(saved[k]) == law[k] for k in ('mean', 'square', 'tail_mass', 'tail_mean')), 'All complete comparison product laws')
    require(prefix[17]['mean'] == Q(4, 3) and prefix[17]['square'] == Q(1403, 630), 'AP(4,5) law, not AP(4,6)')
    growth = {p: 1+Q(3*p-1, (p-1)*(p-9)) for p in (17, 19)}
    P = multiply(growth.values())
    params = {p: (p-9, Q(p-1, p-9), Q(3*p-1, (p-1)**2), growth[19] if p == 17 else Q(1)) for p in (17, 19)}
    require(P == Q(5251, 2880) and max(cap*a*future for d, cap, a, future in params.values()) == Q(295, 576), 'Natural cap growth and final convexity threshold')
    target_hi = Q(271244178927891, 10**12)
    target_lo = Q(27124417892789, 10**11)
    W = target_hi-1
    require(target_hi-target_lo == Q(1, 10**12) and W == Q(probe['SH28_W_equals_Gamma_target_minus_one'])
            and target_hi == Q(probe['Gamma19_target_upper_endpoint']) and W >= Q(295, 576), 'Final Γ is1+W and threshold bracket is retained')
    capacity_polynomial = lambda f: 5345*f*f-5596976*f+1124897312
    require(capacity_polynomial(target_lo) > 0 > capacity_polynomial(target_hi)
            and 2*5345*484-5596976 < 0,
            'Exact23-to29 scalar capacity bracket and decreasing legal seed polynomial')

    def charge(p, z):
        return Q(max(z-8, 0), p-9)

    def h(p, z, w, pure_charge=False):
        d, cap, a, future = params[p]
        correction = Q(0) if pure_charge else future*a*(Q(p-1, p-1-min(z, 8))-cap)
        return w*charge(p, z)+correction

    def floor(p, w, pure_charge=False):
        law = prior[p]
        return sum(v*h(p, n, w, pure_charge) for n, v in law['low_atoms'].items())+w*(law['tail_mean']-8*law['tail_mass'])/(p-9)

    # Only the generic mathematical functions are used. No PG1 source loader
    # or older AP(4,6) supported-profile evaluator is called.
    for p in (17, 19):
        d, cap, a, future = params[p]
        original_step, features = generic.build_step(
            p, 8, future, prefix[p]['factors'], {j: Q(0) for j in range(1, 18)}, Q(1), Q(0))
        require((original_step['d'], original_step['cap'], original_step['a'],
                 original_step['future_multiplier']) == (d, cap, a, future)
                and original_step['whole_n2_charge_improvement'] == 0,
                'Same original17/19 generic cost with no different-law source observation')
        for n, probability, end, charges, energies, improvement in features:
            require(probability == prefix[p]['low_atoms'][n] and improvement == 0,
                    'Original independent auxiliary factor and zero unrelated correction')
            for j in range(1, end+2):
                require(charges[j] == charge(p, n*j)
                        and W*charges[j]+energies[j] == h(p, n*j, W),
                        'Every generic low-load cost coefficient agrees')
        for control in (original_step['minimum_W'], W):
            generic.verify_at(original_step, features, control,
                              {j: Q(0) for j in range(1, 18)}, Q(1))

    require(floor(17, W) == -Q(413, 1728)
            and floor(19, W) == W/Q(32827093840)-Q(1003370205358, 7921588082265), 'Correct floors before the sole13 normalization')
    rows = {}
    expected_names = [kind+str(p)+'-'+str(k) for kind in ('cost', 'charge') for p in (17, 19) for k in range(1, 8)]
    require([r['name'] for r in probe['new_exact_envelopes']] == expected_names, 'Exactly14 cost and14 charge envelopes')
    for row in probe['new_exact_envelopes']:
        is_charge = row['name'].startswith('charge')
        label = row['name'][6:] if is_charge else row['name'][4:]
        p, k = map(int, label.split('-'))
        w = Q(1) if is_charge else W
        target = lambda n, p=p, k=k, w=w, is_charge=is_charge: h(p, k*n, w, is_charge)
        tail = (-8*w/(p-9), k*w/(p-9), Q(0))
        upper, lower, witness = audit_row(row, target, tail)
        rows[row['name']] = (upper, lower, witness)

    def components(lower=False, pure_charge=False):
        index = int(lower)
        den = Ehi if lower else E
        w = Q(1) if pure_charge else W
        output = []
        for p in (17, 19):
            law = prefix[p]
            low_terms = {k: v*rows[('charge' if pure_charge else 'cost')+str(p)+'-'+str(k)][index] for k, v in law['low_atoms'].items()}
            tail = w*(law['tail_mean']*reused['mean'][index]-8*law['tail_mass']*mass)/(p-9)
            raw = sum(low_terms.values())+tail
            t = floor(p, w, pure_charge)
            require(raw-mass*t >= 0, 'Shifted numerator is nonnegative before denominator substitution')
            normalized = t+(raw-mass*t)/den
            output.append(dict(prime=p, floor=t, raw_low_terms=low_terms, raw_tail=tail, raw_upper_or_lower=raw, normalized=normalized))
        return output

    uc, lc, uq, lq = components(), components(True), components(False, True), components(True, True)
    for got, key in [(uc, 'upper_costs'), (lc, 'independent_method_lower_costs'), (uq, 'upper_assigned_bad_masses'), (lq, 'independent_method_lower_bad_masses')]:
        require(encode(got) == probe[key], 'Independent normalization and complete tail: '+key)
    PAP = Q(1403, 630)
    require(PAP*reused['square'][1]-mass > 0, 'Lower square numerator remains positive')
    G13 = 1+(PAP*reused['square'][0]-mass)/E
    G13lower = 1+(PAP*reused['square'][1]-mass)/Ehi
    residual_upper = P*G13-1+sum(r['normalized'] for r in uc)-W
    residual_lower = P*G13lower-1+sum(r['normalized'] for r in lc)-W
    bad_upper = sum(r['normalized'] for r in uq)
    require(0 <= bad_upper < 1, 'Ordinary union bound gives positive survival')
    ordinary_gamma = 1+(P*G13-1)/(1-bad_upper)
    computed = dict(new_Gamma13_upper=G13, complete_bad_mass_upper=bad_upper,
                    ordinary_Gamma19_upper_if_positive_survival=ordinary_gamma,
                    SH28_upper_residual_at_threshold_upper_endpoint=residual_upper,
                    SH28_independent_method_lower_residual_at_threshold_upper_endpoint=residual_lower)
    for key, value in computed.items():
        require(value == Q(probe[key]), 'Exact published final value: '+key)
    require(residual_upper >= residual_lower > 0 and ordinary_gamma > target_hi, 'The stated method does not close the scalar endpoint')

    # Keep the already-certified cost witnesses fixed: they give a valid affine lower
    # for every W. Verify that it decreases, which transports the obstruction to all
    # smaller eligible W without assuming monotonicity of independently optimized LPs.
    slope = Q(-1)
    shift_slopes = {}
    for p in (17, 19):
        law = prefix[p]
        raw_slope = sum(v*sum(weight*charge(p, k*n) for n, weight in rows['cost'+str(p)+'-'+str(k)][2].items()) for k, v in law['low_atoms'].items())
        raw_slope += (law['tail_mean']*reused['mean'][1]-8*law['tail_mass']*mass)/(p-9)
        floor_slope = floor(p, Q(1), True)
        normalized_slope = floor_slope+(raw_slope-mass*floor_slope)/Ehi
        shift_slopes[p] = raw_slope-mass*floor_slope
        require(shift_slopes[p] >= 0, 'Shifted witness numerator is nondecreasing for all W')
        slope += normalized_slope
    require(slope < 0, 'Fixed-witness affine residual decreases throughout the target range')
    minimum_W = Q(295, 576)
    for p, row in zip((17, 19), lc):
        shifted_at_target = row['raw_upper_or_lower']-mass*row['floor']
        shifted_at_minimum = shifted_at_target+(minimum_W-W)*shift_slopes[p]
        require(min(shifted_at_target, shifted_at_minimum) >= 0, 'Witness lower numerator stays nonnegative for every eligible W')
    intercept = residual_lower-slope*W
    affine_method_gamma_lower = 1-intercept/slope
    require(affine_method_gamma_lower > target_hi, 'Fixed-witness scalar method Gamma lower exceeds target endpoint')

    fixed_witness = {
        'minimum_W': minimum_W, 'residual_slope': slope,
        'shifted_numerator_slopes': shift_slopes,
        'residual_intercept': intercept, 'Gamma_method_lower': affine_method_gamma_lower,
        'domain': 'All W>=295/576 for this fixed separately bounded scalar-envelope interface.',
    }
    result = {
        'schema': SCHEMA, 'source_sha256': pins, 'source299_logical_sha256': source_hash,
        'same_law': SAME_LAW, 'source_mass': mass, 'raw_square_upper': reused['square'][0],
        'AP13_survival_lower': E, 'independent_method_AP13_survival_upper': Ehi,
        'new_AP_square_factor': PAP, 'new_Gamma13_upper': G13,
        'Gamma19_target_upper_endpoint': target_hi,
        'SH28_W_equals_Gamma_target_minus_one': W,
        'prefix_complete_distributions': prefix, 'post13_complete_distributions': prior,
        'reused_exact_envelopes': probe['reused_exact_envelopes'],
        'new_exact_envelopes': probe['new_exact_envelopes'],
        'upper_costs': uc, 'independent_method_lower_costs': lc,
        'upper_assigned_bad_masses': uq, 'independent_method_lower_bad_masses': lq,
        **computed, 'fixed_witness_lower': fixed_witness,
        'counts': {'new_envelopes': 28, 'reused_envelopes': 2,
                   'low_integer_checks': low_checks, 'entire_integer_tail_checks': tail_checks,
                   'witness_moment_checks': moment_checks,
                   'denominator_witness_moment_checks': denominator_witness_checks},
        'scope': SCOPE,
    }
    return encode(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--certificate', type=Path)
    parser.add_argument('--check', action='store_true', help='Replay every exact proof; also the default.')
    args = parser.parse_args()
    io = reader(args.base)
    path = args.certificate if args.certificate is not None else args.base/CERTIFICATE
    stored = json.loads(io.read_artifact_bytes(path), object_pairs_hook=unique, parse_float=reject_float)
    result = calculate(args.base, stored, io)
    require(result == stored, 'Entire canonical certificate, same-law domain and final scope equality')
    print('PASS:28 new and2 reused whole-integer envelopes; complete tails, source witnesses and same-law Gamma19 scalar boundary.')
    print('Gamma13 upper', float(Q(result['new_Gamma13_upper'])),
          '; scalar method Gamma lower', float(Q(result['fixed_witness_lower']['Gamma_method_lower'])))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
