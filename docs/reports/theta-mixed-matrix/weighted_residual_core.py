"""Pay a finite-core weighted residual Gram using saved full-Gamma actions.

Original-model suppliers remain premises; no new action grid or Lean result.
"""
import argparse
import hashlib
import json
import math
import sys
from fractions import Fraction
from pathlib import Path

import flint
from flint import arb, arb_mat, ctx, fmpq, fmpq_poly


def dyadic(value):
    m, e = map(int, value)
    return Fraction(m) * Fraction(2) ** e


def endpoint(item):
    return dyadic(item['dyadic'])


def rational(item):
    return Fraction(int(item['numerator']), int(item['denominator']))


def ball(value):
    value = Fraction(value)
    return arb(fmpq(value.numerator, value.denominator))


def pair(item):
    lo, hi = dyadic(item['lower_dyadic']), dyadic(item['upper_dyadic'])
    if lo > hi:
        raise ValueError('Ordered finite sample endpoints required')
    return (lo + hi) / 2, (hi - lo) / 2


def span(item):
    midpoint, radius = pair(item)
    return ball(midpoint - radius).union(ball(midpoint + radius))


def bound(value, lower=False):
    if not value.is_finite():
        raise ValueError('Finite core enclosure required')
    point = value.lower() if lower else value.upper()
    return {'display': str(point), 'dyadic': [str(v) for v in point.man_exp()]}


def interval(value):
    return {'lower_dyadic': bound(value, True)['dyadic'],
            'upper_dyadic': bound(value)['dyadic']}


def cardinal_kernel():
    """Exact polynomial integrals and a Bernstein Lebesgue bound."""
    full = fmpq_poly([1])
    for j in range(32):
        full *= fmpq_poly([-fmpq(2*j + 1, 2)**2, 0, 1])
    derivative, polynomials, maxima = full.derivative(), [], []
    for k in range(64):
        node = fmpq(2*k - 63, 2)
        polynomial, remainder = divmod(full, fmpq_poly([-node, 1]))
        if remainder:
            raise ValueError('Exact cardinal polynomial division required')
        polynomial /= derivative(node)
        polynomials.append(polynomial)
        unit = fmpq_poly([0])
        for coefficient in reversed(list(polynomial)):
            unit = unit*fmpq_poly([-fmpq(3, 2), 3]) + coefficient
        coefficients = list(unit) + [fmpq(0)]*(64 - len(unit))
        bernstein = [sum((coefficients[j]*fmpq(math.comb(i, j), math.comb(63, j))
                         for j in range(i + 1)), fmpq(0)) for i in range(64)]
        maxima.append(max(abs(v) for v in bernstein))
    kernel = [[arb(0) for _ in range(64)] for _ in range(64)]
    for i in range(64):
        for j in range(i + 1):
            product = polynomials[i]*polynomials[j]
            integral = sum((product[k]*2*fmpq(3, 2)**(k + 1)/(k + 1)
                            for k in range(0, len(product), 2)), fmpq(0))
            kernel[i][j] = kernel[j][i] = arb(integral)
    return arb_mat(kernel), arb(sum(maxima, fmpq(0)))


def produce(directory, reconstruction="saved"):
    if reconstruction not in ("saved", "sinc"):
        raise ValueError("Known residual reconstruction required")
    hashes = {}

    def load(name):
        raw = (directory/name).read_bytes()
        hashes[name] = hashlib.sha256(raw).hexdigest()
        return json.loads(raw)

    weight = load('joint-weighted-input-result.json')
    low = load('low-common-action-samples.json')
    high = load('high-full-action-samples.json')
    local = load('local-high-input-samples.json')
    low_result = load('low-common-action-result.json')
    high_result = load('high-full-action-result.json')
    gram = load('local-z-gram-result.json')
    low_caps = load('low-full-action-coefficients.json')
    off = load('off-grid-action-result.json')
    saved = load('restricted-schur-result.json')
    moments = load('exact-ground-moments-result.json')
    trials = load('common-trials.json')
    cp = load('continuous-projection-result.json') if reconstruction == 'sinc' else None
    if cp is not None:
        if (cp['bandwidth_N'], cp['trial_gamma_terms'], cp['trial_prime_cutoff'],
                cp['sample_spacing_h'], cp['physical_input_radius_X'],
                cp['contour_delta']) != (64, 1024, 64, '1/256', 4, '1/8'):
            raise ValueError('Compatible continuous projection supplier required')
        shared = {}
        for source in (cp, local, gram, off, low_caps):
            for name, digest in source.get('input_sha256', {}).items():
                if name in shared and shared[name] != digest:
                    raise ValueError('Common projection provenance mismatch: ' + name)
                shared[name] = digest
    for source in (weight, low, high, local, low_result, high_result, gram,
                   low_caps, off, saved, moments):
        for name, digest in source.get('input_sha256', {}).items():
            if name in hashes and hashes[name] != digest:
                raise ValueError('Common saved input mismatch: ' + name)
    for source, filename in ((low_result, 'low-common-action-samples.json'),
                             (high_result, 'high-full-action-samples.json'),
                             (gram, 'local-high-input-samples.json')):
        if source['retained_sample_sha256'] != hashes[filename]:
            raise ValueError('Saved matrix/sample provenance mismatch')
    if (moments['coefficient_sha256'] != hashes['low-full-action-coefficients.json']
            or low_result['ground_moment_sha256'] != hashes['exact-ground-moments-result.json']):
        raise ValueError('Saved exact ground provenance mismatch')
    if (weight['comparison_c'], saved['target_c'], weight['bandwidth_N'],
            saved['bandwidth_N'], weight['radius'], weight['grid_cells']) != ('3/8', '3/8', 64, 64, '3/2', 128):
        raise ValueError('Saved common weight/model parameters required')
    if (low['low_columns'], low['action_gamma'], low['action_prime_cutoff'],
            low['sample_dyadic_exponent']) != (95, 'full', 64, -80):
        raise ValueError('Saved full-Gamma low action required')
    if (high['action_gamma'], high['action_prime_cutoff'],
            high['Z_definition_gamma_terms'], local['trial_gamma_terms'],
            local['trial_prime_cutoff']) != ('full', 64, 1024, 1024, 64):
        raise ValueError('Full action on the fixed Z family required')
    if (not saved['complete_prime_transport'] or saved['retained_action_gamma'] != 'full'
            or saved['retained_action_prime_cutoff'] != 64
            or low_result['action_prime_powers'] != high_result['action_prime_powers']):
        raise ValueError('Saved complete common residual supplier required')
    for source in (low, high, local):
        if (source['bandwidth_N'], source['sample_spacing_h'], source['even']) != (64, '1/256', True):
            raise ValueError('Saved common even lattice required')
        if len(source['samples']) != 1025 or any(row['index'] != k for k, row in enumerate(source['samples'])):
            raise ValueError('Complete ordered saved sample rows required')
    if (moments['bandwidth_N'], moments['orthonormal_columns'],
            trials['coefficient_exponent']) != (64, 95, -40):
        raise ValueError('Saved exact ground/correction parameters required')
    raw_a = trials['correction_map_A']
    if len(raw_a) != 4 or any(len(row) != 95 for row in raw_a):
        raise ValueError('Exact common correction matrix required')
    a = [[Fraction(int(v))*Fraction(2)**-40 for v in row] for row in raw_a]
    fa = endpoint(saved['A_frobenius_upper'])
    if fa <= 0 or fa**2 < sum(v*v for row in a for v in row):
        raise ValueError('Saved correction norm is understated')
    delta = Fraction(saved['full_high_floor_lower'])
    if delta <= 0 or rational(weight['exterior_potential']) < delta:
        raise ValueError('Positive compatible exterior floor required')
    beta = []
    if len(weight['cells']) != 128:
        raise ValueError('Complete pointwise weight cells required')
    for i, cell in enumerate(weight['cells']):
        if (Fraction(cell['left']), Fraction(cell['right'])) != (Fraction(3*i, 256), Fraction(3*(i + 1), 256)):
            raise ValueError('Exact joint cell/lattice correspondence required')
        potential = rational(cell['potential'])
        if potential < delta or rational(cell['inverse_weight']) != 1/potential:
            raise ValueError('Positive compatible cell weight required')
        beta.append(1/delta - 1/potential)
    bmax = ball(max(beta))

    row_metadata = {}
    if reconstruction == 'sinc':
        from sinc_residual_rows import reconstruct
        rows, sample_error, row_metadata = reconstruct(low, high, local, a)
    else:
        rows, sample_errors = [], []
        for k in range(415):
            lo, hi, src = low['samples'][k], high['samples'][k], local['samples'][k]
            if any(len(lo.get(key, [])) != 95 for key in ('H', 'PH')) or any(
                    len(row.get(key, [])) != 4 for row, key in ((hi, 'HZ'), (hi, 'PHZ'), (src, 'H'), (src, 'PH'))):
                raise ValueError('Complete common source columns required')
            lm, lr = [], []
            for left, right in zip(lo['H'], lo['PH']):
                pairs = [(Fraction(int(v[0]))*Fraction(2)**-80,
                          Fraction(int(v[1]))*Fraction(2)**-80) for v in (left, right)]
                if any(x > y for x, y in pairs):
                    raise ValueError('Ordered low sample endpoints required')
                lm.append(sum((x + y)/2*t for (x, y), t in zip(pairs, (1, -1))))
                lr.append(sum((y - x)/2 for x, y in pairs))
            zm, zr, hm, hr = [], [], [], []
            for j in range(4):
                z0, z1 = pair(src['H'][j]), pair(src['PH'][j])
                h0, h1 = pair(hi['HZ'][j]), pair(hi['PHZ'][j])
                zm.append(z0[0] - z1[0]); zr.append(z0[1] + z1[1])
                hm.append(h0[0] - h1[0]); hr.append(h0[1] + h1[1])
            rows.append([ball(lm[j] - sum((zm[t]/8 + hm[t])*a[t][j] for t in range(4)))
                         for j in range(95)])
            sample_errors.append(ball(sum(v*v for v in lr)).sqrt()
                                 + ball(fa)*(ball(sum(v*v for v in zr)).sqrt()/8
                                             + ball(sum(v*v for v in hr)).sqrt()))
        sample_error = max(endpoint(bound(v)) for v in sample_errors)
    kernel, lebesgue = cardinal_kernel()
    line_caps = [endpoint(low_caps['low_full_H_line_L2_upper']),
                 endpoint(off['retained_prime_full_HZ_line_L2_upper']),
                 endpoint(off['wide_strip_same_high_line_L2_upper'])]
    rho_value = endpoint(saved['residual_retained_operator_norm_upper'])
    prime_value = endpoint(saved['complete_prime_joint_residual_error_upper'])
    if min(line_caps) <= 0 or rho_value < 0 or prime_value < 0:
        raise ValueError('Positive common line/norm suppliers required')
    line = ball(line_caps[0]) + ball(fa)*(ball(line_caps[1]) + ball(line_caps[2])/8)
    h, strip, circle = ball(Fraction(1, 256)), ball(Fraction(1, 8)), ball(Fraction(3, 25))
    product = math.prod(fmpq(2*j + 1, 2)**2 for j in range(2, 32))
    analytic = line/(arb.pi()*(strip - circle)).sqrt()*(h/circle)**64*arb(product)
    point_error = analytic + lebesgue*ball(sample_error)
    if reconstruction == 'sinc':
        projection_caps = [endpoint(low_caps['low_full_H_physical_and_lattice_tail_upper']),
                           endpoint(off['retained_prime_full_HZ_sinc_projection_pointwise_error_upper']),
                           endpoint(cp['combined_sinc_quadrature_and_physical_tail_pointwise_error_upper'])]
        if min(projection_caps) < 0:
            raise ValueError('Nonnegative continuous projection allowances required')
        lattice_ratio = (-2*arb.pi()*strip/h).exp()
        sinc_line = ((2*64*strip).sinh()/(2*arb.pi()*strip)).sqrt()
        low_projection = (2*ball(line_caps[0])*sinc_line*lattice_ratio/(1 - lattice_ratio)
                          + (64/arb.pi())*ball(projection_caps[0]))
        projection_error = low_projection + ball(fa)*(ball(projection_caps[1])
                                                     + ball(projection_caps[2])/8)
        row_metadata['common_continuous_projection_operator_error_upper'] = bound(projection_error)
        point_error = analytic + lebesgue*(ball(sample_error) + projection_error)
    rho, prime_error = ball(rho_value), ball(prime_value)
    integration_error = bmax*(2*rho*arb(3).sqrt()*point_error + 3*point_error**2)
    if reconstruction == 'sinc':
        mass = 6*h*ball(sum(beta, Fraction(0)))
        integration_error = 2*rho*(bmax*mass).sqrt()*point_error + mass*point_error**2
        row_metadata['core_weight_gain_mass_upper'] = bound(mass)
    prime_core_error = bmax*(2*rho*prime_error + prime_error**2)
    integration_item, prime_item = bound(integration_error), bound(prime_core_error)
    total_item = bound(ball(endpoint(integration_item) + endpoint(prime_item)))
    total_error = ball(endpoint(total_item))

    matrix = arb_mat(95, 95)
    for i, coefficient in enumerate(beta):
        samples = arb_mat([rows[abs(3*i - 30 + j)] for j in range(64)])
        matrix += 2*h*ball(coefficient)*(samples.transpose()*kernel*samples)
    matrix = (matrix + matrix.transpose())/2
    e = [span(v) for v in moments['component_intervals']]
    if len(e) != 95:
        raise ValueError('Exact ground component count required')
    enorm = sum((v*v for v in e), arb(0)).sqrt()
    v = e[:]; v[0] += enorm
    vv = sum((x*x for x in v), arb(0))
    if not enorm > 0 or not vv > 0:
        raise ValueError('Nonzero exact ground frame required')
    frame = arb_mat([[arb(int(i == j)) - 2*v[i]*v[j]/vv for j in range(1, 95)] for i in range(95)])
    restricted = frame.transpose()*matrix*frame
    restricted = (restricted + restricted.transpose())/2
    gain = restricted - total_error*arb_mat([[int(i == j) for j in range(94)] for i in range(94)])
    diagonal_lowers = [endpoint(bound(gain[i, i], True)) for i in range(94)]
    best = max(range(94), key=diagonal_lowers.__getitem__)
    return {
        'scope': 'Conditional common finite-core weighted residual supplier under saved original-model premises; no new parameter sign, global half-bound, cofinal, RH/Robin or Lean certificate',
        'runtime': {'python': sys.version.split()[0], 'python_flint': flint.__version__, 'precision_bits': ctx.prec},
        'input_sha256': hashes, 'target_c': '3/8', 'bandwidth_N': 64,
        'low_columns': 95, 'restricted_columns': 94,
        'retained_action_gamma': 'full', 'retained_action_prime_cutoff': 64,
        'Z_definition_gamma_terms': 1024, 'sample_spacing_h': '1/256',
        'core_radius': '3/2', 'positive_cells': 128,
        'cardinal_nodes': '[-30,33]', 'cardinal_degree': 63, 'circle_radius': '3/25',
        'used_absolute_sample_indices': '[0,414]', 'scalar_floor': str(delta),
        'maximum_core_weight_gain_upper': bound(bmax),
        'common_strip_line_L2_upper': bound(line),
        'analytic_interpolation_point_error_upper': bound(analytic),
        'Bernstein_Lebesgue_cap_upper': bound(lebesgue),
        'common_sample_operator_error_upper': bound(ball(sample_error)),
        'common_total_point_error_upper': bound(point_error),
        'core_integration_and_input_operator_error_upper': integration_item,
        'complete_prime_core_operator_error_upper': prime_item,
        'total_core_operator_error_upper': total_item,
        'restricted_gain_entry_intervals': [[interval(gain[i, j]) for j in range(94)] for i in range(94)],
        'restricted_gain_trace_lower': bound(sum((gain[i, i] for i in range(94)), arb(0)), True),
        'best_exact_frame_column_index_zero_based': best,
        'best_exact_frame_column_gain_lower': bound(gain[best, best], True),
        'restricted_gain_positive_semidefinite_checked': False,
        'exact_ground_frame_uncertainty_transported': True,
        'raw_95_source_annihilates_ground_direction_claimed': False,
        'theta_callbacks_executed': 0, 'old_producers_rerun': False,
        'new_parameter_or_cofinal_sign_certified': False,
        'saved_global_04605_recomputed': False, 'Lean_certification': False,
        **row_metadata,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input-dir', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--reconstruction', choices=['saved', 'sinc'], default='saved')
    args = parser.parse_args()
    ctx.prec = 192
    result = produce(args.input_dir, args.reconstruction)
    name = ('sinc-weighted-residual-core-result.json' if args.reconstruction == 'sinc'
            else 'weighted-residual-core-result.json')
    output = args.output or args.input_dir/name
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'restricted_gain_entry_intervals'}, indent=2))


if __name__ == '__main__':
    main()
