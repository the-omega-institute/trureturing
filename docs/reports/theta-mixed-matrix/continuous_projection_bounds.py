"""Directed model coefficients for continuous sinc projection and aliases.

Actual forward samples, their numerical errors and the common Gram are
separate obligations. No old integration grid or DFT probe is repeated.
"""
import argparse
import hashlib
import json
from pathlib import Path

from flint import arb, ctx, fmpq


def exact(item):
    mantissa, exponent = item['dyadic']
    return arb(int(mantissa))*arb(2)**int(exponent)


def upper(value):
    if not value.is_finite():
        raise RuntimeError('Nonfinite continuous-projection coefficient')
    value = value.upper()
    return {'display': str(value),
            'dyadic': [str(x) for x in value.man_exp()]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--precision', type=int, default=128)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.precision < 64:
        parser.error('Precision must be at least 64 bits')
    ctx.prec = args.precision
    canonical = Path(__file__).resolve().parent
    inputs = {}

    def load(name):
        data = (canonical/name).read_bytes()
        inputs[name] = hashlib.sha256(data).hexdigest()
        return json.loads(data)

    strip = load('strip-root-bounds-result.json')
    high = load('high-trial-bounds-result.json')
    trials = load('common-trials.json')
    if strip['input_sha256']['high-trial-bounds-result.json'] != inputs['high-trial-bounds-result.json']:
        raise RuntimeError('Strip/high supplier hash mismatch')
    if high['input_sha256']['common-trials.json'] != inputs['common-trials.json']:
        raise RuntimeError('Saved high-family trial hash mismatch')
    if (high['bandwidth_N'], high['trial_gamma_terms'], high['trial_prime_cutoff']) != (64, 1024, 64):
        raise RuntimeError('Whole-line high-family parameter mismatch')
    if strip['contour_delta'] != '1/8' or trials['coefficient_exponent'] != -40:
        raise RuntimeError('Contour or dyadic family mismatch')

    N, X, omega = arb(64), arb(4), arb(512)
    delta, h, c = arb(fmpq(1, 8)), arb(fmpq(1, 256)), arb(fmpq(3, 8))
    F = 2*arb.pi()/h
    if not omega < F/2:
        raise RuntimeError('Retained frequency band exceeds the half-period')
    FB = exact(high['trial_B_frobenius_upper'])
    M = exact(high['finite_multiplier_sup_upper'])
    W = exact(high['retained_prime_weight_sum_upper'])
    A0 = exact(strip['s_real_sup_upper'])
    B = exact(strip['s_line_L2_upper'])
    D = exact(strip['retained_forward_line_L2_operator_upper'])
    K = ((2*N*delta).sinh()/(2*arb.pi()*delta)).sqrt()
    ratio = (-delta*F).exp()
    qh = 2*D*FB*K*ratio/(1-ratio)

    b, UX = arb.pi()/2, (2*X).exp()
    if not UX > 2/b:
        raise RuntimeError('Physical lattice tail is not monotone')
    Cs = (2*arb.pi()*arb(fmpq(7, 6))*(2*arb.pi()+3)).sqrt()
    CH = Cs*FB*(A0*(N/arb.pi()).sqrt()*(2*M+8+2*W)+2*c)
    JX = CH*(-b*UX).exp()*(UX/b+1/b**2)
    physical_projection = N/arb.pi()*JX
    G = 4+(1+4*omega**2).log()/2
    alias_sum = 2*(-delta*(F-omega)).exp()/(1-ratio)
    records = []
    for family, U in (
        ('low_band_unit_ball', (N*delta).exp()),
        ('same_five_generator_high_family', exact(strip['common_high_line_L2_operator_upper'])),
    ):
        point = B*U/(2*arb.pi()).sqrt()*alias_sum
        records.append({
            'input_family': family,
            'infinite_lattice_alias_sup_upper': upper(point),
            'retained_band_full_gamma_alias_action_upper': upper(A0*G*(2*omega).sqrt()*point),
        })
    result = {
        'scope': 'Paper-model continuous-projection and infinite-lattice alias coefficients; actual sample/action/Gram errors and matrix sign remain unpaid',
        'precision_bits': ctx.prec, 'input_sha256': inputs,
        'classical_source': 'Tao Proposition 3(i),(v), Fourier inversion and the saved model strip envelopes',
        'bandwidth_N': 64, 'trial_gamma_terms': 1024, 'trial_prime_cutoff': 64,
        'sample_spacing_h': '1/256', 'physical_input_radius_X': 4,
        'frequency_period': '512 pi', 'alias_retained_frequency_band_Omega': 512,
        'contour_delta': '1/8',
        'sinc_line_L2_upper': upper(K),
        'infinite_sinc_lattice_uniform_pointwise_error_upper': upper(qh),
        'forward_pointwise_envelope_coefficient_upper': upper(CH),
        'forward_physical_and_discrete_L1_tail_upper': upper(JX),
        'finite_sinc_lattice_tail_pointwise_error_upper': upper(physical_projection),
        'combined_sinc_quadrature_and_physical_tail_pointwise_error_upper': upper(qh+physical_projection),
        'projection_sample_error_L1_multiplier_upper': upper(N/arb.pi()),
        'infinite_lattice_alias_records': records,
        'finite_DFT_identity': {
            'length': 32768, 'physical_period': 128,
            'local_output_radius': '33/4', 'input_radius': 4,
            'maximum_used_difference': '49/4', 'kernel_signed_radius': 64,
            'continuous_cutoff_in_kernel': 64, 'sharp_frequency_mask_used': False,
        },
        'actual_operator_samples_evaluated': False,
        'old_integration_grid_rerun': False,
        'unpaid': ['actual forward sample enclosures and their errors',
                   'kernel and arithmetic evaluation errors',
                   'whole-line high action and common Gram',
                   'projected ground direction and restricted matrix sign'],
        'Lean_certification': False,
    }
    output = args.output or canonical/'continuous-projection-result.json'
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
