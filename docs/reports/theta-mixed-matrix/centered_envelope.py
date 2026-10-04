"""Test a generic exponential error envelope on pole-cancelled primitives.

The kernel is not the arithmetic screw kernel. Exact four-tent moments
give new directed examples; no theta, prime, action or old matrix is run.
"""
import argparse
import json
from pathlib import Path

from flint import acb, arb, ctx, fmpq


def interval(value):
    if not value.is_finite():
        raise ValueError('Finite directed interval required')
    return {
        'lower_dyadic': [str(v) for v in value.lower().man_exp()],
        'upper_dyadic': [str(v) for v in value.upper().man_exp()],
        'display': str(value),
    }


def tent_transform(z, width):
    if z.contains(0):
        raise ValueError('Nonzero transform argument required')
    return 2*(1-(width*z).cos())/(width*z*z)


def produce(precision=192, phase=None):
    if precision < 128:
        raise ValueError('At least 128 bits required')
    ctx.prec = precision
    width = arb(fmpq(1, 8))
    z = acb(arb.pi(), arb(fmpq(1, 2)))
    transform = tent_transform(z, width)
    coefficient = z*z*transform*transform
    if not abs(coefficient) > 0:
        raise ValueError('Nonzero oscillatory coefficient required')

    def leading(tau):
        rotation = acb(0, -2*arb.pi()*arb(tau)).exp()
        return 4*(coefficient*rotation).real

    if phase is None:
        choices = [(fmpq(k, 64), leading(fmpq(k, 64))) for k in range(64)]
        phase = min(choices, key=lambda item: float(item[1].mid()))[0]
    else:
        phase = fmpq(phase)
    if not 0 <= phase < 1:
        raise ValueError('Exact phase in [0,1) required')
    if not leading(phase) < -abs(coefficient):
        raise ValueError('Selected phase must certify a negative leading coefficient')
    positive_phase = phase+fmpq(1, 2)
    if positive_phase >= 1:
        positive_phase -= 1
    if not leading(positive_phase) > abs(coefficient):
        raise ValueError('Opposite phase must certify a positive leading coefficient')

    pole_transform = tent_transform(acb(0, arb(fmpq(1, 2))), width).real
    tent_norm_squared = 2*width/3
    samples = []
    for kind, tau in [('negative', phase), ('positive_control', positive_phase)]:
        for index in (3, 4, 6, 9, 12):
            exact_r = fmpq(index)+tau
            r = arb(exact_r)
            ratio = (r/2).cosh()/((r-1)/2).cosh()
            if not ratio > 0:
                raise ValueError('Positive exact cosh-ratio enclosure required')
            moment = 2*pole_transform*((r/2).cosh()-ratio*((r-1)/2).cosh())
            if not moment.contains(0):
                raise ValueError('Exact algebraic pole cancellation lost')
            norm_squared = 2*(1+ratio*ratio)*tent_norm_squared
            if not norm_squared > 0:
                raise ValueError('Positive primitive norm required')
            fourier = 2*transform*((z*r).cos()-ratio*(z*(r-1)).cos())
            quadratic = (z*z*fourier*fourier).real
            quotient = quadratic/norm_squared
            if kind == 'negative' and not quotient < 0:
                raise ValueError('Negative example sign not certified')
            if kind == 'positive_control' and not quotient > 0:
                raise ValueError('Positive control sign not certified')
            samples.append({
                'kind': kind, 'r_exact': str(exact_r),
                'support_window_half_width_exact': str(exact_r+fmpq(1, 4)),
                'cosh_ratio_interval': interval(ratio),
                'zero_pole_moment_interval': interval(moment),
                'primitive_norm_squared_interval': interval(norm_squared),
                'kernel_quadratic_interval': interval(quadratic),
                'quotient_by_Neumann_metric_interval': interval(quotient),
                'quotient_scaled_by_exp_minus_r_interval': interval(quotient*(-r).exp()),
            })
    return {
        'scope': 'Generic exponential-envelope transfer obstruction on the pole-cancelled odd space; not the actual screw/theta form, not a cofinal arithmetic estimate or RH/Robin/Lean certificate',
        'precision_bits': precision,
        'kernel': 'cos(pi*t)*cosh(t/2)',
        'pointwise_envelope': 'abs(kernel(t)) <= exp(abs(t)/2)',
        'kernel_is_actual_arithmetic': False,
        'tent_half_width_exact': '1/8', 'paired_shift_distance_exact': '1',
        'transform_argument': 'pi+i/2',
        'phase_exact': str(phase), 'positive_control_phase_exact': str(positive_phase),
        'phase_selection': '64 exact dyadics; midpoint selection only, final leading coefficient and every sample use directed arithmetic',
        'negative_leading_coefficient_interval': interval(leading(phase)),
        'positive_leading_coefficient_interval': interval(leading(positive_phase)),
        'pole_cancellation': 'Exact cosh ratio makes F_f(i/2)=F_f(-i/2)=0; numerical moment interval encloses the algebraic zero',
        'domain': 'Real even compact H0^1 primitives; derivatives in odd L2 and the exact pole-cancelled constraint; smooth witnesses by the stated approximation bridge',
        'samples': samples,
        'new_directed_sample_signs_checked': True,
        'old_producers_replayed': False,
        'cofinal_arithmetic_estimate': 'Unproved',
        'RH_and_full_Robin': 'Unresolved',
        'Lean_certification': False,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--precision', type=int, default=192)
    parser.add_argument('--phase', help='Use a saved exact rational phase without reselecting it')
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().with_name(
        'centered-envelope-result.json'))
    args = parser.parse_args()
    result = produce(args.precision, args.phase)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({
        'phase': result['phase_exact'],
        'sample_quotients': [{
            'kind': s['kind'], 'r': s['r_exact'],
            'quotient': s['quotient_by_Neumann_metric_interval']['display'],
        } for s in result['samples']],
        'kernel_is_actual_arithmetic': False,
        'cofinal_arithmetic_estimate': 'Unproved',
    }, indent=2))
