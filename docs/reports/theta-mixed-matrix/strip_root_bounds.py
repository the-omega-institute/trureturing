"""Original-theta coherent root and directed Fourier-tail coefficients.

This supplies paper-model inputs, not retained integrals or a matrix sign.
Invalid whole boxes raise ValueError in ordinary mode; analytic integration
probes receive a nonfinite ball so the integrator can subdivide them.
"""
import hashlib
import json
import sys
from pathlib import Path

import flint
from flint import acb, arb, ctx, fmpq

ctx.prec = 128
CANONICAL = Path(__file__).resolve().parent
STRIP = arb(fmpq(1, 6))
OVERLAP = arb(fmpq(1, 8))
ROOT_TERMS = 8


def rational(numerator, denominator=1):
    return arb(fmpq(numerator, denominator))


def relative_tail(terms):
    if not isinstance(terms, int) or isinstance(terms, bool) or terms < 1:
        raise ValueError('Positive integer relative-series count required')
    n = terms + 1
    return rational(7, 2)*n**4*arb(-2*(n*n-1)).exp()*rational(1000, 999)


def right_root(z, terms=ROOT_TERMS):
    """Transported positive root on Re z > -1/8, |Im z| < 1/6."""
    z = acb(z)
    if not z.is_finite() or not z.real > -OVERLAP or not abs(z.imag) < STRIP:
        raise ValueError('Whole box is outside the right overlap strip')
    remainder = acb(0)
    w = (2*z).exp()
    leading = 2*arb.pi()*w-3
    if not leading.real > 0:
        raise ValueError('Leading-root right-half-plane enclosure failed')
    for n in range(2, terms+1):
        remainder += (n*n*(2*arb.pi()*n*n*w-3)/leading
                      *(-arb.pi()*(n*n-1)*w).exp())
    error = relative_tail(terms).upper()
    remainder += acb(arb(0, error), arb(0, error))
    root_factor = 1+remainder
    denominator = (z/2).cosh()
    if not root_factor.real > 0 or not denominator.real > 0:
        raise ValueError('Principal-root factor enclosure failed; subdivide box')
    result = (arb.pi().sqrt()*(rational(5, 4)*z-arb.pi()*w/2).exp()
              *leading.sqrt()*root_factor.sqrt()/denominator.sqrt())
    if not result.is_finite():
        raise ValueError('Nonfinite coherent root enclosure')
    return result


def strict_root(z):
    """Even glued branch with diagnostic rejection of uncertified boxes."""
    z = acb(z)
    if not z.is_finite() or not abs(z.imag) < STRIP:
        raise ValueError('Whole box is outside the certified physical strip')
    if z.real > -OVERLAP:
        return right_root(z)
    if z.real < OVERLAP:
        return right_root(-z)
    raise ValueError('Box spans both overlap charts; subdivide box')


def coherent_root(z, analytic=False):
    """Even glued branch; reflection negates both coordinates.

    Following acb.integral's callback contract, an uncertified analytic
    probe returns a nonfinite ball. Ordinary evaluation retains diagnostics.
    This module does not evaluate an integral or certify its quadrature.
    """
    try:
        return strict_root(z)
    except ValueError:
        if analytic:
            return acb('nan')
        raise


def endpoint(value):
    if not value.is_finite():
        raise RuntimeError('Nonfinite coefficient')
    value = value.upper()
    return {'display': str(value), 'dyadic': [str(x) for x in value.man_exp()]}


def from_endpoint(item):
    mantissa, exponent = item['dyadic']
    return arb(int(mantissa))*arb(2)**int(exponent)


def envelopes(delta):
    delta = arb(delta)
    if not delta >= 0 or not delta <= rational(1, 8):
        raise ValueError('Envelope contour is outside [0,1/8]')
    a = arb.pi()*(2*delta).cos()
    C = 2*arb.pi()*rational(7, 6)/(delta/2).cos()
    if not a > 2:
        raise RuntimeError('Monotone envelope condition failed')
    expa = (-a).exp()
    A = (C*(2*arb.pi()+3)*expa).sqrt()
    B = (C*expa*(2*arb.pi()*(1/a+1/a**2)+3/a)).sqrt()
    V = (4*arb.pi()*rational(7, 6)*expa
         *(2*arb.pi()*(1/a+2/a**2+2/a**3)+3*(1/a+1/a**2))).sqrt()
    return A, B, V


def callback_checks():
    checks = 0
    for x in (rational(-3), rational(-1), rational(-1, 16), arb(0),
              rational(1, 16), arb(1), arb(3)):
        for y in (arb(0), rational(-1, 10), rational(1, 10),
                  rational(-1, 8), rational(1, 8)):
            z = acb(x, y)
            value = coherent_root(z)
            if not value.overlaps(coherent_root(-z)):
                raise RuntimeError('Even branch check failed')
            if not value.conjugate().overlaps(coherent_root(z.conjugate())):
                raise RuntimeError('Schwarz branch check failed')
            if y.is_zero() and not value.real > 0:
                raise RuntimeError('Positive real root check failed')
            checks += 1
    overlap_checks = 0
    for x in (rational(-1, 16), arb(0), rational(1, 16)):
        for y in (rational(-1, 8), rational(1, 8)):
            z = acb(arb(x, rational(1, 256)), arb(y, rational(1, 1024)))
            if not right_root(z).overlaps(right_root(-z)):
                raise RuntimeError('Full-box overlap chart check failed')
            overlap_checks += 1
    invalid = (
        acb(0, rational(1, 6)),
        acb(0, arb(rational(1, 8), rational(1, 12))),
        acb(arb(0, rational(1, 4)), 0),
        acb(arb(1, 1), rational(1, 8)),
        acb('nan'),
    )
    rejected = 0
    for z in invalid:
        try:
            coherent_root(z)
        except ValueError:
            rejected += 1
        else:
            raise RuntimeError('An uncertified entire box was accepted')
        if coherent_root(z, analytic=True).is_finite():
            raise RuntimeError('An uncertified analytic probe was finite')
    if not coherent_root(acb(rational(1, 16), rational(1, 8)), analytic=True).is_finite():
        raise RuntimeError('A valid analytic probe was nonfinite')
    return {'point_branch_checks': checks, 'full_box_overlap_checks': overlap_checks,
            'invalid_whole_boxes_rejected': rejected,
            'invalid_analytic_probes_nonfinite': len(invalid),
            'valid_analytic_probes_finite': 1,
            'scope': 'Bounded branch checks only; all-strip proof is in strip-root.md'}


def main():
    inputs = {}

    def read_data(name):
        data = (CANONICAL/name).read_bytes()
        inputs[name] = hashlib.sha256(data).hexdigest()
        return json.loads(data)

    high = read_data('high-trial-bounds-result.json')
    trials = read_data('common-trials.json')
    trial_hash = inputs['common-trials.json']
    if trial_hash != high['input_sha256']['common-trials.json']:
        raise RuntimeError('High-family coefficient hash mismatch')
    if (high['bandwidth_N'], high['trial_gamma_terms'], high['trial_prime_cutoff']) != (64, 1024, 64):
        raise RuntimeError('High-family parameter mismatch')
    if trials['coefficient_exponent'] != -40:
        raise RuntimeError('Unexpected saved dyadic precision')
    FB = from_endpoint(high['trial_B_frobenius_upper'])
    M = from_endpoint(high['finite_multiplier_sup_upper'])
    W = from_endpoint(high['retained_prime_weight_sum_upper'])
    q_rational = rational(56000, 342657)
    if not q_rational < rational(1, 6):
        raise RuntimeError('Exact relative margin failed')
    delta = rational(1, 8)
    A, B, V = envelopes(delta)
    A0 = envelopes(arb(0))[0]
    D = A*A*(M+8+2*W)*(64*delta).exp()+rational(3, 8)*V
    U = (V*V+(D*FB)**2).sqrt()
    low_line = arb(2).sqrt()*A*(64*delta).exp()
    high_line = arb(2).sqrt()*A*U
    records = []
    for omega in (128, 256, 512):
        if not arb(omega) >= 1/(4*delta):
            raise RuntimeError('Gamma exponential envelope is not decreasing')
        G = 4+(1+4*arb(omega)**2).log()/2
        decay = (-delta*omega).exp()
        records.append({
            'frequency_band_Omega': omega,
            'full_gamma_symbol_envelope_upper': endpoint(G),
            'low_sp_fourier_tail_norm_upper': endpoint(decay*low_line),
            'high_sZ_fourier_tail_operator_norm_upper': endpoint(decay*high_line),
            'low_full_gamma_action_tail_upper': endpoint(A0*G*decay*low_line),
            'high_full_gamma_action_tail_upper': endpoint(A0*G*decay*high_line),
            'high_high_gamma_form_tail_upper': endpoint(G*decay**2*high_line**2),
        })
    if not from_endpoint(records[-1]['high_full_gamma_action_tail_upper']) < rational(1, 10**15):
        raise RuntimeError('Declared finite-frequency high-action tail target failed')
    result = {
        'scope': 'Paper-model original-kernel/root and Fourier-action coefficients; '
                 'retained integrals, projection, residual Gram and matrix sign unpaid; no Lean or RH certificate',
        'runtime': {'python': sys.version.split()[0], 'python_flint': flint.__version__,
                    'precision_bits': ctx.prec},
        'input_sha256': inputs,
        'physical_nonvanishing_strip': '1/6', 'contour_delta': '1/8',
        'right_chart_minimum_real': '-1/8', 'root_retained_theta_terms': ROOT_TERMS,
        'relative_remainder_rational_upper': '56000/342657 < 1/6',
        'relative_root_series_tail_upper': endpoint(relative_tail(ROOT_TERMS)),
        's_strip_sup_upper': endpoint(A), 's_real_sup_upper': endpoint(A0),
        's_line_L2_upper': endpoint(B), 'v0_line_L2_upper': endpoint(V),
        'retained_forward_line_L2_operator_upper': endpoint(D),
        'common_high_line_L2_operator_upper': endpoint(U),
        'low_sp_two_line_L2_operator_upper': endpoint(low_line),
        'high_sZ_two_line_L2_operator_upper': endpoint(high_line),
        'tail_bounds': records,
        'callback_checks': callback_checks(),
        'high_trial_definition': 'Z=Q H_1024,64 E B; g=Q v0; exact continuous Q',
        'retained_integrals_evaluated': False,
        'original_derivative_grid_rerun': False,
        'unpaid': ['retained whole-line integrals', 'physical/input truncation',
                  'continuous projection quadrature', 'coefficient and ground transport',
                  'common residual Gram', 'matrix sign', 'cofinal c to 1/2'],
    }
    output = CANONICAL/'strip-root-bounds-result.json'
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
