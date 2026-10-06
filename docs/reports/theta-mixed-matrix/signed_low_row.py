"""Signed arithmetic coupling on the original weighted low unit ball.

Reuse saved theta bounds and the signed-head integrator. Pay the Fourier
tail as well as the head band, and retain the complete arithmetic tail.
This fixed-band allowance supplies neither the low sign nor RH.
"""
import argparse
import hashlib
import json
from pathlib import Path

from flint import arb, ctx, fmpq

from signed_head import compute_heads, interval


def exact_upper(item):
    mantissa, exponent = item['dyadic']
    value = arb(int(mantissa))*arb(2)**int(exponent)
    if not value.is_finite() or not value > 0:
        raise ValueError('Positive finite saved upper bound required')
    return value


def saved_ball(item):
    def endpoint(pair):
        return arb(int(pair[0]))*arb(2)**int(pair[1])
    lower = endpoint(item['lower_dyadic'])
    upper = endpoint(item['upper_dyadic'])
    if not lower <= upper:
        raise ValueError('Ordered directed endpoints required')
    return lower.union(upper)


def produce(precision=192, supplier_root=None):
    if precision < 128:
        raise ValueError('At least 128 bits required')
    ctx.prec = precision
    canonical = (Path(supplier_root) if supplier_root is not None
                 else Path(__file__).resolve().parent)
    names = ('derivative-bandwidth-result.json', 'forward-action-result.json',
             'sharp-center-result.json')
    payloads = {name: (canonical/name).read_bytes() for name in names}
    hashes = {name: hashlib.sha256(data).hexdigest()
              for name, data in payloads.items()}
    suppliers = {name: json.loads(data) for name, data in payloads.items()}
    derivative, forward, center = (suppliers[name] for name in names)
    if any(data['bandwidth_N'] != 64 for data in (derivative, forward, center)):
        raise ValueError('Original saved low bandwidth must be 64')
    for name in (names[0], names[2]):
        if forward['input_data_sha256'][name] != hashes[name]:
            raise ValueError('Saved theta supplier identity mismatch')
    norms2 = [exact_upper(x) for x in derivative['derivative_norm_squared_upper']]
    if len(norms2) != 4:
        raise ValueError('Four original derivative bounds required')
    sup = exact_upper(forward['s_derivative_sup_upper'][0])
    if not sup**4 >= norms2[0]*norms2[1]:
        raise ValueError('Saved H1 supremum does not enclose the derivative transport')
    K0 = exact_upper(center['K0_upper'])
    N = 64
    cutoff = '289/2'
    width = '1/64'
    bands = (128, 192)
    head = compute_heads(precision, (cutoff,), width, bands)[0]
    variation = saved_ball(head['total_variation_interval'])
    X = arb(fmpq(cutoff))
    L = head['Fibonacci_integer']
    b = arb(fmpq(3, 8))
    r = (-2*b).exp()
    # Existing complete prime operator tail; both translated directions.
    prime_tail = 2*K0*K0*r**(L+1)*((L+1)-L*r)/(1-r)**2
    # Both continuum directions, with exp(t/2)dt and n=exp(t)>X.
    continuum_tail = 2*K0*K0*(-2*b*X).exp()/(2*b*X.sqrt())
    full_tail = prime_tail+continuum_tail
    baseline_head = sup*sup*variation
    baseline_complete = baseline_head+full_tail
    results = []
    for data, T in zip(head['bands'], bands):
        if T <= N or data['band_exact'] != str(T):
            raise ValueError('The Fourier band must strictly contain the low source band')
        U = saved_ball(data['signed_band_upper_allowance_interval'])
        # Angular unnormalized Fourier: no dimension factor for the low unit ball.
        band = norms2[0]*U
        spectral_tail = variation*variation*2*norms2[2]/(3*arb(T-N)**3)
        factor = sup*sup/(2*arb.pi())
        head_bound = (factor*(band+spectral_tail)).sqrt()
        full_bound = head_bound+full_tail
        if not head_bound < baseline_head or not full_bound < baseline_complete:
            raise ValueError('Preregistered complete coupling improvement not certified')
        results.append({
            'band_T_exact': str(T),
            'band_expense_before_weight_interval': interval(band),
            'out_of_band_expense_before_weight_interval': interval(spectral_tail),
            'head_operator_norm_upper_allowance_interval': interval(head_bound),
            'complete_operator_norm_upper_allowance_interval': interval(full_bound),
            'head_to_same_measure_weighted_TV_ratio_interval': interval(
                head_bound/baseline_head),
            'complete_to_same_head_TV_plus_tail_ratio_interval': interval(
                full_bound/baseline_complete),
        })
    return {
        'scope': 'Fixed N=64 complete signed-discrepancy coupling upper allowance; '
                 'not a low-block sign, cofinal, RH/Robin, Lean or priority result',
        'precision_bits': precision,
        'bandwidth_N': N,
        'cutoff_X_exact': cutoff,
        'tent_width_exact': width,
        'original_row': 'p=s v, s=sqrt(Phi/(2cosh(x/2))), w=1/s^2, v in P_N L2',
        'actual_operator': 'M_s C_mu M_s P_N on original whole-line L2',
        'input_data_sha256': hashes,
        'saved_s_sup_upper_interval': interval(sup),
        'saved_s_L2_squared_upper_interval': interval(norms2[0]),
        'saved_s_second_L2_squared_upper_interval': interval(norms2[2]),
        'full_two_direction_prime_tail_upper_interval': interval(prime_tail),
        'full_two_direction_continuum_tail_upper_interval': interval(continuum_tail),
        'full_arithmetic_tail_upper_interval': interval(full_tail),
        'same_measure_weighted_TV_head_upper_allowance_interval': interval(baseline_head),
        'same_head_weighted_TV_plus_tail_upper_allowance_interval': interval(baseline_complete),
        'new_signed_head': head,
        'bands': results,
        'both_preregistered_full_allowance_improvements': True,
        'finite_row_count_factor': 'None; bound is uniform on the entire low unit ball',
        'old_theta_actions_or_matrices_replayed': False,
        'low_block_sign_and_common_cofinal_comparison': 'Unproved',
        'RH_and_full_Robin': 'Unresolved',
        'Lean_certification': False,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--precision', type=int, default=192)
    parser.add_argument('--supplier-root', type=Path)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().with_name(
        'signed-low-row-result.json'))
    args = parser.parse_args()
    result = produce(args.precision, args.supplier_root)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({
        'N': result['bandwidth_N'],
        'full_tail': result['full_arithmetic_tail_upper_interval']['display'],
        'bands': [{
            'T': row['band_T_exact'],
            'full_allowance': row['complete_operator_norm_upper_allowance_interval']['display'],
            'same_measure_ratio': row['complete_to_same_head_TV_plus_tail_ratio_interval']['display'],
        } for row in result['bands']],
    }, indent=2))
