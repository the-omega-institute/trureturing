"""Local signed-frequency allowance on the original weighted low ball.

Reuse saved theta H1 bounds, prime-power metadata and the complete
arithmetic tail. Only the Lorentzian-weighted signed head is evaluated;
no theta action, matrix or previous head integral is repeated.
"""
import argparse
import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx, fmpq

from signed_head import interval
from signed_low_row import exact_upper, saved_ball


def local_square(z, end, atoms):
    """Double signed-measure integral of exp(-z*abs(t-u))."""
    half = arb(fmpq(1, 2))
    zm, zp = z-half, z+half
    if not zm.is_finite() or not zp.is_finite() or zm.contains(0) or zp.contains(0):
        raise ValueError('Separated elementary primitive denominators required')
    endpoint = (-zm*end).exp()
    j0 = (1-endpoint)/zm
    # The two same-half blocks and the two opposite-half blocks.
    pp = acb(2*sum((c*c for t, c in atoms), arb(0)))
    laplace_atoms = acb(0)
    pc = acb(0)
    for i, (t, c) in enumerate(atoms):
        et = (-z*t).exp()
        laplace_atoms += c*et
        for u, d in atoms[:i]:
            pp += 4*c*d*(-z*(t-u)).exp()
        jt = et*j0+((t/2).exp()-et)/zp
        jt += ((t/2).exp()-(z*t-zm*end).exp())/zm
        pc += 2*c*jt
    pp += 2*laplace_atoms**2
    cc = 4*((end.exp()-1)-j0)/zp+2*j0**2
    signed = pp-2*pc+cc
    if not signed.is_finite():
        raise ValueError('Finite signed local energy required')
    return signed.real


def produce(precision=192, supplier_root=None):
    if precision < 128:
        raise ValueError('At least 128 bits required')
    ctx.prec = precision
    root = (Path(supplier_root) if supplier_root is not None
            else Path(__file__).resolve().parent)
    names = ('derivative-bandwidth-result.json', 'forward-action-result.json',
             'sharp-center-result.json', 'signed-low-row-result.json')
    payloads = {name: (root/name).read_bytes() for name in names}
    hashes = {name: hashlib.sha256(data).hexdigest() for name, data in payloads.items()}
    derivative, forward, center, old = (json.loads(payloads[name]) for name in names)
    if any(data['bandwidth_N'] != 64 for data in (derivative, forward, center, old)):
        raise ValueError('Original saved low bandwidth must be 64')
    for name in names[:3]:
        if old['input_data_sha256'][name] != hashes[name]:
            raise ValueError('Saved signed-low-row supplier identity mismatch')
    for name in (names[0], names[2]):
        if forward['input_data_sha256'][name] != hashes[name]:
            raise ValueError('Saved theta supplier identity mismatch')
    if old['cutoff_X_exact'] != '289/2':
        raise ValueError('Retain the same exact arithmetic cutoff')
    head = old['new_signed_head']
    if head['cutoff_X_exact'] != old['cutoff_X_exact'] or head['Fibonacci_integer'] != 144:
        raise ValueError('Common signed head and endpoint required')
    metadata = head['positive_prime_power_atoms']
    if len(metadata) != 47 or not all(a['n'] < b['n'] for a, b in zip(metadata, metadata[1:])):
        raise ValueError('Retain the ordered 47 positive atoms from the saved head')
    if any(m['prime']**m['exponent'] != m['n'] or m['n'] > 144 for m in metadata):
        raise ValueError('Saved prime-power metadata inconsistent')
    atoms = [(arb(m['n']).log(), arb(m['prime']).log()/arb(m['n']).sqrt())
             for m in metadata]
    end = arb(fmpq('289/2')).log()
    if not (end-saved_ball(head['logarithmic_cut_A_interval'])).contains(0):
        raise ValueError('Same logarithmic endpoint required')
    a0sq, a1sq = (exact_upper(v) for v in derivative['derivative_norm_squared_upper'][:2])
    sup = exact_upper(forward['s_derivative_sup_upper'][0])
    tail = saved_ball(old['full_arithmetic_tail_upper_interval'])
    reference = saved_ball(old['same_head_weighted_TV_plus_tail_upper_allowance_interval'])
    old_complete = saved_ball(old['bands'][0]['complete_operator_norm_upper_allowance_interval'])
    if old['bands'][0]['band_T_exact'] != '128':
        raise ValueError('Compare with the retained T=128 complete allowance')
    # Parameters fixed before this new frequency-cell calculation.
    N, q, subdivisions = 64, arb(2), 8
    cells = []
    hull = None
    for j in range(N*subdivisions):
        left, right = fmpq(j, subdivisions), fmpq(j+1, subdivisions)
        eta = arb((left+right)/2, arb((right-left)/2).upper())
        value = local_square(acb(q, eta), end, atoms)
        if not value.upper() > 0:
            raise ValueError('Positive local-energy upper endpoint not certified')
        hull = value if hull is None else hull.union(value)
        cells.append({'left_exact': str(left), 'right_exact': str(right),
                      'signed_double_integral_real_interval': interval(value)})
    # Reflection covers [-N,0]; the shared endpoints cover all of [0,N].
    local_sup = hull.upper()
    coefficient = sup*sup*(q*a0sq+a1sq/q)/2
    head_upper = (coefficient*local_sup).sqrt()
    complete_upper = head_upper+tail
    if not complete_upper < old_complete or not complete_upper < reference:
        raise ValueError('Preregistered same-operator complete allowance improvement not certified')
    return {
        'scope': 'Fixed original N=64 complete signed arithmetic upper allowance; '
                 'not actual norm, low sign, cofinality, RH/Robin, Lean or priority',
        'precision_bits': precision,
        'bandwidth_N': N,
        'cutoff_X_exact': old['cutoff_X_exact'],
        'Lorentzian_scale_q_exact': '2',
        'cell_width_exact': '1/8',
        'positive_half_closed_cells': len(cells),
        'same_saved_positive_prime_power_atoms': metadata,
        'input_data_sha256': hashes,
        'actual_operator': old['actual_operator'],
        'theta_L2_squared_upper_interval': interval(a0sq),
        'theta_first_derivative_L2_squared_upper_interval': interval(a1sq),
        'original_s_sup_upper_interval': interval(sup),
        'local_signed_double_integral_sup_upper_interval': interval(local_sup),
        'weighted_coefficient_interval': interval(coefficient),
        'head_operator_norm_upper_allowance_interval': interval(head_upper),
        'saved_complete_arithmetic_tail_interval': interval(tail),
        'complete_operator_norm_upper_allowance_interval': interval(complete_upper),
        'retained_T128_complete_upper_allowance_interval': interval(old_complete),
        'complete_to_retained_T128_allowance_ratio_interval': interval(complete_upper/old_complete),
        'same_head_weighted_TV_plus_tail_interval': interval(reference),
        'complete_to_same_head_TV_plus_tail_ratio_interval': interval(complete_upper/reference),
        'closed_frequency_cells': cells,
        'Fourier_frequency_integral_truncation': 'None; Lorentzian identity integrates the full real line',
        'old_theta_actions_matrices_or_head_integrals_replayed': False,
        'same_signed_prime_continuum_cross_terms_retained': True,
        'low_sign_common_cofinal_comparison_RH_Robin': 'Unresolved',
        'Lean_certification': False,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--precision', type=int, default=192)
    parser.add_argument('--supplier-root', type=Path)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().with_name(
        'local-signed-frequency-result.json'))
    args = parser.parse_args()
    result = produce(args.precision, args.supplier_root)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: result[key] for key in (
        'positive_half_closed_cells', 'complete_operator_norm_upper_allowance_interval',
        'complete_to_retained_T128_allowance_ratio_interval',
        'complete_to_same_head_TV_plus_tail_ratio_interval')}, indent=2))
