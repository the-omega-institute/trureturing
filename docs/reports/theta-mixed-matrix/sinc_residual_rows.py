"""Reconstruct the common residual from saved unprojected even rows.

Reuse the continuous physical sinc sum; acquire no operator samples.
"""
from fractions import Fraction

from flint import arb, arb_mat

from weighted_residual_core import ball, bound, dyadic, endpoint, pair


def reconstruct(low, high, local, a):
    """Return exact midpoint rows with one paid operator error cap."""
    raw, squared_errors = [], []
    for k in range(1025):
        lo, hi, src = low['samples'][k], high['samples'][k], local['samples'][k]
        if (len(lo.get('H', [])) != 95 or len(hi.get('HZ', [])) != 4
                or len(src.get('H', [])) != 4):
            raise ValueError('Complete unprojected source columns required')
        lp = [(dyadic((v[0], -80)), dyadic((v[1], -80))) for v in lo['H']]
        if any(x > y for x, y in lp):
            raise ValueError('Ordered unprojected low endpoints required')
        hp, sp = [pair(v) for v in hi['HZ']], [pair(v) for v in src['H']]
        mids, radii = [], []
        for j, (left, right) in enumerate(lp):
            mids.append((left + right)/2 - sum(
                (hp[t][0] + sp[t][0]/8)*a[t][j] for t in range(4)))
            radii.append((right - left)/2 + sum(
                (hp[t][1] + sp[t][1]/8)*abs(a[t][j]) for t in range(4)))
        raw.append([ball(v) for v in mids])
        squared_errors.append(sum(v*v for v in radii))
    raw_error = ball(max(squared_errors)).sqrt()

    pi = arb.pi()
    sinc = [1/(4*pi)] + [ball(Fraction(d, 4)).sin()/(pi*d)
                         for d in range(1, 1439)]
    weights, amplification = [], []
    for k in range(415):
        row = [arb(int(k == 0)) - sinc[k]]
        row.extend(arb(int(k == m)) - sinc[abs(k - m)] - sinc[k + m]
                   for m in range(1, 1025))
        weights.append(row)
        amplification.append(endpoint(bound(sum((abs(v) for v in row), arb(0)))))
    amplification_cap = ball(max(amplification))
    projected = arb_mat(weights)*arb_mat(raw)

    rows, rounding_errors = [], []
    for k in range(415):
        mids, radii = [], []
        for j in range(95):
            lower = endpoint(bound(projected[k, j], True))
            upper = endpoint(bound(projected[k, j]))
            mids.append(ball((lower + upper)/2))
            radii.append((upper - lower)/2)
        rows.append(mids)
        rounding_errors.append(sum(v*v for v in radii))
    rounding_error = ball(max(rounding_errors)).sqrt()
    source_error = amplification_cap*raw_error + rounding_error
    if not source_error.is_finite() or not amplification_cap > 0:
        raise ValueError('Finite common sinc reconstruction required')
    metadata = {
        'residual_reconstruction': 'even-folded continuous sinc from saved unprojected rows',
        'unprojected_input_rows': 1025,
        'reconstructed_absolute_nodes': '[0,414]',
        'continuous_cutoff_kernel': 'sin(d/4)/(pi*d), value1/(4pi) at d0',
        'unprojected_common_row_operator_error_upper': bound(raw_error),
        'even_folded_sinc_row_amplification_upper': bound(amplification_cap),
        'sinc_kernel_and_row_arithmetic_operator_error_upper': bound(rounding_error),
        'sinc_source_and_arithmetic_operator_error_upper': bound(source_error),
    }
    return rows, endpoint(bound(source_error)), metadata
