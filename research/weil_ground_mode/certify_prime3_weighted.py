"""Energy-weighted infinite-complement certificate for the actual c=3 Weil form.

Uses the reviewed arithmetic routines in certify_prime3_refined.py, checked
by SHA-256. The new paper theorem gives, on |n|>=65,
q(y) >= sum (3/2 + log(|n|/65))*|y_n|^2.
The verifier uses rational shell weights 3/2+j/2 for
65*2**j <= |n| < 65*2**(j+1). It does not infer a form bound from
diagonal entries, and does not run an eigensolver or use zeta-zero data.

All omitted spatial Fourier modes are covered by the existing second-jet
majorant, now divided by their own certified energy. Analytic Hilbert-transform,
Gamma-diagonal, closed-form and Fourier-domain bridges are in the existing
RH theory volume; this executable check is not a Lean kernel proof.
"""
from __future__ import annotations
import hashlib
import importlib.util
import json
import pathlib
import platform
import time
from fractions import Fraction
import numpy as np
from mpmath import iv

if not __debug__:
    raise RuntimeError('Verification requires assertions; do not use python -O.')
ROOT = pathlib.Path(__file__).resolve().parent
BASE = ROOT / 'certify_prime3_refined.py'
BASE_HASH = '8bb067fc5499b0f2e1e48836e7a82237a15504109f82a856c72478d1096d69d0'
if hashlib.sha256(BASE.read_bytes()).hexdigest() != BASE_HASH:
    raise RuntimeError('Arithmetic dependency differs from the reviewed source.')
spec = importlib.util.spec_from_file_location('weil_reviewed_arithmetic', BASE)
if spec is None or spec.loader is None:
    raise ImportError('Cannot load arithmetic dependency.')
b = importlib.util.module_from_spec(spec)
spec.loader.exec_module(b)
N, M, BITS, ERROR_BITS = 64, 32768, 44, 60

def rat(x: Fraction):
    return iv.mpf(x.numerator) / x.denominator

def digest(matrix: np.ndarray) -> str:
    payload = json.dumps([[str(int(x)) for x in row] for row in matrix],
                         separators=(',', ':')).encode()
    return hashlib.sha256(payload).hexdigest()

def run() -> None:
    start = time.time()
    iv.dps = 55
    n0, d = N + 1, 2 * N + 1
    ns = np.arange(-N, N + 1, dtype=np.int64)
    ms = np.arange(N + 1, M + 1, dtype=np.int64)
    L, pi = iv.ln(3), iv.pi
    pole_debt = 2 * ((iv.sqrt(3) - 1 / iv.sqrt(3)) / 2 - L / 2)
    prime_debt = iv.ln(2) / iv.sqrt(2)
    # Actual all-scale logarithmic lower-bound constant, specialized at c=3.
    weight_at_n0 = (iv.ln(n0 / L) - 2 - (2 * L + 1) / (pi * n0)
                    - L / (2 * pi**2 * n0**2) - prime_debt - pole_debt)
    assert bool(weight_at_n0 > iv.mpf(3) / 2)
    assert bool(iv.ln(2) > iv.mpf(1) / 2)
    assert bool(L < 2 * iv.ln(2))  # disjoint prime-2 translation chains

    sig = b.symbol_array(np.arange(1, M + 1))
    slo = np.r_[-sig.hi[:N][::-1], 0, sig.lo[:N]]
    shi = np.r_[-sig.lo[:N][::-1], 0, sig.hi[:N]]
    C = ((b.I(slo[None, :], shi[None, :])
          - b.I(sig.lo[N:, None], sig.hi[N:, None]))
         / (b.PI * b.I(ms[:, None] - ns[None, :])))
    assert np.all(np.isfinite(C.lo)) and np.all(np.isfinite(C.hi))
    X = np.rint(C.mid() * 2**BITS).astype(np.int64)
    assert int(np.max(np.abs(X))) < 2**53
    exactx = np.ldexp(X.astype(float), -BITS)
    err = np.maximum(b.up(C.hi - exactx), b.up(exactx - C.lo))
    assert np.all(err >= 0) and np.all(np.isfinite(err))
    radius = np.ceil(np.ldexp(err, ERROR_BITS)).astype(np.int64)
    assert int(np.max(radius)) < 2**53
    assert np.all(np.ldexp(radius.astype(float), -ERROR_BITS) >= err)
    assert 2 * radius.size * int(np.max(radius))**2 < 2**63
    e2 = Fraction(2 * int(np.sum(radius * radius, dtype=np.int64)),
                  2**(2 * ERROR_BITS))
    shells, G = [], np.zeros((d, d), dtype=object)
    first, j = n0, 0
    while first <= M:
        last = min(2 * first - 1, M)
        gplus = b.exact_gram(X[first - n0:last - n0 + 1])
        g = gplus + gplus[::-1, ::-1]
        assert np.array_equal(g, g[::-1, ::-1])
        shells.append((first, last, Fraction(3 + j, 2), g))
        G += g
        first *= 2
        j += 1
    assert sum(last - first + 1 for first, last, _, _ in shells) == M - N
    assert digest(G) == '7f4e1049624807432efe96a68fe63babbc1c3bd37f2d40600a4cddadbddb85a9'
    trace = Fraction(sum(int(G[i, i]) for i in range(d)), 2**(2 * BITS))
    eta = Fraction(1, 10**10)
    assert e2 < eta and 4 * trace * e2 < (eta - e2)**2
    # The same global error-energy inequality also holds after row weighting:
    # ||C*WC-Cq*WCq|| <= ||W||*(2||Cq||_F*||E||_F+||E||_F^2).
    tail_weight = shells[-1][2]
    tail_start = shells[-1][0]
    assert M + 1 >= tail_start
    rem = Fraction(9, 10**13)
    analytic_rem = 16 * 9 * N**4 * d / (pi**2 * (1 - iv.mpf(N) / M)**2 * M**5)
    assert bool(analytic_rem < rat(rem))
    print('weighted-shell exact Gram and error-energy checks passed', flush=True)

    ss = [iv.mpf([float(slo[i]), float(shi[i])]) for i in range(d)]
    AA = [[iv.mpf(0) for _ in range(d)] for _ in range(d)]
    tail = [[iv.mpf(0) for _ in range(d)] for _ in range(d)]
    for i, ni in enumerate(ns):
        AA[i][i] = b.diagonal_iv(int(ni))
        for h in range(i):
            AA[i][h] = (ss[i] - ss[h]) / (pi * int(ns[h] - ni))
            AA[h][i] = AA[i][h]
        for h in range(i + 1):
            t = 8 / pi**2 * ((9 + ss[i] * ss[h]) / M
                 + int(ni) * int(ns[h]) * (9 + ss[i] * ss[h]) / M**3)
            if i == h:
                t += rat(rem)
            tail[i][h] = t
            tail[h][i] = t
    vv = [iv.mpf(int(x)) / 2**40 for x in b.CANDIDATE]
    assert len(vv) == d and b.CANDIDATE == tuple(reversed(b.CANDIDATE))
    norm = sum((x * x for x in vv), iv.mpf(0))
    assert bool(norm > 0)
    ray = sum((vv[i] * AA[i][h] * vv[h] for i in range(d) for h in range(d)), iv.mpf(0)) / norm
    lower = Fraction(107, 2 * 10**9)
    upper = Fraction(560909, 10**13)
    threshold = Fraction(3, 250000)
    assert bool(ray < rat(upper)) and lower < upper < threshold < Fraction(3, 2)
    even = [[(N, 1)]] + [[(N + h, 1), (N - h, 1)] for h in range(1, N + 1)]
    odd = [[(N + h, 1), (N - h, -1)] for h in range(1, N + 1)]
    def check(shift: Fraction, lift: bool):
        HH = [[iv.mpf(0) for _ in range(d)] for _ in range(d)]
        for i in range(d):
            for h in range(i + 1):
                g = sum((iv.mpf(int(Gj[i, h])) / 2**(2 * BITS) / rat(w - shift)
                         for _, _, w, Gj in shells), iv.mpf(0))
                g += tail[i][h] / rat(tail_weight - shift)
                if i == h:
                    g += rat(eta) / rat(Fraction(3, 2) - shift)
                val = AA[i][h] - g + (vv[i] * vv[h] if lift else 0)
                if i == h:
                    val -= rat(shift)
                HH[i][h], HH[h][i] = val, val
        def block(basis):
            return [[sum((sx * sy * HH[i][h] for i, sx in x for h, sy in y), iv.mpf(0))
                     for y in basis] for x in basis]
        tag = 'weighted-complement' if lift else 'weighted-full-lower'
        return {'even': b.interval_ldl(block(even), tag + '-even'),
                'odd': b.interval_ldl(block(odd), tag + '-odd')}
    low_pivots = check(lower, False)
    comp_pivots = check(threshold, True)
    distance_sq = (upper - lower) / (threshold - lower)
    distance = Fraction(59, 4000)
    assert distance_sq < distance**2
    report = {
        'scale': 'a=log(3)/2', 'N': N, 'M': M,
        'candidate': 'unchanged 129-entry dyadic vector in certify_prime3_refined.py',
        'source_sha256': hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
        'arithmetic_dependency_sha256': BASE_HASH,
        'unweighted_gram_sha256': digest(G),
        'logarithmic_lower_constant_display': str(weight_at_n0),
        'exact_error_energy': str(e2), 'unweighted_gram_error_budget': str(eta),
        'second_jet_unweighted_scalar_tail_budget': str(rem),
        'shells': [{'first': first, 'last': last, 'energy_lower': str(w), 'gram_sha256': digest(g)}
                   for first, last, w, g in shells],
        'infinite_remainder_energy_lower': str(tail_weight),
        'candidate_rayleigh_interval': str(ray),
        'ground_lower': str(lower), 'candidate_upper': str(upper),
        'orthogonal_threshold': str(threshold),
        'gap_lower': str(threshold - upper),
        'projective_distance_sq_upper': str(distance_sq),
        'projective_distance_upper': str(distance),
        'full_lower_ldl_pivots_display': low_pivots,
        'complement_ldl_pivots_display': comp_pivots,
        'python': platform.python_version(), 'numpy': np.__version__,
        'elapsed_seconds': time.time() - start,
        'status': 'directed interval and exact integer checks passed; not a Lean run',
        'paper_bridges': ['actual Fourier/domain identification',
                         'integer discrete-Hilbert norm <= pi',
                         'actual Gamma diagonal and high-frequency symbol bounds',
                         'full logarithmic high-mode form bound and weighted Schur completion',
                         'infinite second-jet square summation']}
    (ROOT / 'prime3_weighted_certificate.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2), flush=True)

if __name__ == '__main__':
    run()
