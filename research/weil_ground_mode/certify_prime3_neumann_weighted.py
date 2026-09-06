"""Energy-weighted, all-mode Schur certificate for the c=3 Weil window.

Uses the arithmetic interval primitives and the fixed dyadic candidate in
certify_prime3_refined.py. The new analytic input is the Neumann Green-kernel
completion of the canonical Gamma resolvent mixture. It gives, for every
even high-mode vector, the diagonal lower form
  sum_{|m|>N} (gamma(2*pi*m/log(3)) - log(2)/sqrt(2))*|y_m|^2.
The paper proof and its exact domain/normalization are in the existing RH
research theory volume. The Lean companion proves the boundary-kernel
factorization and finite Gamma-mixture positivity, not the full operator
bridge. This executable certificate is not a Lean kernel proof.

No zero locations or eigensolver enter. A failed interval LDL attempt during
lower-bound search makes no claim about a negative eigenvalue.
"""
from __future__ import annotations
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path
import numpy as np
from mpmath import iv
import importlib.util

ROOT = Path(__file__).resolve().parent
BASE_PATH = ROOT / 'certify_prime3_refined.py'
BASE_HASH = '8bb067fc5499b0f2e1e48836e7a82237a15504109f82a856c72478d1096d69d0'
if hashlib.sha256(BASE_PATH.read_bytes()).hexdigest() != BASE_HASH:
    raise RuntimeError('Arithmetic dependency differs from the reviewed source.')
spec = importlib.util.spec_from_file_location('weil_refined_arithmetic', BASE_PATH)
if spec is None or spec.loader is None:
    raise ImportError('Cannot load the pinned arithmetic dependency.')
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)

if not __debug__:
    raise RuntimeError('Verification requires assertions; do not run with -O.')

ROOT = Path(__file__).resolve().parent
N, M, BITS, ERROR_BITS = 64, 32768, 44, 60
THRESHOLD = Fraction(1, 200000)
OLD_LOWER = Fraction(103, 2000000000)
UPPER = Fraction(560909, 10**13)


def rat(x: Fraction):
    return iv.mpf(x.numerator) / x.denominator


def neumann_weight_lower(n: int) -> Fraction:
    """Independent analytic gamma lower bound, then verified rational floor."""
    assert n > 0
    L = iv.ln(3)
    bound = iv.ln(iv.mpf(n) / L) - L / (iv.pi * n) - iv.ln(2) / iv.sqrt(2)
    value = Fraction(math.floor(float(bound.a) * 2**20) - 1, 2**20)
    assert bool(rat(value) < bound)
    assert value > THRESHOLD
    return value


def ldl_check(A):
    """Interval LDL; returns None if positivity was not certified."""
    size = len(A)
    factors = [[iv.mpf(0) for _ in range(size)] for _ in range(size)]
    pivots = []
    for j in range(size):
        factors[j][j] = iv.mpf(1)
        p = A[j][j] - sum((factors[j][k]**2 * pivots[k] for k in range(j)), iv.mpf(0))
        if not bool(p > 0):
            return None
        pivots.append(p)
        for i in range(j + 1, size):
            factors[i][j] = (A[i][j] - sum(
                (factors[i][k] * factors[j][k] * pivots[k] for k in range(j)),
                iv.mpf(0))) / p
    return min(float(p.a) for p in pivots)


def run():
    iv.dps = 55
    assert bool(iv.ln(3) < 2 * iv.ln(2))
    ns = np.arange(-N, N + 1, dtype=np.int64)
    ms = np.arange(N + 1, M + 1, dtype=np.int64)
    dimension = len(ns)
    sig = base.symbol_array(np.arange(1, M + 1))
    slo = np.r_[-sig.hi[:N][::-1], 0, sig.lo[:N]]
    shi = np.r_[-sig.lo[:N][::-1], 0, sig.hi[:N]]
    C = (base.I(slo[None, :], shi[None, :]) -
         base.I(sig.lo[N:, None], sig.hi[N:, None])) / (
             base.PI * base.I(ms[:, None] - ns[None, :]))
    assert np.all(np.isfinite(C.lo)) and np.all(np.isfinite(C.hi))
    scaled = np.rint(C.mid() * 2**BITS)
    assert np.all(np.isfinite(scaled)) and np.max(np.abs(scaled)) < 2**53
    X = scaled.astype(np.int64)
    exactx = np.ldexp(X.astype(float), -BITS)
    err = np.maximum(base.up(C.hi - exactx), base.up(exactx - C.lo))
    assert np.all(np.isfinite(err)) and np.all(err >= 0)
    scaledradius = np.ceil(np.ldexp(err, ERROR_BITS))
    assert np.all(np.isfinite(scaledradius)) and np.max(scaledradius) < 2**53
    radius = scaledradius.astype(np.int64)
    assert np.all(np.ldexp(radius.astype(float), -ERROR_BITS) >= err)
    assert 2 * radius.size * int(np.max(radius))**2 < 2**63

    weighted = [[Fraction(0) for _ in range(dimension)] for _ in range(dimension)]
    ordinary = np.zeros((dimension, dimension), dtype=object)
    trace_w, error_w, error_unweighted = Fraction(0), Fraction(0), Fraction(0)
    shells = []
    first = N + 1
    while first <= M:
        last = min(2 * (first - 1), M)
        lo, hi = first - (N + 1), last - N
        positive_gram = base.exact_gram(X[lo:hi])
        gram = positive_gram + positive_gram[::-1, ::-1]
        ordinary += gram
        energy_lower = neumann_weight_lower(first)
        weight = 1 / (energy_lower - THRESHOLD)
        e_shell = Fraction(2 * int(np.sum(radius[lo:hi]**2, dtype=np.int64)),
                           2**(2 * ERROR_BITS))
        error_w += weight * e_shell
        error_unweighted += e_shell
        trace_w += weight * Fraction(sum(int(gram[i, i]) for i in range(dimension)),
                                    2**(2 * BITS))
        for i in range(dimension):
            for j in range(dimension):
                weighted[i][j] += weight * Fraction(int(gram[i, j]), 2**(2 * BITS))
        shells.append({'first': first, 'last': last,
                       'energy_lower': str(energy_lower),
                       'resolvent_weight_upper': str(weight)})
        first = last + 1

    assert sum(s['last'] - s['first'] + 1 for s in shells) == M - N
    assert np.array_equal(ordinary, ordinary[::-1, ::-1])
    ordinary_hash = hashlib.sha256(json.dumps(
        [[str(int(x)) for x in row] for row in ordinary],
        separators=(',', ':')).encode()).hexdigest()
    assert ordinary_hash == '7f4e1049624807432efe96a68fe63babbc1c3bd37f2d40600a4cddadbddb85a9' 
    eta = Fraction(1, 10**16)
    while not (error_w < eta and 4 * trace_w * error_w < (eta - error_w)**2):
        eta *= 2
    assert eta < Fraction(1, 10**9)
    ordinary_trace = Fraction(sum(int(ordinary[i, i]) for i in range(dimension)),
                              2**(2 * BITS))
    old_eta = Fraction(1, 10**10)
    assert error_unweighted < old_eta
    assert 4 * ordinary_trace * error_unweighted < (old_eta - error_unweighted)**2

    # Original all-parity high block, independently rechecked for the odd sector.
    a = iv.ln(3) / 2
    eps = 4 / (3 * iv.pi**2)
    R = iv.pi * N / (4 * a)
    gamma0 = -iv.euler - iv.pi/2 - 3*iv.ln(2) - iv.ln(iv.pi)
    t = R / 2
    increment = sum((t*t / ((iv.mpf(j)+iv.mpf(1)/4) *
                    ((iv.mpf(j)+iv.mpf(1)/4)**2 + t*t)) for j in range(512)), iv.mpf(0))
    pole_debt = 2 * ((iv.sqrt(3) - 1/iv.sqrt(3))/2 - a)
    beta_old = (1-eps)*(gamma0+increment)+eps*gamma0-iv.ln(2)/iv.sqrt(2)-pole_debt
    assert bool(beta_old > 1)
    assert bool(2*((iv.sqrt(3)+1/iv.sqrt(3))/2)+iv.ln(2)/iv.sqrt(2) < 3)
    rem = Fraction(9, 10**13)
    analytic_rem = 16*9*N**4*dimension / (iv.pi**2*(1-iv.mpf(N)/M)**2*M**5)
    assert bool(analytic_rem < rat(rem))
    far_lower = neumann_weight_lower(M + 1)
    far_weight = 1 / (far_lower - THRESHOLD)

    symbols = [iv.mpf([float(slo[i]), float(shi[i])]) for i in range(dimension)]
    arithmetic = [[iv.mpf(0) for _ in range(dimension)] for _ in range(dimension)]
    W = [[iv.mpf(0) for _ in range(dimension)] for _ in range(dimension)]
    G = [[iv.mpf(0) for _ in range(dimension)] for _ in range(dimension)]
    for i, ni in enumerate(ns):
        arithmetic[i][i] = base.diagonal_iv(int(ni))
        for j in range(i):
            value = (symbols[i]-symbols[j])/(iv.pi*int(ns[j]-ni))
            arithmetic[i][j] = arithmetic[j][i] = value
        for j in range(i + 1):
            tail = 8/iv.pi**2 * ((9+symbols[i]*symbols[j])/M +
                     int(ns[i])*int(ns[j])*(9+symbols[i]*symbols[j])/M**3)
            w = rat(weighted[i][j]) + rat(far_weight) * tail
            g = iv.mpf(int(ordinary[i, j]))/2**(2*BITS) + tail
            if i == j:
                w += rat(eta + far_weight * rem)
                g += rat(old_eta + rem)
            W[i][j] = W[j][i] = w
            G[i][j] = G[j][i] = g

    candidate = [iv.mpf(int(x))/2**40 for x in base.CANDIDATE]
    assert len(candidate) == dimension
    assert base.CANDIDATE == tuple(reversed(base.CANDIDATE))
    norm = sum((x*x for x in candidate), iv.mpf(0))
    assert bool(norm > 0)
    ray = sum((candidate[i]*arithmetic[i][j]*candidate[j]
               for i in range(dimension) for j in range(dimension)), iv.mpf(0))/norm
    assert bool(ray < rat(UPPER))
    even = [[(N, 1)]] + [[(N+j, 1), (N-j, 1)] for j in range(1, N+1)]
    odd = [[(N+j, 1), (N-j, -1)] for j in range(1, N+1)]

    def block(A, basis):
        return [[sum((sx*sy*A[i][j] for i, sx in x for j, sy in y), iv.mpf(0))
                 for y in basis] for x in basis]

    odd_matrix = [[arithmetic[i][j] - G[i][j]/(1-rat(THRESHOLD)) -
                   (rat(THRESHOLD) if i == j else 0)
                   for j in range(dimension)] for i in range(dimension)]
    odd_pivot = ldl_check(block(odd_matrix, odd))
    assert odd_pivot is not None
    even_complement = [[arithmetic[i][j] - W[i][j] + candidate[i]*candidate[j] -
                        (rat(THRESHOLD) if i == j else 0)
                        for j in range(dimension)] for i in range(dimension)]
    even_complement_pivot = ldl_check(block(even_complement, even))
    assert even_complement_pivot is not None
    even_lower_base = block([[arithmetic[i][j]-W[i][j]
                             for j in range(dimension)] for i in range(dimension)], even)
    mass = [1] + [2]*N

    def certify_lower(value):
        return ldl_check([[even_lower_base[i][j] -
                          (mass[i]*rat(value) if i == j else 0)
                          for j in range(N+1)] for i in range(N+1)])

    assert certify_lower(OLD_LOWER) is not None
    low, search_high = OLD_LOWER, UPPER
    for _ in range(14):
        trial = (low + search_high)/2
        if certify_lower(trial) is not None:
            low = trial
        else:
            search_high = trial
    lower_pivot = certify_lower(low)
    assert lower_pivot is not None and OLD_LOWER < low < UPPER < THRESHOLD
    projective_sq = (UPPER-low)/(THRESHOLD-low)
    # This is a substantive certification target, not a fitted error report.
    assert projective_sq < Fraction(1, 2500)
    output = {
        'scale': 'a=log(3)/2', 'N': N, 'M': M,
        'candidate_source': 'certify_prime3_refined.CANDIDATE, unchanged',
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'base_source_sha256': hashlib.sha256(Path(base.__file__).read_bytes()).hexdigest(),
        'ordinary_gram_sha256': hashlib.sha256(json.dumps(
            [[str(int(x)) for x in row] for row in ordinary],
            separators=(',', ':')).encode()).hexdigest(),
        'shells': shells, 'far_energy_lower': str(far_lower),
        'weighted_gram_error_upper': str(eta),
        'weighted_error_energy': str(error_w),
        'unweighted_second_jet_tail_upper': str(rem),
        'candidate_rayleigh_interval': str(ray),
        'ground_lower': str(low), 'candidate_upper': str(UPPER),
        'orthogonal_threshold': str(THRESHOLD),
        'projective_distance_sq_upper': str(projective_sq),
        'projective_distance_upper': '1/50',
        'pivot_displays': {'even_lower': lower_pivot,
                           'even_complement': even_complement_pivot,
                           'odd_complement': odd_pivot},
        'status': 'directed intervals and exact rational/integer checks passed',
        'formal_scope': 'Not a Lean run. Operator identification and the Neumann Gamma '
                        'mixture are paper bridges; the Lean companion proves the '
                        'Green-kernel completion and finite-mixture positivity.',
        'search_scope': 'Failed LDL attempts imply no spectral upper bound; the '
                        'reported lower bound is separately rechecked.'}
    path = ROOT / 'prime3_neumann_weighted_certificate.json'
    path.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps(output, indent=2), flush=True)
    return output


if __name__ == '__main__':
    run()
