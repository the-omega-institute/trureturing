"""Certified complex Fourier readout of the actual c=3 Weil ground line.

Reuses the pinned arithmetic primitive implementation, fixed dyadic candidate,
and independently proved Neumann/odd-complement form estimates of PR #5602.
All finite endpoint sums for the directional readout use exact binary integer
accumulators. The entire uncomputed dual tail has an analytic M^-2 enclosure.
A Rouché comparison with an affine function counts a simple real zero in an
explicit complex disk. No zeta zeros, Xi evaluations or eigensolver are inputs.

The conclusions use the paper Fourier/closed-form and variational bridges
stated in RH_RESEARCH_LANE_THEORY.md. This is not a Lean kernel replay.
"""
from __future__ import annotations
import hashlib
import importlib.util
import json
import math
import platform
import time
from fractions import Fraction
from pathlib import Path
import numpy as np
from mpmath import iv

if not __debug__:
    raise RuntimeError('Run without -O: assertions are part of verification.')
ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'certify_prime3_refined.py'
BASE_HASH = '8bb067fc5499b0f2e1e48836e7a82237a15504109f82a856c72478d1096d69d0'
if hashlib.sha256(BASE.read_bytes()).hexdigest() != BASE_HASH:
    raise RuntimeError('Pinned arithmetic dependency hash mismatch.')
spec = importlib.util.spec_from_file_location('weil_arithmetic', BASE)
if spec is None or spec.loader is None:
    raise ImportError('Cannot load pinned arithmetic primitives.')
b = importlib.util.module_from_spec(spec)
spec.loader.exec_module(b)
iv.dps = 55
N, M, BITS, ERROR_BITS = 64, 32768, 44, 60
ELL, UPPER, THRESHOLD = Fraction(11, 200000000), Fraction(560909, 10**13), Fraction(1, 200000)
CENTER, RADIUS = Fraction(2827, 200), Fraction(1, 250)


def rat(x):
    x = Fraction(x)
    return iv.mpf(x.numerator) / x.denominator


def binary_sum(values):
    """Exact sum of finite binary64 endpoints, rounded only into iv at the end.

    The decoded integer significand, sign and power of two are exact. Python
    integers cannot overflow; subnormals and zeros are included. No floating
    reduction result is accepted as an enclosure.
    """
    x = np.ascontiguousarray(values, dtype=np.float64).ravel()
    if not np.all(np.isfinite(x)):
        raise ArithmeticError('Non-finite endpoint in exact accumulator.')
    u = x.view(np.uint64)
    ef = ((u >> np.uint64(52)) & np.uint64(2047)).astype(np.int64)
    mant = (u & np.uint64((1 << 52) - 1)).astype(np.int64)
    mant = mant + np.where(ef != 0, 1 << 52, 0).astype(np.int64)
    mant = np.where((u >> np.uint64(63)) != 0, -mant, mant)
    ex = np.where(ef != 0, ef - 1075, -1074)
    keep = mant != 0
    if not np.any(keep):
        return iv.mpf(0)
    mant, ex = mant[keep], ex[keep]
    emin = int(np.min(ex))
    acc = sum(int(v) << (int(e) - emin) for v, e in zip(mant, ex))
    return iv.mpf(acc) * iv.mpf(2)**emin


def interval_sum(values):
    lo, hi = binary_sum(values.lo), binary_sum(values.hi)
    return iv.mpf([lo.a, hi.b])


def accumulator_regression():
    tests = [[1., 2.**-53, -1.], [2.**100, -2.**100, 3.],
             [0., -0., np.nextafter(0., 1.), -np.nextafter(0., 1.)],
             [np.nextafter(0., 1.), np.nextafter(0., 1.)]]
    rng = np.random.default_rng(20260906)
    tests += [np.ldexp(rng.uniform(-1, 1, 47), rng.integers(-200, 200, 47)) for _ in range(30)]
    for x in tests:
        exact = sum((Fraction.from_float(float(t)) for t in x), Fraction(0))
        got = binary_sum(x)
        # Endpoint comparison against the exact rational, with more precision.
        with_precision = iv.dps
        iv.dps = 300
        expected = rat(exact)
        assert bool(got.a <= expected.a) and bool(expected.b <= got.b)
        iv.dps = with_precision
    return len(tests)


def energy_floor(n):
    L = iv.ln(3)
    analytic = iv.ln(iv.mpf(n)/L) - L/(iv.pi*n) - iv.ln(2)/iv.sqrt(2)
    floor = Fraction(math.floor(float(analytic.a)*2**20)-1, 2**20)
    assert bool(rat(floor) < analytic) and floor > THRESHOLD
    return floor


def ldl(A, name):
    d = len(A)
    low = [[iv.mpf(0) for _ in range(d)] for _ in range(d)]
    piv = []
    for j in range(d):
        low[j][j] = iv.mpf(1)
        v = A[j][j] - sum((low[j][k]**2*piv[k] for k in range(j)), iv.mpf(0))
        if not bool(v > 0):
            raise ArithmeticError(f'{name}: positivity not certified at pivot {j}: {v}')
        piv.append(v)
        for i in range(j+1, d):
            low[i][j] = (A[i][j]-sum((low[i][k]*low[j][k]*piv[k]
                                      for k in range(j)), iv.mpf(0)))/v
    print(name, 'positive; minimum pivot lower display', min(float(v.a) for v in piv), flush=True)
    return low, piv


def inverse_energy(factor, h):
    low, piv = factor
    y = []
    for i in range(len(h)):
        y.append(h[i]-sum((low[i][j]*y[j] for j in range(i)), iv.mpc(0)))
    return sum((abs(y[i])**2/piv[i] for i in range(len(h))), iv.mpf(0))


def run():
    start = time.time()
    regressions = accumulator_regression()
    L, pi = iv.ln(3), iv.pi
    a = L/2
    assert bool(L < 2*iv.ln(2))
    assert bool(2*((iv.sqrt(3)+1/iv.sqrt(3))/2)+iv.ln(2)/iv.sqrt(2) < 3)
    ns, ms = np.arange(-N, N+1, dtype=np.int64), np.arange(N+1, M+1, dtype=np.int64)
    d = len(ns)
    sig = b.symbol_array(np.arange(1, M+1))
    slo = np.r_[-sig.hi[:N][::-1], 0, sig.lo[:N]]
    shi = np.r_[-sig.lo[:N][::-1], 0, sig.hi[:N]]
    C = (b.I(slo[None,:], shi[None,:])-b.I(sig.lo[N:,None], sig.hi[N:,None]))/(
        b.PI*b.I(ms[:,None]-ns[None,:]))
    assert np.all(np.isfinite(C.lo)) and np.all(np.isfinite(C.hi))
    quant = np.rint(C.mid()*2**BITS)
    assert np.max(np.abs(quant)) < 2**53
    X = quant.astype(np.int64)
    qfloat = np.ldexp(X.astype(float), -BITS)
    er = np.maximum(b.up(C.hi-qfloat), b.up(qfloat-C.lo))
    assert np.all(np.isfinite(er)) and np.all(er >= 0)
    rr = np.ceil(np.ldexp(er, ERROR_BITS))
    assert np.max(rr) < 2**53
    radius = rr.astype(np.int64)
    assert np.all(np.ldexp(radius.astype(float), -ERROR_BITS) >= er)
    assert 2*radius.size*int(np.max(radius))**2 < 2**63
    WG = [[Fraction(0) for _ in range(d)] for _ in range(d)]
    G = np.zeros((d,d), dtype=object)
    invlo, invhi = np.empty(len(ms)), np.empty(len(ms))
    tracew, errorw, e0 = Fraction(0), Fraction(0), Fraction(0)
    shells = []
    first = N+1
    while first <= M:
        last = min(2*(first-1), M)
        i, j = first-N-1, last-N
        gp = b.exact_gram(X[i:j]); g = gp+gp[::-1,::-1]; G += g
        floor = energy_floor(first); inv = 1/(floor-THRESHOLD)
        er2 = Fraction(2*int(np.sum(radius[i:j]**2, dtype=np.int64)), 2**(2*ERROR_BITS))
        e0 += er2; errorw += inv*er2
        tracew += inv*Fraction(sum(int(g[h,h]) for h in range(d)), 2**(2*BITS))
        for h in range(d):
            for k in range(h+1):
                WG[h][k] += inv*Fraction(int(g[h,k]), 2**(2*BITS))
        ii = b.outer_iv(rat(inv)); invlo[i:j], invhi[i:j] = ii.lo, ii.hi
        shells.append({'first':first, 'last':last, 'energy_lower':str(floor), 'inverse_weight':str(inv)})
        first = last+1
    assert np.array_equal(G, G[::-1,::-1])
    gh = hashlib.sha256(json.dumps([[str(int(t)) for t in row] for row in G],separators=(',',':')).encode()).hexdigest()
    assert gh == '7f4e1049624807432efe96a68fe63babbc1c3bd37f2d40600a4cddadbddb85a9'
    eta = Fraction(4, 152587890625)
    assert errorw < eta and 4*tracew*errorw < (eta-errorw)**2
    eta0 = Fraction(1, 10**10)
    tr0 = Fraction(sum(int(G[i,i]) for i in range(d)), 2**(2*BITS))
    assert e0 < eta0 and 4*tr0*e0 < (eta0-e0)**2
    rem = Fraction(9, 10**13)
    assert bool(16*9*N**4*d/(pi**2*(1-iv.mpf(N)/M)**2*M**5) < rat(rem))
    far = energy_floor(M+1)-THRESHOLD
    assert far > 0
    # Recheck the original all-parity bound used for the odd sector.
    eps, R = 4/(3*pi**2), pi*N/(4*a)
    gamma0 = -iv.euler-pi/2-3*iv.ln(2)-iv.ln(pi)
    t = R/2
    inc = sum((t*t/((iv.mpf(j)+iv.mpf(1)/4)*((iv.mpf(j)+iv.mpf(1)/4)**2+t*t))
               for j in range(512)), iv.mpf(0))
    debt = 2*((iv.sqrt(3)-1/iv.sqrt(3))/2-a)
    old_beta = (1-eps)*(gamma0+inc)+eps*gamma0-iv.ln(2)/iv.sqrt(2)-debt
    assert bool(old_beta > 1)
    symbols = [iv.mpf([float(slo[i]),float(shi[i])]) for i in range(d)]
    AA = [[iv.mpf(0) for _ in range(d)] for _ in range(d)]
    GG = [[iv.mpf(0) for _ in range(d)] for _ in range(d)]
    WW = [[iv.mpf(0) for _ in range(d)] for _ in range(d)]
    for i,ni in enumerate(ns):
        AA[i][i] = b.diagonal_iv(int(ni))
        for j in range(i):
            AA[i][j] = AA[j][i] = (symbols[i]-symbols[j])/(pi*int(ns[j]-ni))
        for j in range(i+1):
            tail = 8/pi**2*((9+symbols[i]*symbols[j])/M + int(ni)*int(ns[j])*(9+symbols[i]*symbols[j])/M**3)
            g = iv.mpf(int(G[i,j]))/2**(2*BITS)+tail
            w = rat(WG[i][j])+tail/rat(far)
            if i == j:
                g += rat(eta0+rem); w += rat(eta+rem/far)
            GG[i][j] = GG[j][i] = g
            WW[i][j] = WW[j][i] = w
    vfull = [iv.mpf(int(t))/2**40 for t in b.CANDIDATE]
    assert b.CANDIDATE == tuple(reversed(b.CANDIDATE)) and len(vfull) == d
    norm2 = sum((v*v for v in vfull),iv.mpf(0)); assert bool(norm2 > 0)
    mu = sum((vfull[i]*AA[i][j]*vfull[j] for i in range(d) for j in range(d)),iv.mpf(0))/norm2
    assert bool(mu < rat(UPPER)) and ELL < UPPER < THRESHOLD
    even = [[(N,1)]]+[[(N+j,1),(N-j,1)] for j in range(1,N+1)]
    odd = [[(N+j,1),(N-j,-1)] for j in range(1,N+1)]
    def block(A,basis):
        return [[sum((sx*sy*A[i][j] for i,sx in x for j,sy in y),iv.mpf(0))
                 for y in basis] for x in basis]
    odd_s = [[AA[i][j]-GG[i][j]/(1-rat(THRESHOLD))-(rat(THRESHOLD) if i==j else 0)
              for j in range(d)] for i in range(d)]
    odd_fac = ldl(block(odd_s,odd),'odd full-space threshold')
    Se = block([[AA[i][j]-WW[i][j]-(rat(ELL) if i==j else 0)
                 for j in range(d)] for i in range(d)],even)
    ell_fac = ldl(Se,'even full-space ground lower')
    comp = block([[AA[i][j]-WW[i][j]+vfull[i]*vfull[j]-(rat(THRESHOLD) if i==j else 0)
                   for j in range(d)] for i in range(d)],even)
    comp_fac = ldl(comp,'even candidate-orthogonal threshold')
    # Exact nonorthonormal basis of k-perp: x0=-sum_i p_i*x_i, p_i=2*v_i/v0.
    vf = [Fraction(int(t),2**40) for t in b.CANDIDATE[N:]]
    assert vf[0] != 0
    p = [rat(2*vf[i]/vf[0]) for i in range(1,N+1)]
    J = [[Se[i+1][j+1]-p[i]*Se[0][j+1]-p[j]*Se[i+1][0]+p[i]*p[j]*Se[0][0]
          for j in range(N)] for i in range(N)]
    jf = ldl(J,'constrained directional Schur matrix')
    projective_sq = (UPPER-ELL)/(THRESHOLD-ELL)
    assert projective_sq < Fraction(1,2500)
    print('arithmetic enclosure and complete Schur checks passed',flush=True)

    # All z in the complex square containing the closed target disk.
    zr = rat(CENTER)+rat(RADIUS)*iv.mpf([-1,1])
    zi = rat(RADIUS)*iv.mpf([-1,1])
    z = iv.mpc(zr,zi)
    assert bool(L*abs(z) < pi*N)
    w = z*L/(2*pi)
    wx,wy = b.outer_iv(w.real),b.outer_iv(w.imag)
    w2r,w2i = b.cmul((wx,wy),(wx,wy))
    denr,deni = b.I(ms*ms)-w2r,-w2i
    deninv = b.cinv(denr,deni)
    factor = -L*iv.sqrt(L)/pi**2 * z*iv.sin(a*z)
    fr,fi = b.outer_iv(factor.real),b.outer_iv(factor.imag)
    fqr,fqi = b.cmul((fr,fi),deninv)
    invD = b.I(invlo,invhi)
    pairlo = np.column_stack((C.lo[:,N],b.down(C.lo[:,N+1:]+C.lo[:,N-1::-1])))
    pairhi = np.column_stack((C.hi[:,N],b.up(C.hi[:,N+1:]+C.hi[:,N-1::-1])))
    Cp = b.I(pairlo,pairhi)
    realterms = Cp*b.I(fqr.lo[:,None],fqr.hi[:,None])*b.I(invlo[:,None],invhi[:,None])
    imagterms = Cp*b.I(fqi.lo[:,None],fqi.hi[:,None])*b.I(invlo[:,None],invhi[:,None])
    highnorm = interval_sum((fqr*fqr+fqi*fqi)*invD/2)
    zsin = abs(z*iv.sin(a*z))
    highnorm += (8*L**3/(27*pi**4*M**3*rat(far)))*zsin**2
    dual = []
    tail_displays = []
    for n in range(N+1):
        tr = interval_sum(b.I(realterms.lo[:,n],realterms.hi[:,n]))
        ti = interval_sum(b.I(imagterms.lo[:,n],imagterms.hi[:,n]))
        mult = 1 if n == 0 else 2
        # Arithmetic symbol budget B=3, and the full far energy is >=far.
        bound = 2*mult*3*L*iv.sqrt(L)*zsin/(3*pi**3*rat(far)*M*(M-n))
        tail_displays.append(str(bound))
        dual.append(iv.mpc(tr+iv.mpf([-1,1])*bound,ti+iv.mpf([-1,1])*bound))
    fP = [2*iv.sin(a*z)/(iv.sqrt(L)*z)] + [4*z*iv.sin(a*z)/(iv.sqrt(L)*(z*z-(2*pi*n/L)**2)) for n in range(1,N+1)]
    corrected = [fP[n]-dual[n] for n in range(N+1)]
    h = [corrected[i+1]-p[i]*corrected[0] for i in range(N)]
    sensitivity = inverse_energy(jf,h)+highnorm
    error = iv.sqrt(rat(UPPER-ELL)*sensitivity)

    # Independent affine Rouché comparator from the explicit finite candidate.
    t0 = rat(CENTER); sn,cs = iv.sin(a*t0),iv.cos(a*t0)
    f0 = 2*sn/(iv.sqrt(L)*t0)
    df0 = 2*(a*t0*cs-sn)/(iv.sqrt(L)*t0**2)
    fs,dfs = [f0],[df0]
    for n in range(1,N+1):
        dn = t0**2-(2*pi*n/L)**2
        fs.append(4*t0*sn/(iv.sqrt(L)*dn))
        dfs.append(4*((sn+a*t0*cs)*dn-2*t0**2*sn)/(iv.sqrt(L)*dn**2))
    K0 = sum((rat(vf[n])*fs[n] for n in range(N+1)),iv.mpf(0))/iv.sqrt(norm2)
    K1 = sum((rat(vf[n])*dfs[n] for n in range(N+1)),iv.mpf(0))/iv.sqrt(norm2)
    assert bool(K1 > 0)
    affine_floor = rat(RADIUS)*abs(K1)-abs(K0)
    # ||k||=1; integral_I x^4 dx=L^5/80. Complex disk Taylor remainder.
    taylor = rat(RADIUS)**2/2*iv.exp(a*rat(RADIUS))*iv.sqrt(L**5/80)
    assert bool(affine_floor > 0)
    assert bool(error+taylor < affine_floor), (error,taylor,affine_floor)
    print('complex-disk Rouche strict inequality passed',flush=True)
    out = {
        'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'arithmetic_dependency_sha256':BASE_HASH,'exact_gram_sha256':gh,
        'scale':'a=log(3)/2','N':N,'M':M,'candidate':'unchanged dyadic vector from pinned arithmetic source',
        'ground_lower':str(ELL),'candidate_upper':str(UPPER),'orthogonal_threshold':str(THRESHOLD),
        'candidate_rayleigh_interval':str(mu),'projective_distance_sq_upper':str(projective_sq),
        'weighted_gram_error':str(eta),'unweighted_gram_error':str(eta0),
        'second_jet_scalar_tail':str(rem),'shells':shells,'far_energy_after_shift':str(far),
        'exact_binary_accumulator_regressions':regressions,
        'disk_center':str(CENTER),'disk_radius':str(RADIUS),
        'low_constrained_inverse_energy':str(inverse_energy(jf,h)),
        'entire_high_observation_energy':str(highnorm),'uniform_sensitivity_interval':str(sensitivity),
        'uniform_ground_fourier_error':str(error),'largest_dual_tail_component_display':max(float(iv.mpf(s).b) for s in tail_displays),
        'candidate_value_at_center':str(K0),'candidate_derivative_at_center':str(K1),
        'affine_boundary_floor':str(affine_floor),'candidate_taylor_remainder':str(taylor),
        'rouche_strict_margin':str(affine_floor-error-taylor),
        'zero_count':'Exactly one zero, counted with multiplicity, in each disk around +/-2827/200 of radius 1/250. The zero is real and simple by evenness, conjugation and uniqueness.',
        'scope':'Actual fixed-window projectively normalized ground transform via paper operator/domain and Schur bridges. Not a Xi zero certificate, not an unbounded-scale limit, and not a Lean kernel replay.',
        'python':platform.python_version(),'numpy':np.__version__,'elapsed_seconds':time.time()-start,
        'status':'directed interval, exact integer Gram, exact endpoint sums and strict Rouche inequality passed'}
    path=ROOT/'prime3_directional_certificate.json';path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2),flush=True)

if __name__ == '__main__':
    run()
