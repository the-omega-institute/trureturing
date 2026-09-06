"""Independent exact/numerical regression for PR #5882. This is not a Lean run.

The optional --prime3-certificate input is a JSON from PR #5602. Reading its
numbers verifies only parameter arithmetic; it does NOT verify its interval
LDL, infinite tail, actual operator domain, or arithmetic coercivity.

Run: python verify_projective_readout.py --output verification.json
Dependencies: Python 3.10+, numpy, sympy. No network or zeta-zero data needed.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import platform
import random
import numpy as np
import sympy as sp

SEED = 20260906
SOURCE_PIN = '4ddc8bf4cc75b3c7581ec5c2a1dccca7f91007a3'
CERT_BLOB = 'd55cfc86e16019d22aa7c4e4ca758c01236f7b72'
CANDIDATE_SOURCE_BLOB = 'a8690fc54e79d1a80b12aeca2ce4837bb9e585af'
# Exact integer coefficients retrieved from the pinned verifier, with reflection
# reconstructed literally; these are a finite candidate, not an actual eigenmode.
CANDIDATE_LEFT = (
  1884327,1949881,2454431,1955838,2267166,2628844,2019817,2725995,
  2666928,2258922,3191558,2627834,2740665,3535958,2652877,3431115,
  3691004,2914967,4199523,3702151,3543262,4868979,3743722,4552854,
  5304731,4078317,5814371,5510634,4965730,7089643,5694160,6550526,
  8139061,6265021,8774613,8880841,7751943,11365368,9561858,10650784,
  13940578,10893066,15245277,16256238,14112283,21456639,18619811,20944288,
  28759160,22515646,33301119,36045767,31375026,51306542,40139614,48028821,
  55055748,16558565,-14587791,-293594608,-638883816,-8057897274,-64380122561,494208169232)
CANDIDATE_CENTER = -843813904619


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def inner(x: sp.Matrix, y: sp.Matrix) -> sp.Expr:
    return sp.expand((x.conjugate().T * y)[0])


def n2(x: sp.Matrix) -> sp.Expr:
    return inner(x, x)


def exact_equal(a: sp.Expr | sp.Matrix, b: sp.Expr | sp.Matrix, message: str) -> None:
    if isinstance(a, sp.MatrixBase):
        require(all(sp.expand(z) == 0 for z in a-b), message)
    else:
        require(sp.simplify(a-b) == 0, message)


def run(certificate: Path | None = None) -> dict:
    rng = random.Random(SEED)
    nrng = np.random.default_rng(SEED)
    counts: Counter = Counter()
    R, I = sp.Rational, sp.I
    k = sp.Matrix([R(3,5), R(4,5)*I])
    V = sp.Matrix([[R(3,5), -R(4,5)], [R(4,5)*I, R(3,5)*I]])
    exact_equal(V.conjugate().T*V, sp.eye(2), 'exact unitary')

    # Actual Hermitian eigenproblems, with a strictly positive rank-one excess.
    # The projective budget is attained exactly, even after phase and scale changes.
    for j in range(36):
        t = R(rng.randrange(-4,5),10) + I*R(rng.randrange(-4,5),10)
        ell, s = R(j-17,9), R(j+2,11)
        v = sp.Matrix([sp.conjugate(t),1])
        A0 = ell*sp.eye(2)+s*v*v.conjugate().T
        A = V*A0*V.conjugate().T
        c = R(j+1,7)+I*R(3-j,13)
        u = c*V*sp.Matrix([1,-t])
        alpha = inner(k,u)
        w = u/alpha-k
        mu, threshold = inner(k,A*k), ell+s
        delta = sp.simplify((mu-ell)/(threshold-ell))
        exact_equal(A.conjugate().T,A,'Hermitian action')
        exact_equal(A*u,ell*u,'actual eigen equation')
        exact_equal(inner(k,w),0,'actual projective orthogonality')
        exact_equal(inner(w,A*w),ell*n2(w)+mu-ell,'derived energy identity')
        exact_equal(n2(w),delta,'attained projective budget')
        require(0 <= delta < 1,'valid strict gap and budget')
        counts['exact_hermitian_eigenproblems'] += 1
        counts['exact_projective_identities'] += 5

        # Nonzero complex readout representers and explicit least-energy cancellation.
        for z in range(3):
            g = sp.Matrix([R(j+z+1,11)+I*R(z+2,9), R(z+1,5)+I*R(j+2,17)])
            g0 = g-inner(k,g)*k
            b, d = inner(g,k), n2(g0)
            require(d>0,'nondegenerate readout component')
            wc = -b/d*g0
            exact_equal(inner(k,wc),0,'cancelling error orthogonal')
            exact_equal(inner(g,k+wc),0,'actual readout cancellation')
            rho = sp.simplify(sp.conjugate(b)*b/d)
            exact_equal(n2(wc),rho,'exact least cancellation energy')
            exact_equal(d,n2(g)-sp.conjugate(b)*b,'projected readout norm')
            lhs = sp.simplify(sp.conjugate(inner(g,w))*inner(g,w))
            require(lhs<=d*delta,'centered readout bound')
            for budget in [rho/2, rho, rho+R(1,19)]:
                margin = sp.simplify(d*budget < sp.conjugate(b)*b)
                require(bool(margin) == bool(budget<rho),'sharp strict threshold')
                if not bool(margin):
                    require(n2(wc)<=budget,'actual failure witness inside closed ball')
                counts['exact_radius_threshold_checks'] += 1
            counts['exact_readout_cancellation_witnesses'] += 1
            counts['exact_readout_identities'] += 4

    # Degenerate readouts: g=0, g parallel to k, and zero overlap with k.
    for g in [sp.zeros(2,1), (2+3*I)*k, V*sp.Matrix([0,1])]:
        b, g0 = inner(g,k), g-inner(k,g)*k
        for delta in [R(0),R(1,100),R(1)]:
            d=n2(g0); threshold=bool(d*delta < sp.conjugate(b)*b)
            if d==0:
                require(threshold == (b!=0),'parallel/zero readout condition')
            else:
                wc=-b/d*g0
                require(threshold == (n2(wc)>delta),'zero-overlap condition')
            counts['exact_degenerate_ball_checks'] += 1

    # Actual two-state balanced systems and actual one-state reduced trajectories.
    for j in range(18):
        eta=F(1,2**j) if j<15 else F(j-13)
        eps=min(F(1),15*eta/64)
        a=[F(1,2),F(1,4)]; b=[F(1),eps]; d=[F(4,3),16*eps*eps/15]
        require(0<eps<=1 and 32*eps*eps/15<eta,'construct eps for every positive eta sample')
        require(d[0]>=d[1],'genuine retained larger weight')
        for h in range(2):
            require(a[h]**2*d[h]+b[h]**2==d[h],'both exact Stein equations')
            require(b[h]*(1/b[h])==1,'actual input/output inverse')
            counts['exact_stein_and_port_checks'] += 2
        require((1-4*a[0])*(1-4*a[1])==0 and 1-4*a[0]==-1,'fixed lost determinant root')
        x=[F(0),F(0)]; z=F(0); err=F(0); inp=F(0)
        for N in range(28):
            require(err <= (32*eps*eps/15)**2*inp,'actual finite-window reduction bound')
            counts['exact_forced_window_bounds'] += 1
            u=[F(rng.randrange(-9,10),7),F(rng.randrange(-9,10),11)]
            y=[b[h]*x[h] for h in range(2)]; yr=[z,F(0)]
            err+=sum((y[h]-yr[h])**2 for h in range(2))
            inp+=sum(t*t for t in u)
            x=[a[h]*x[h]+b[h]*u[h] for h in range(2)]
            z=a[0]*z+u[0]
        counts['exact_determinant_loss_systems'] += 1

    # Random finite-dimensional complex systems. Floating arithmetic is supplemental.
    max_error=0.0
    for j in range(60):
        n=3+j%5
        X=nrng.normal(size=(n,n))+1j*nrng.normal(size=(n,n))
        U=np.linalg.qr(X)[0]
        eigs=np.r_[0.,np.linspace(1.,3.,n-1)]+j/17.
        A=(U*eigs)@U.conj().T; u=(2.+3j)*U[:,0]
        k=U[:,0]+.08*U[:,1]+.03j*U[:,-1];k/=np.linalg.norm(k)
        W=np.linalg.qr(np.column_stack((k,U)))[0][:,1:]
        T=float(np.linalg.eigvalsh(W.conj().T@A@W)[0]);mu=float(np.vdot(k,A@k).real)
        lower=eigs[0]-.001;upper=mu+.001
        require(upper<T,'numeric gap')
        delta=(upper-lower)/(T-lower);alpha=np.vdot(k,u);w=u/alpha-k
        err=float(np.vdot(w,w).real)
        require(err<=delta+1e-12,'numeric projective enclosure')
        energy=float(np.vdot(w,A@w).real)
        max_error=max(max_error,abs(energy-eigs[0]*err-mu+eigs[0]),abs(np.vdot(k,w)))
        for _ in range(4):
            g=nrng.normal(size=n)+1j*nrng.normal(size=n)
            b=np.vdot(g,k);g0=g-np.vdot(k,g)*k;d=float(np.vdot(g0,g0).real)
            wc=-b/d*g0;rho=abs(b)**2/d
            max_error=max(max_error,abs(np.vdot(g,k+wc)),abs(np.vdot(k,wc)),abs(np.vdot(wc,wc).real-rho))
            require(abs(np.vdot(g,w))**2<=d*delta+1e-10,'numeric centered readout bound')
            counts['numeric_centered_readout_checks'] += 1
        counts['numeric_complex_eigenproblems'] += 1

    # Exact arithmetic consumption of the real, separately produced certificate.
    fields={'ground_lower':'103/2000000000','candidate_upper':'560909/10000000000000',
            'orthogonal_threshold':'1/200000'}
    external_hash=None
    if certificate is not None:
        raw=certificate.read_bytes();external_hash=hashlib.sha256(raw).hexdigest()
        given=json.loads(raw)
        for key,value in fields.items():
            require(F(given[key])==F(value),f'pinned parameter mismatch: {key}')
    lower,upper,T=(F(fields[k]) for k in ['ground_lower','candidate_upper','orthogonal_threshold'])
    delta=(upper-lower)/(T-lower);angle=delta/(1+delta)
    require(delta==F(15303,16495000) and delta<F(61,2000)**2,'prime3 budget arithmetic')
    require(angle==F(15303,16510303),'prime3 exact angle threshold')
    v=CANDIDATE_LEFT+(CANDIDATE_CENTER,)+CANDIDATE_LEFT[::-1]
    require(len(v)==129 and v==v[::-1],'pinned finite candidate symmetry')
    total=sum(c*c for c in v)
    accepted=[i-64 for i,c in enumerate(v) if 15303*total < 16510303*c*c]
    require(accepted==[-2,-1,0,1,2],'exact finite-coordinate readout margins')
    counts['prime3_candidate_coordinate_thresholds']=len(v)
    report={
      'status':'all independent regressions passed; no Lean or Scribe execution',
      'seed':SEED,'python':platform.python_version(),'numpy':np.__version__,'sympy':sp.__version__,
      'counts':dict(counts),'maximum_numeric_identity_error':max_error,
      'prime3':{'source_commit':SOURCE_PIN,'certificate_git_blob':CERT_BLOB,'candidate_source_git_blob':CANDIDATE_SOURCE_BLOB,
        'external_json_sha256':external_hash,'delta':str(delta),'radius_upper':'61/2000',
        'normalized_overlap_squared_threshold':str(angle),
        'candidate_integer_norm_squared':str(total),
        'candidate_coordinate_readouts_passing_margin':accepted,
        'scope':'exact arithmetic for the pinned finite candidate and conditional Hilbert readout certificate; not arithmetic operator/domain verification'},
      'nonclaims':['No Lean kernel or Scribe check','No replay of PR5602 interval verifier',
        'No verification of the actual infinite Weil domain or form coercivity',
        'No contour zero count or Xi scale limit','No novelty or priority determination']}
    report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return report


def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--prime3-certificate',type=Path)
    ap.add_argument('--output',type=Path,default=Path(__file__).with_name('verification.json'))
    args=ap.parse_args()
    report=run(args.prime3_certificate)
    text=json.dumps(report,indent=2,ensure_ascii=False)+'\n'
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(text)
    print(text)

if __name__=='__main__':
    main()
