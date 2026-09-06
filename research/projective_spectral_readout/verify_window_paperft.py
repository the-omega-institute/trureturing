"""Finite numerical regression for actual plus-sign Fourier/L2 identities.

This independently evaluates Lebesgue integrals with mpmath. It is not
extracted Lean, interval-certified quadrature, kernel validation or a proof of
uniform convergence. It reads no zeta zeros or external certificate verdicts.
Run: python verify_window_paperft.py --output window_paperft_verification.json
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import platform
import mpmath as mp

mp.mp.dps = 40
TOL = mp.mpf('1e-30')
COUNTS: Counter = Counter()
MAX_ERROR = mp.mpf(0)


def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


def close(x, y, label: str) -> None:
    global MAX_ERROR
    error = abs(x-y) / (1+abs(x)+abs(y))
    MAX_ERROR = max(MAX_ERROR, error)
    require(error < TOL, label)
    COUNTS[label] += 1


def integrate(f, a):
    return mp.quad(f, [-a, 0, a])


def inner(g, f, a):
    return integrate(lambda x: mp.conj(g(x))*f(x), a)


def ft(f, z, a):
    return integrate(lambda x: f(x)*mp.exp(1j*z*x), a)


def squared_norm(f, a):
    result = inner(f, f, a)
    require(abs(mp.im(result)) < TOL, 'norm square is real')
    return mp.re(result)


def run() -> dict:
    # Orthonormal polynomial coordinates serve as actual L2 window functions.
    for a in [mp.mpf(1)/3, mp.mpf(1), mp.mpf(7)/4]:
        phi0 = lambda x: 1/mp.sqrt(2*a)
        phi1 = lambda x: mp.sqrt(3/(2*a))*x/a
        phi2 = lambda x: mp.sqrt(5/(2*a))*(3*(x/a)**2-1)/2
        k = lambda x: mp.mpf(3)/5*phi0(x)+mp.mpf(4)/5*1j*phi1(x)
        w = lambda x: (mp.mpf(1)/7+mp.j/11)*phi2(x)
        delta = mp.mpf(1)/49+mp.mpf(1)/121
        f = lambda x: (1+2j)*phi0(x)+(mp.mpf(2)/3-1j)*phi1(x)+phi2(x)/5
        close(squared_norm(k,a),1,'unit_candidate')
        close(inner(k,w,a),0,'orthogonal_error')
        close(squared_norm(w,a),delta,'actual_error_energy')
        for z in [mp.mpc(0), mp.mpc(1)/3, mp.mpc(-2), mp.mpc(2,mp.mpf(1)/3),
                  mp.mpc(-1,-mp.mpf(2)/5),mp.mpc(0,mp.mpf(3)/4)]:
            kernel = lambda x: mp.conj(mp.exp(1j*z*x))
            F = ft(f,z,a)
            close(F,inner(kernel,f,a),'actual_fourier_inner_identity')
            E = squared_norm(kernel,a)
            analytic = 2*a if z.imag==0 else mp.sinh(2*a*z.imag)/z.imag
            close(E,analytic,'kernel_norm_integral')
            b=abs(z.imag)+mp.mpf(1)/10
            M=mp.sqrt(2*a)*mp.exp(b*a)
            require(E <= M*M+TOL,'strip kernel bound')
            COUNTS['kernel_strip_bounds'] += 1
            if z.imag==0:
                close(E,2*a,'real_frequency_normalization')
            K=ft(k,z,a)
            W=ft(w,z,a)
            g0=lambda x: kernel(x)-mp.conj(K)*k(x)
            d=E-abs(K)**2
            close(squared_norm(g0,a),d,'centered_kernel_energy')
            require(abs(W)**2 <= d*delta+TOL,'centered Fourier error')
            COUNTS['centered_fourier_error_bounds'] += 1
            require(abs(W) <= M*mp.sqrt(delta)+TOL,'strip Fourier error')
            COUNTS['fourier_strip_bounds'] += 1
            require(d>mp.mpf('1e-10'),'nondegenerate cancellation fixture')
            wc=lambda x: -K/d*g0(x)
            rho=abs(K)**2/d
            close(inner(k,wc,a),0,'cancelling_error_orthogonality')
            close(ft(lambda x: k(x)+wc(x),z,a),0,'actual_fourier_cancellation')
            close(squared_norm(wc,a),rho,'least_cancellation_energy')
            # Strictness is essential because the error ball is closed.
            for ratio in [mp.mpf(1)/2,mp.mpf(1),mp.mpf(2)]:
                budget=ratio*rho
                margin=(1+budget)*abs(K)**2-budget*E
                if ratio<1:
                    require(margin>0,'inside sharp margin')
                elif ratio==1:
                    close(margin,0,'closed_ball_boundary')
                else:
                    require(margin<0,'outside sharp margin')
                COUNTS['sharp_radius_thresholds'] += 1
        # Discontinuous L2 representatives require no smoothness or evenness.
        step=lambda x: mp.mpc(2,1) if x<0 else mp.mpc(-1,3)
        z=mp.mpc(mp.mpf(2)/3,mp.mpf(1)/5)
        kernel=lambda x: mp.conj(mp.exp(1j*z*x))
        close(ft(step,z,a),inner(kernel,step,a),'discontinuous_representative')

    # A varying-window model with growing scale c_j, not artificially vanishing c_j.
    # The family is synthetic, and these finitely many checks do not establish a limit.
    envelopes=[]
    for j in range(1,9):
        a=mp.mpf(j)/2
        b=mp.mpf(1)/4
        c=mp.exp(a/10)
        amplitude=mp.exp(-2*a)
        phi0=lambda x: 1/mp.sqrt(2*a)
        phi1=lambda x: mp.sqrt(3/(2*a))*x/a
        w=lambda x: amplitude*phi1(x)
        envelope=c*mp.sqrt(2*a)*mp.exp(b*a)*amplitude
        envelopes.append(envelope)
        for z in [mp.mpc(-2,-b),mp.mpc(0,b),mp.mpc(3,0)]:
            require(abs(c*ft(w,z,a))<=envelope+TOL,'varying window rate bound')
            COUNTS['varying_window_rate_bounds'] += 1
    require(all(envelopes[i+1]<envelopes[i] for i in range(len(envelopes)-1)),
            'sampled envelope decrease')

    # Negative controls detect the two sign errors and a normalization error.
    a=mp.mpf(7)/4;z=mp.mpc(mp.mpf(2)/3,mp.mpf(1)/5)
    f=lambda x: 1+(2+1j)*x+x*x/3
    correct=ft(f,z,a)
    wrong_sign=lambda x: mp.exp(1j*mp.conj(z)*x)
    wrong_conjugate=lambda x: mp.exp(1j*z*x)
    wrong=[inner(wrong_sign,f,a),inner(wrong_conjugate,f,a),correct/(2*a)]
    gaps=[abs(correct-v) for v in wrong]
    for gap in gaps:
        require(gap>mp.mpf('1e-6'),'mutated convention rejected')
        COUNTS['negative_controls_rejected'] += 1
    # A zero-length interval has zero norm; there is no normalized L2 candidate there.
    close(mp.quad(lambda x: 1,[0,0]),0,'zero_length_window')
    return {
        'status':'all finite numerical regressions passed; not Lean or interval certification',
        'python':platform.python_version(),'mpmath':mp.__version__,'precision_digits':mp.mp.dps,
        'counts':dict(COUNTS),'maximum_normalized_identity_error':mp.nstr(MAX_ERROR,15),
        'sampled_varying_window_envelopes':[mp.nstr(x,15) for x in envelopes],
        'negative_control_gaps':[mp.nstr(x,15) for x in gaps],
        'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope':'actual plus-sign Fourier integrals on finite Lebesgue windows and synthetic error families',
        'not_verified':['Lean elaboration/kernel','Scribe emission','Arithmetic Weil full-domain coercivity',
                        'Actual all-scale Rayleigh rate','Convergence of any actual candidate family to Xi']}


def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=Path(__file__).with_name('window_paperft_verification.json'))
    args=ap.parse_args()
    report=run()
    text=json.dumps(report,indent=2)+'\n'
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(text)
    print(text)


if __name__=='__main__':
    main()
