#!/usr/bin/env python3
"""Finite diagnostics only. This is not Lean elaboration or a kernel proof.
Run with Python 3, NumPy and SciPy. Writes continuation_checks.json beside itself.
"""
from __future__ import annotations
from pathlib import Path
import hashlib, json, platform
import numpy as np
import scipy
import math
import mpmath as mp
from scipy.linalg import expm

ROOT = Path(__file__).resolve().parents[3]
RNG = np.random.default_rng(88992026)
COUNTS: dict[str,int] = {}
ERRORS: dict[str,float] = {}

def check(group: str, test: bool) -> None:
    if not bool(test):
        raise AssertionError(group)
    COUNTS[group] = COUNTS.get(group,0) + 1

def close(group: str, left, right, tol: float=2e-10) -> None:
    err = float(np.max(np.abs(np.asarray(left)-np.asarray(right))))
    ERRORS[group] = max(ERRORS.get(group,0),err)
    check(group, err <= tol)

def unitary(n: int):
    return np.linalg.qr(RNG.normal(size=(n,n))+1j*RNG.normal(size=(n,n)))[0]

def spectral(u, a):
    return (u*np.asarray(a))@u.conj().T

def matrix_log(a):
    v,u=np.linalg.eigh(a)
    return spectral(u,np.log(v))

def klein_checks():
    for n in range(2,9):
        for repeat in range(30):
            u,v=unitary(n),unitary(n)
            a=RNG.uniform(0.01,2,n)
            if repeat%2 == 0: a[0]=0
            b=RNG.uniform(0.02,2,n)
            loga=np.zeros_like(a); nz=a>0; loga[nz]=np.log(a[nz])
            A,B=spectral(u,a),spectral(v,b)
            logA,logB=spectral(u,loga),spectral(v,np.log(b))
            w=np.abs(u.conj().T@v)**2
            close('overlap_row_sum',w.sum(axis=1),1)
            close('overlap_col_sum',w.sum(axis=0),1)
            cross=np.trace(A@logB).real
            close('cross_trace',cross,np.sum(a[:,None]*np.log(b)[None,:]*w))
            gap=np.trace(A@(logA-logB)-A+B).real
            scalar=a[:,None]*loga[:,None]-a[:,None]*np.log(b)[None,:]-a[:,None]+b[None,:]
            close('klein_decomposition',gap,np.sum(w*scalar))
            check('klein_nonnegative',gap >= -2e-11)
            an,bn=a/a.sum(),b/b.sum()
            lan=np.zeros_like(an); nn=an>0; lan[nn]=np.log(an[nn])
            rho,sigma=spectral(u,an),spectral(v,bn)
            D=np.trace(rho@(spectral(u,lan)-spectral(v,np.log(bn)))).real
            check('density_relative_entropy',D>=-2e-11)
    # The legacy totalized log expression is not valid without support inclusion.
    A=np.diag([1.,0.]); B=np.diag([0.,1.])
    close('unsupported_totalized_boundary',np.trace(A@(np.zeros((2,2))-np.zeros((2,2)))),0)
    # The physical Umegaki divergence for this pair is infinite, deliberately not tested as finite.

def gibbs_checks():
    for n in range(2,9):
        for repeat in range(20):
            H=spectral(unitary(n),RNG.normal(size=n))
            K=H+spectral(unitary(n),RNG.normal(size=n)/4)
            norm=float(np.linalg.norm(H-K,2))
            zH,zK=np.trace(expm(H)).real,np.trace(expm(K)).real
            check('pressure_lipschitz',abs(np.log(zH)-np.log(zK))<=norm+1e-11)
            u=unitary(n); r=RNG.uniform(0.01,1,n)
            if repeat%2==0: r[0]=0
            r/=r.sum(); lr=np.zeros(n); nz=r>0; lr[nz]=np.log(r[nz])
            rho=spectral(u,r); entropy=-np.sum(r*lr)
            E=np.trace((H-K)@rho).real
            check('expectation_norm',abs(E)<=norm+1e-11)
            beta=float(RNG.uniform(0.03,4))
            logZH=np.log(np.trace(expm(-beta*H)).real)
            logZK=np.log(np.trace(expm(-beta*K)).real)
            fH,fK=-logZH/beta,-logZK/beta
            check('free_energy_stability',abs(fH-fK)<=norm+1e-11)
            logR=spectral(u,lr)
            GH=np.trace(rho@(logR+beta*H+logZH*np.eye(n))).real/beta
            GK=np.trace(rho@(logR+beta*K+logZK*np.eye(n))).real/beta
            close('excess_identity',GH,np.trace(rho@H).real-entropy/beta-fH)
            check('excess_stability',abs(GH-GK)<=2*norm+1e-11)
            check('gibbs_positivity',GH>=-1e-10)
    # Scalar shifts attain the pressure and equilibrium free-energy constant.
    H=np.diag([0.,1.]); K=H+0.25*np.eye(2)
    close('pressure_sharp_shift',abs(np.log(np.trace(expm(H)))-np.log(np.trace(expm(K)))),0.25)

def remainder_checks():
    mp.mp.dps=60
    # Nilpotent shift and upper-triangular nonnormal perturbation have exact
    # derivative-layer zeros. The test reads a fixed matrix entry at gap j.
    for n in range(2,9):
        B=np.diag(np.ones(n-1),1)+np.diag(RNG.uniform(-0.2,0.2,n))
        norm=float(np.linalg.norm(B,2))
        bm=mp.matrix([[mp.mpf(float(x)) for x in row] for row in B])
        cache={}
        for t in (0.001,0.01,0.1,0.3):
            for z in (0.,0.1,0.5,1.):
                cache[t,z]=mp.expm(mp.mpf(t)*mp.mpf(z)*bm)
        for j in range(n):
            for T in (0.001,0.01,0.1,0.3):
                check('nonempty_small_window',T*norm<1)
                for s in (0.,0.1,0.5,1.):
                    u=T*s
                    P=sum((u**k/math.factorial(k)*np.linalg.matrix_power(B,k)
                          for k in range(j+1)),np.zeros_like(B))
                    exact=expm(u*B)
                    # Direct Taylor tail bound, computed independently of the Lean proof.
                    bound=math.exp(abs(u)*norm)*(abs(u)*norm)**(j+1)/math.factorial(j+1)
                    check('actual_exponential_remainder',np.linalg.norm(exact-P,2)<=bound+2e-14)
                    lead=s**j/math.factorial(j)*np.linalg.matrix_power(B,j)[0,j]
                    check('exact_lower_derivative_zeros',all(np.linalg.matrix_power(B,k)[0,j]==0 for k in range(j)))
                    # Use 60-digit matrix exponentials before dividing by T^j.
                    # Frobenius norm is an independent upper bound for the operator norm.
                    bbound=mp.sqrt(sum(bm[i,k]**2 for i in range(n) for k in range(n)))
                    K=mp.exp(mp.mpf(T)*bbound)*bbound**(j+1)/mp.factorial(j+1)
                    mlead=mp.mpf(s)**j/mp.factorial(j)*(bm**j)[0,j]
                    err=abs(cache[T,s][0,j]/mp.mpf(T)**j-mlead)
                    check('uniform_scaled_layer_high_precision',err<=K*mp.mpf(T)+mp.mpf('1e-35'))
    # Dropping the vanishing-derivative premise breaks normalization.
    B=np.eye(2); T=1e-4
    check('graded_hypothesis_counterexample',abs(expm(T*B)[0,0]/T-1)>9000)

def gaussian_checks():
    for n in range(1,8):
        for p in (1,n,n+2):
            for repeat in range(12):
                M=RNG.normal(size=(p,n))
                if repeat==0: M[:]=0
                if repeat==1: M[:,0]=0
                beta=float(RNG.uniform(0.1,3)); tau=float(RNG.uniform(0.05,5))
                Q=beta*np.eye(n)+tau*M.T@M
                S=np.linalg.inv(Q); y=RNG.normal(size=p); x=RNG.normal(size=n)
                b=tau*M.T@y; mu=S@b; dx=x-mu
                loss=lambda z: beta*(z@z)+tau*((y-M@z)@(y-M@z))
                check('precision_positive',np.linalg.eigvalsh(Q).min()>=beta-1e-11)
                close('precision_inverse',Q@S,np.eye(n))
                close('center_equation',Q@mu,b)
                close('gaussian_complete_square',loss(x),dx@Q@dx+tau*(y@y)-mu@b)
                close('quadratic_loss_gap',loss(x)-loss(mu),dx@Q@dx)
                check('quadratic_mode',loss(x)>=loss(mu)-1e-10)
                # Independent conditional Gaussian formulas from the actual joint covariance.
                Sy=M@M.T/beta+np.eye(p)/tau
                gain=(M.T/beta)@np.linalg.inv(Sy)
                posterior_cov=np.eye(n)/beta-gain@M/beta
                close('conditional_gaussian_covariance',S,posterior_cov)
                close('conditional_gaussian_mean',mu,gain@y)
    # Removing positive prior precision invalidates the arbitrary-sensor inverse claim.
    Q=np.zeros((2,2))
    check('prior_positivity_counterexample',np.linalg.matrix_rank(Q)==0)

def main():
    klein_checks()
    gibbs_checks()
    remainder_checks()
    gaussian_checks()
    source_paths=['D5/S3/Quantum/Divergence/SpectralKlein.lean','D5/S3/Quantum/Thermal/GibbsFreeEnergyStability.lean','D5/S3/Observer/Linear/GradedExponentialRemainder.lean','D5/S3/Observer/Linear/GaussianObservationPrecision.lean']
    records=[]
    for rel in source_paths:
        path=ROOT/rel
        import re
        text=path.read_text()
        code=re.sub(r'/\-.*?\-/', '', text, flags=re.S)
        code=re.sub(r'--[^\n]*','',code)
        check('source_no_placeholders',not re.search(r'\b(sorry|admit|native_decide)\b',code))
        check('source_no_new_axioms',not re.search(r'^\s*axiom\s',code,re.M))
        names=re.findall(r'^(?:@\[simp\]\s+)?theorem\s+([A-Za-z0-9_]+)',code,re.M)
        companion=ROOT/'Blueprint'/(rel[:-5]+'.scribe.cs')
        st=companion.read_text()
        anchors=re.findall(r'DeclarationHandle\.Create\("([^"]+)"\)',st)
        for anchor in anchors:
            check('scribe_anchor_present',anchor==rel[:-5]+'.'+anchor.split('.')[-1] and anchor.split('.')[-1] in names)
        records.append({'path':rel,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                        'public_theorem_source_count':len(names),'principal_scribe_anchors':len(anchors)})
    result={'seed':88992026,'checks':COUNTS,'total_assertions':sum(COUNTS.values()),
            'max_absolute_errors':ERRORS,'source_files':records,
            'python':platform.python_version(),'numpy':np.__version__,'scipy':scipy.__version__,'mpmath':mp.__version__,
            'lean_elaborated':False,'kernel_verified':False,'scribe_compiled':False,
            'status':'EXECUTED_FINITE_NUMERICAL_DIAGNOSTICS_ONLY'}
    dest=Path(__file__).with_suffix('.json')
    dest.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
