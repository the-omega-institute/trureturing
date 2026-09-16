#!/usr/bin/env python3
"""Finite checks supporting the string/observer appendix.

These checks are examples, not a proof of a string background, a recovery theorem,
or the universal claims in the appendix. No network, Lean, or CI is invoked.
Run: python check_integration.py --output checks.json
Requirements: Python 3, numpy, sympy.
"""
from __future__ import annotations
import argparse
import itertools
import json
from pathlib import Path
from typing import Callable
import numpy as np
import sympy as sp

BASE = "e984c77223b55a3cda565c7694098e436926183d"
SEED = 20260917
TOL = 1e-10
rng = np.random.default_rng(SEED)

def adj(a: np.ndarray) -> np.ndarray:
    return a.conj().T

def herm(a: np.ndarray) -> np.ndarray:
    return (a + adj(a)) / 2

def fmat(a: np.ndarray, f: Callable[[np.ndarray], np.ndarray]) -> np.ndarray:
    v, q = np.linalg.eigh(herm(a))
    if v.min() < -1e-11:
        raise ValueError("Matrix is not positive semidefinite.")
    return (q * f(np.maximum(v, 1e-15))) @ adj(q)

def pd(d: int) -> np.ndarray:
    a = rng.normal(size=(d,d)) + 1j*rng.normal(size=(d,d))
    return adj(a) @ a + np.eye(d)

def state(d: int) -> np.ndarray:
    a = pd(d)
    return a / np.trace(a).real

def unitary(d: int) -> np.ndarray:
    a = rng.normal(size=(d,d)) + 1j*rng.normal(size=(d,d))
    q, r = np.linalg.qr(a)
    diag = np.diag(r)
    return q @ np.diag(diag / np.abs(diag))

def rel(a: np.ndarray, b: np.ndarray) -> float:
    return float(np.trace(a @ (fmat(a,np.log)-fmat(b,np.log))).real)

def fidelity(a: np.ndarray, b: np.ndarray) -> float:
    sa = fmat(a, np.sqrt)
    return min(1., float(np.trace(fmat(sa @ b @ sa,np.sqrt)).real))

def trace_norm(a: np.ndarray) -> float:
    return float(np.linalg.svd(a,compute_uv=False).sum())

def expect_close(x: np.ndarray | complex | float, y: np.ndarray | complex | float,
                 label: str, tol: float = TOL) -> float:
    err = float(np.max(np.abs(np.asarray(x)-np.asarray(y))))
    if err > tol:
        raise AssertionError(f"{label}: residual {err} exceeds {tol}")
    return err

def exact_charge_checks() -> dict:
    F = sp.Matrix([[1,1],[1,0]])
    A = F**2
    D = sp.diag(A,A.inv().T)
    eta = sp.zeros(4)
    eta[:2,2:] = sp.eye(2)
    eta[2:,:2] = sp.eye(2)
    assert D.T*eta*D == eta
    assert D.det() == 1
    # Exact finite illustration of the no-nonzero-periodic-charge proof.
    e1 = sp.Matrix([1,0,0,0])
    orbit = []
    for k in range(21):
        z = D**k*e1
        norm = (z.T*z)[0]
        assert norm == sp.fibonacci(4*k+1)
        if k:
            assert (D**k-sp.eye(4)).det() != 0
        orbit.append(int(norm))
    eta1 = sp.Matrix([[0,1],[1,0]])
    o11 = []
    for vals in itertools.product(range(-3,4),repeat=4):
        d = sp.Matrix(2,2,vals)
        if d.T*eta1*d == eta1:
            o11.append(list(vals))
    assert len(o11) == 4
    H = sp.diag(2,3,sp.Rational(1,2),sp.Rational(1,3))
    Hp = D.inv().T*H*D.inv()
    assert Hp*eta*Hp == eta
    charge_count = 0
    for coords in itertools.product(range(-2,3),repeat=4):
        z = sp.Matrix(coords)
        assert ((D*z).T*Hp*(D*z))[0] == (z.T*H*z)[0]
        charge_count += 1
    radius_count = 0
    for R, ap in [(sp.Rational(3,2),sp.Rational(5,3)),
                  (sp.Rational(1,3),sp.Rational(7,2)), (sp.Integer(1),sp.Integer(1))]:
        for n,w in itertools.product(range(-4,5),repeat=2):
            Rp = ap/R
            pL, pR = n/R+w*R/ap, n/R-w*R/ap
            pLp, pRp = w/Rp+n*Rp/ap, w/Rp-n*Rp/ap
            assert sp.simplify(pLp-pL)==0 and sp.simplify(pRp+pR)==0
            assert sp.simplify((n/R)**2+(w*R/ap)**2-(w/Rp)**2-(n*Rp/ap)**2)==0
            assert n*w == w*n
            radius_count += 1
    return dict(golden_O22_identity=True, golden_orbit_k0_to20=orbit,
                O11_bounded_search=o11, transported_quadratic_checks=charge_count,
                circle_T_duality_checks=radius_count,
                caveat="Bounded checks do not replace the general algebraic proofs.")

def matrix_checks() -> dict:
    maxima = dict(schur=0.,response=0.,entropy_identity=0.,entropy_covariance=0.,
                  erasure_covariance=0.,erasure_trace=0.)
    P=np.diag([1,1,0,0]).astype(complex)
    Q=np.eye(4)-P
    for _ in range(64):
        D=pd(4); U=unitary(4); Dp=U@D@adj(U)
        V=np.eye(4,dtype=complex)[:,:2]
        W=np.eye(4,dtype=complex)[:,2:]
        def schur(d,v,w):
            return adj(v)@d@v-adj(v)@d@w@np.linalg.solve(adj(w)@d@w,adj(w)@d@v)
        maxima['schur']=max(maxima['schur'],expect_close(schur(D,V,W),schur(Dp,U@V,U@W),'Schur'))
        C=rng.normal(size=(2,4))+1j*rng.normal(size=(2,4)); Cp=C@adj(U)
        maxima['response']=max(maxima['response'],expect_close(C@np.linalg.solve(D,adj(C)),Cp@np.linalg.solve(Dp,adj(Cp)),'response'))
        M0=P@D@P+Q@D@Q
        tau=np.trace(D).real
        I=float(np.trace(D@fmat(D,np.log)-M0@fmat(M0,np.log)).real)
        maxima['entropy_identity']=max(maxima['entropy_identity'],expect_close(I,tau*rel(D/tau,M0/tau),'entropy identity'))
        Pp=U@P@adj(U); Qp=np.eye(4)-Pp
        M0p=Pp@Dp@Pp+Qp@Dp@Qp
        Ip=float(np.trace(Dp@fmat(Dp,np.log)-M0p@fmat(M0p,np.log)).real)
        maxima['entropy_covariance']=max(maxima['entropy_covariance'],expect_close(I,Ip,'entropy covariance'))
        ev=np.linalg.eigvalsh(D)
        b2=float(np.linalg.norm(D[:2,2:],'fro')**2)
        assert b2/ev.max()-TOL <= I <= b2/ev.min()+TOL
        rho=state(4)
        def erase(r,v):
            out=np.zeros((3,3),complex)
            out[:2,:2]=adj(v)@r@v
            out[2,2]=np.trace(r)-np.trace(out[:2,:2])
            return herm(out)
        left=erase(U@rho@adj(U),U@V); right=erase(rho,V)
        maxima['erasure_covariance']=max(maxima['erasure_covariance'],expect_close(left,right,'erasure'))
        maxima['erasure_trace']=max(maxima['erasure_trace'],expect_close(np.trace(left),1,'erasure trace'))
        assert np.linalg.eigvalsh(left).min()>-TOL
    H=np.array([[1,1],[1,-1]],complex)/np.sqrt(2)
    d=np.diag([1.,4.]); c=np.array([[1.,0.]],complex)
    old=(c@np.linalg.solve(d,adj(c)))[0,0].real
    wrong=(c@np.linalg.solve(H@d@adj(H),adj(c)))[0,0].real
    expect_close(old,1.,'original response'); expect_close(wrong,5/8,'wrong-cut response')
    return dict(samples=64,max_residuals=maxima,
                wrong_fixed_window=dict(original=old,untransported=wrong))

def quantum_checks() -> dict:
    rotations=[unitary(2),unitary(2)]
    # Two nonprojective instruments with outcome-dependent post-measurement maps.
    K=[]
    for x in range(2):
        r=rotations[x]
        K.append([unitary(2)@np.diag(np.sqrt([.8,.3]))@adj(r),
                  unitary(2)@np.diag(np.sqrt([.2,.7]))@adj(r)])
    for ks in K:
        expect_close(sum(adj(k)@k for k in ks),np.eye(2),'instrument TP')
    U=unitary(2); Kp=[[U@k@adj(U) for k in ks] for ks in K]
    max_word=0.; words=0
    for _ in range(4):
        rho=state(2)
        for length in range(6):
            for word in itertools.product(range(4),repeat=length):
                a=rho.copy(); b=U@rho@adj(U)
                for label in word:
                    x,y=divmod(label,2)
                    a=K[x][y]@a@adj(K[x][y]); b=Kp[x][y]@b@adj(Kp[x][y])
                max_word=max(max_word,expect_close(np.trace(a),np.trace(b),'word probability'))
                words+=1
    def protocol(rho,ks,noise=(0.,)*5):
        branches={():rho}
        for j,p in enumerate(noise):
            nxt={}
            for record,a in branches.items():
                x=(sum(record)+j)%2
                for y in range(2):
                    b=ks[x][y]@a@adj(ks[x][y])
                    nxt[record+(y,)]=(1-p)*b+p*np.trace(b)*np.eye(2)/2
            branches=nxt
        probs=np.array([np.trace(a).real for a in branches.values()])
        expect_close(probs.sum(),1.,'protocol normalization')
        return probs
    max_adaptive=0.; max_noise_tv=0.; max_recovery_tv=0.; min_recovery_slack=1e9
    noise=(.03,.04,.02,.05,.01)
    sigma=np.eye(2)/2
    for _ in range(64):
        rho=state(2)
        p=protocol(rho,K); pp=protocol(U@rho@adj(U),Kp)
        max_adaptive=max(max_adaptive,expect_close(p,pp,'adaptive covariance'))
        noisy=protocol(rho,K,noise)
        tv=float(np.abs(p-noisy).sum()/2)
        assert tv <= sum(noise)+TOL  # diamond upper bound delta_j <= 2 noise_j
        max_noise_tv=max(max_noise_tv,tv)
        # For dephasing and maximally mixed sigma, the recovery is dephasing.
        recovered=np.diag(np.diag(rho))
        defect=rel(rho,sigma)-rel(recovered,sigma)
        f=fidelity(rho,recovered)
        slack=defect+2*np.log(f)
        assert slack>=-TOL
        min_recovery_slack=min(min_recovery_slack,float(slack))
        tv=float(np.abs(p-protocol(recovered,K)).sum()/2)
        bound=np.sqrt(max(0.,1-np.exp(-defect)))
        assert tv<=bound+TOL
        max_recovery_tv=max(max_recovery_tv,tv)
        assert trace_norm(rho-recovered)/2<=bound+TOL
    return dict(instrument_word_checks=words,max_word_residual=max_word,
                adaptive_samples=64,max_adaptive_residual=max_adaptive,
                approximate_dictionary_samples=64,max_noise_record_TV=max_noise_tv,
                composable_noise_TV_bound=sum(noise),
                dephasing_recovery_samples=64,min_recovery_inequality_slack=min_recovery_slack,
                max_recovery_record_TV=max_recovery_tv,
                caveat="Recovery probes cover only dephasing with maximally mixed reference, not universal recovery construction.")

def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path('checks.json'))
    args=parser.parse_args()
    result=dict(base_commit=BASE,seed=SEED,numerical_tolerance=TOL,
                software=dict(numpy=np.__version__,sympy=sp.__version__),
                proof_status="Ordinary proofs in the appendix; these are finite exact/numerical checks only.",
                exact=exact_charge_checks(),matrices=matrix_checks(),quantum=quantum_checks())
    args.output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,ensure_ascii=False,indent=2))

if __name__=='__main__':
    main()
