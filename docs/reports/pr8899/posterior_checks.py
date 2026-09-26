#!/usr/bin/env python3
"""Finite checks of the new Gaussian disintegration source. Not a Lean checker.

Run from the repository: python docs/reports/pr8899/posterior_checks.py
Only posterior_checks.json is written. No network, Git, or CI operations.
"""
from __future__ import annotations
from collections import Counter
from pathlib import Path
import hashlib
import json
import platform
import re
import numpy as np
import scipy
from numpy.polynomial.hermite import hermgauss
import itertools
import shutil
from scipy.integrate import quad
import sympy as sp

ROOT = Path(__file__).resolve().parents[3]
SOURCE_FILES = (
    'D5/S3/Observer/Linear/GaussianAffineDisintegration.lean',
    'D5/S3/Observer/Linear/GaussianObservationDisintegration.lean',
    'D5/S3/Observer/Linear/GaussianPosteriorRisk.lean',
)
SEED = 88992609
rng = np.random.default_rng(SEED)
counts: Counter[str] = Counter()
errors: dict[str, float] = {}

def check(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(f'{name} failed after {counts[name]} preceding checks')
    counts[name] += 1

def close(name: str, lhs: object, rhs: object, atol: float = 3e-10) -> None:
    left, right = np.asarray(lhs), np.asarray(rhs)
    error = float(np.max(np.abs(left-right), initial=0))
    errors[name] = max(errors.get(name, 0), error)
    check(name, bool(np.allclose(left, right, atol=atol, rtol=atol)))

def logdensity(x: np.ndarray, mean: np.ndarray, cov: np.ndarray) -> float:
    if x.size == 0:
        return 0.0
    sign, ld = np.linalg.slogdet(cov)
    if sign <= 0:
        raise AssertionError('Nonpositive density covariance')
    v = x-mean
    return float(-(x.size*np.log(2*np.pi)+ld+v @ np.linalg.solve(cov,v))/2)

def cases() -> None:
    for n,p in [(n,p) for n in range(1,6) for p in range(1,7)] + [(0,0),(0,3),(3,0)]:
        for kind in range(4):
            M = rng.normal(size=(p,n))
            if kind == 0: M *= 0
            if kind == 1 and n: M[:,n//2:] = 0
            if kind == 2 and p: M[-1,:] = M[0,:]
            beta, tau = np.exp(rng.uniform(-2,2,size=2))
            Q = beta*np.eye(n)+tau*M.T@M
            S = np.linalg.inv(Q)
            K = tau*S@M.T
            D = np.diag([1/beta]*n+[1/tau]*p)
            X = np.hstack([np.eye(n),np.zeros((n,p))])
            N = np.hstack([np.zeros((p,n)),np.eye(p)])
            B = np.hstack([M,np.eye(p)])
            A = np.hstack([beta*S,-K])
            C = B@D@B.T
            close('input_state_covariance',X@D@X.T,np.eye(n)/beta)
            close('input_noise_covariance',N@D@N.T,np.eye(p)/tau)
            close('input_cross_zero',X@D@N.T,np.zeros((n,p)))
            close('observation_identity',B,M@X+N)
            close('signal_reconstruction',X,K@B+A)
            close('innovation_times_covariance',A@D,np.hstack([S,-S@M.T]))
            close('innovation_cross_zero',A@D@B.T,np.zeros((n,p)))
            close('innovation_covariance',A@D@A.T,S)
            close('gain_independent_schur_formula',K,np.linalg.solve(C,M/beta).T)
            close('covariance_independent_schur_formula',S,np.eye(n)/beta-K@M/beta)
            # Original (Y,X) and reassembled (Y,KY+R) covariance, R independent of Y.
            original = np.vstack([B,X])@D@np.vstack([B,X]).T
            T = np.block([[np.eye(p),np.zeros((p,n))],[K,np.eye(n)]])
            block = np.block([[C,np.zeros((p,n))],[np.zeros((n,p)),S]])
            close('joint_measure_covariance',original,T@block@T.T)
            close('reassembly_jacobian',np.linalg.det(T),1)
            for _ in range(3):
                x,y = rng.normal(size=n),rng.normal(size=p)
                original_log = logdensity(x,np.zeros(n),np.eye(n)/beta)+logdensity(y,M@x,np.eye(p)/tau)
                conditional_log = logdensity(y,np.zeros(p),C)+logdensity(x,K@y,S)
                close('normalized_bayes_density_identity',original_log,conditional_log)
                u,v = rng.normal(size=n),rng.normal(size=p)
                joint_char = np.exp(-((u@A+v@B)@D@(u@A+v@B))/2)
                product_char = np.exp(-(u@S@u)/2)*np.exp(-(v@C@v)/2)
                close('residual_data_characteristic_factorization',joint_char,product_char)


def exact_matrices() -> None:
    for n,p in ((1,1),(2,1),(1,3),(2,3),(3,2)):
        for blind in (False,True):
            M = sp.zeros(p,n) if blind else sp.Matrix(p,n,lambda i,j: sp.Rational((i+1)*(j+2)%5-2,3))
            beta,tau = sp.Rational(3,2),sp.Rational(5,3)
            Q = beta*sp.eye(n)+tau*M.T*M
            S = Q.inv(); K=tau*S*M.T
            D=sp.diag(*([1/beta]*n+[1/tau]*p))
            A=(beta*S).row_join(-K); B=M.row_join(sp.eye(p)); X=sp.eye(n).row_join(sp.zeros(n,p))
            check('exact_reconstruction', X==K*B+A)
            check('exact_innovation_cross_zero', A*D*B.T==sp.zeros(n,p))
            check('exact_innovation_covariance', A*D*A.T==S)


def scalar_quadrature() -> None:
    for m in (0.,-1.,2.):
        for beta,tau in ((1.3,.6),(.8,2.1)):
            s=1/(beta+tau*m*m); k=tau*s*m; cy=m*m/beta+1/tau
            for y in (-1.2,0.,1.7):
                # Conditional density derived from original joint/marginal densities.
                def posterior(x: float) -> float:
                    return float(np.exp(logdensity(np.array([x]),np.zeros(1),np.eye(1)/beta)
                        +logdensity(np.array([y]),np.array([m*x]),np.eye(1)/tau)
                        -logdensity(np.array([y]),np.zeros(1),np.array([[cy]]))))
                mass,me=quad(posterior,-np.inf,np.inf,epsabs=2e-10)
                mean,ee=quad(lambda x:x*posterior(x),-np.inf,np.inf,epsabs=2e-10)
                variance,ve=quad(lambda x:(x-k*y)**2*posterior(x),-np.inf,np.inf,epsabs=2e-10)
                close('quadrature_conditional_mass',mass,1,2e-8)
                close('quadrature_conditional_mean',mean,k*y,2e-8)
                close('quadrature_conditional_covariance',variance,s,2e-8)


def strip_comments(text: str) -> str:
    i=0; depth=0; out=[]
    while i<len(text):
        if text[i:i+2]=='/-': depth+=1; i+=2
        elif depth and text[i:i+2]=='-/': depth-=1; i+=2
        elif depth: i+=1
        elif text[i:i+2]=='--':
            j=text.find('\n',i); i=len(text) if j<0 else j
        else: out.append(text[i]); i+=1
    if depth: raise AssertionError('Unclosed Lean comment')
    return ''.join(out)


def hermite_rule(dimension: int, order: int) -> tuple[np.ndarray,np.ndarray]:
    """Product Gauss-Hermite rule for standard real Gaussian inputs."""
    z,w=hermgauss(order)
    indices=np.array(list(itertools.product(range(order),repeat=dimension)),dtype=int)
    if dimension==0:
        return np.empty((1,0)),np.ones(1)
    return np.sqrt(2)*z[indices], np.prod((w/np.sqrt(np.pi))[indices],axis=1)


def risk_checks() -> None:
    """Independent input-space cubature versus the derived posterior-risk identity."""
    rg=np.random.default_rng(SEED+1)
    for n,p in ((1,1),(1,2),(2,1),(2,2),(0,1),(1,0),(0,0)):
        points,weights=hermite_rule(n+p,5)
        ypoints,yweights=hermite_rule(p,5)
        for blind in (False,True):
            M=rg.normal(size=(p,n))
            if blind: M[:]=0
            beta,tau=np.exp(rg.uniform(-1,1,size=2))
            Sigma=np.linalg.inv(beta*np.eye(n)+tau*M.T@M)
            K=tau*Sigma@M.T
            C=M@M.T/beta+np.eye(p)/tau
            x=points[:,:n]/np.sqrt(beta)
            eps=points[:,n:]/np.sqrt(tau)
            y=x@M.T+eps
            Y=ypoints@np.linalg.cholesky(C).T
            baseline=np.trace(Sigma)/2
            L=rg.normal(size=(n,p))/3
            B=rg.normal(size=(n,p))/4
            c=rg.normal(size=n)/2
            for kind in ('mean','affine','quadratic','cubic'):
                def estimate(z: np.ndarray) -> np.ndarray:
                    base=z@K.T
                    if kind=='mean': return base
                    if kind=='affine': return base+z@L.T+c
                    if kind=='quadratic': return base+(z*z)@B.T+c
                    return base+(z*z*z)@B.T+z@L.T+c
                loss=np.sum((x-estimate(y))**2,axis=1)/2
                direct=float(weights@loss)
                deviation=float(yweights@(np.sum((Y@K.T-estimate(Y))**2,axis=1)/2))
                close('original_input_bayes_risk',direct,baseline+deviation)
                check('bayes_lower_bound',direct>=baseline-1e-10)
                if kind=='mean': close('attained_bayes_minimum',direct,baseline)
                # An actual Euclidean isometry, including the zero-dimensional case.
                U=np.linalg.qr(rg.normal(size=(n,n)))[0]
                rotated=float(weights@(np.sum((x@U.T-estimate(y)@U.T)**2,axis=1)/2))
                close('orthogonal_future_risk',rotated,direct)
    # Measurable nonpolynomial competitors: independent characteristic-function formula.
    pts,wts=hermite_rule(2,35)
    for M in (0.,0.7,-1.4):
        for beta,tau in ((1.,1.),(0.8,2.),(2.,0.7)):
            Sigma=1/(beta+tau*M*M); K=tau*Sigma*M; C=M*M/beta+1/tau
            x=pts[:,0]/np.sqrt(beta); y=M*x+pts[:,1]/np.sqrt(tau)
            for freq in (0.3,0.7):
                g=K*y+0.4*np.sin(freq*y)+0.2
                direct=float(wts@((x-g)**2/2))
                expected=Sigma/2+(0.16*(1-np.exp(-2*freq*freq*C))/2+0.04)/2
                close('nonpolynomial_measurable_estimator',direct,expected,atol=3e-9)
    # A concrete infinite-risk boundary: M=0, beta=tau=1, g(y)=exp(y^2).
    # The squared-estimator integral on [k,k+1] is at least
    # exp(3*k^2/2)/sqrt(2*pi). These increasing lower bounds are diagnostics,
    # not a formal proof of convergence/divergence in this check program.
    previous=0.
    for k in range(1,7):
        lower=float(np.exp(1.5*k*k)/np.sqrt(2*np.pi))
        check('infinite_risk_truncation_lower_bound',lower>previous and lower>k)
        previous=lower


def balanced_scribe(text: str) -> bool:
    """Balance delimiters after removing C# string literals; this is not a compiler."""
    code=re.sub(r'"(?:\\.|[^"\\])*"','""',text)
    stack=[]
    pairs={')':'(',']':'[','}':'{'}
    for ch in code:
        if ch in '([{': stack.append(ch)
        elif ch in ')]}':
            if not stack or stack.pop()!=pairs[ch]: return False
    return not stack


def sources() -> list[dict[str,object]]:
    inventory=[]
    for rel in SOURCE_FILES:
        p=ROOT/rel; text=p.read_text(); code=strip_comments(text)
        check('no_placeholder',not re.search(r'\b(sorry|admit|native_decide)\b',code))
        check('no_new_axiom',not re.search(r'^\s*(?:private\s+)?axiom\s',code,re.M))
        declarations=set(re.findall(r'(?m)^(?:@\[[^\]]+\]\s*)?theorem\s+(\w+)',code))
        scribe=ROOT/('Blueprint/'+rel[:-5]+'.scribe.cs')
        check('paired_scribe',scribe.is_file())
        check('scribe_delimiters',balanced_scribe(scribe.read_text()))
        anchors=re.findall(r'DeclarationHandle.Create\("([^"]+)"\)',scribe.read_text())
        for anchor in anchors:
            check('scribe_anchor',anchor.startswith(rel[:-5]+'.') and anchor.split('.')[-1] in declarations)
        inventory.append({'path':rel,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
                          'public_theorem_source_count':len(declarations),'principal_scribe_anchors':len(anchors)})
    return inventory


def main() -> None:
    cases(); exact_matrices(); scalar_quadrature(); risk_checks(); inventory=sources()
    out={'seed':SEED,'checks':dict(counts),'total_assertions':sum(counts.values()),
         'max_absolute_errors':errors,'source_files':inventory,
         'python':platform.python_version(),'numpy':np.__version__,'scipy':scipy.__version__,
         'sympy':sp.__version__,
         'compiler_presence':{'lean':shutil.which('lean'),'lake':shutil.which('lake')},
         'risk_suite_seed':SEED+1,'lean_elaborated':False,'kernel_verified':False,
         'scribe_compiled':False,'status':'EXECUTED_FINITE_CHECKS_ONLY'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__': main()
