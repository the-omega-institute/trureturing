#!/usr/bin/env python3
"""Independent finite checks for PR8899. NOT a Lean elaboration/kernel checker.

Run from any working directory: python Evidence/PR8899/research.py
Writes validation.json beside this script. Uses fractions for exact counting,
SymPy for exact matrices, NumPy for finite complex numerical diagnostics, and
mpmath for high-precision oscillator diagnostics. No network or Git operations;
only the generated validation report is overwritten.
"""
from __future__ import annotations
import hashlib
import itertools
import json
from pathlib import Path
from fractions import Fraction as Q
import platform
import random
import re
import time
import math
import numpy as np
import sympy as sp
import mpmath as mp

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).with_name('validation.json')
SOURCE_PATHS = (
    'D5/S3/Observer/Linear/OscillatorSensorJets.lean',
    'D5/S3/Observer/Linear/PredictiveEnergySplitting.lean',
    'D5/S3/Quantum/Algebra/WeylReconstruction.lean',
    'D5/S3/Quantum/Thermal/ClassicalProductRecovery.lean',
    'D5/S3/Quantum/Thermal/ExactPartitionCounting.lean',
    'D5/S3/Quantum/Thermal/HiddenExperimentRisk.lean',
)
RNG = random.Random(8899)
NRNG = np.random.default_rng(8899)
checks: dict[str, int] = {}
max_errors: dict[str, float] = {}

def check(group: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(f'Failed check in {group}, prior passed count {checks.get(group, 0)}')
    checks[group] = checks.get(group, 0) + 1


def cnf_checks() -> None:
    def test(n: int, formula: tuple[tuple[tuple[int, bool], ...], ...]) -> None:
        assigns = list(itertools.product((False, True), repeat=n))
        violations = [sum(not any(x[i] == sign for i, sign in c) for c in formula)
                      for x in assigns]
        sat = sum(v == 0 for v in violations)
        weight = Q(1, 2 ** (n + 1))
        z = sum((weight ** v for v in violations), Q(0))
        total = Q(3, 2) * z
        denom = (2 ** (n + 1)) ** len(formula)
        numerator = sum((2 ** (n + 1)) ** (len(formula) - v) for v in violations)
        check('cnf_exact', Q(0) <= z - sat <= Q(1, 2))
        check('cnf_exact', math.floor(Q(2, 3) * total) == sat)
        check('cnf_exact', denom * z == numerator)
        check('cnf_exact', numerator <= 2 ** n * denom)
        # Diagonal Boolean penalties are idempotent and commute at every assignment.
        for c in formula:
            p = [int(not any(x[i] == sign for i, sign in c)) for x in assigns]
            check('cnf_projection', all(v*v == v for v in p))
            check('cnf_projection', len({i for i, _ in c}) <= len(c))
    for n, max_m in ((0, 3), (1, 3), (2, 2)):
        literals = tuple(itertools.product(range(n), (False, True)))
        clauses = [c for k in range(4) for c in itertools.product(literals, repeat=k)]
        for m in range(max_m + 1):
            for f in itertools.product(clauses, repeat=m):
                test(n, f)
    for n in (3, 4, 5):
        for _ in range(100):
            f = tuple(tuple((RNG.randrange(n), bool(RNG.randrange(2)))
                            for _ in range(RNG.randrange(4)))
                      for _ in range(RNG.randrange(7)))
            test(n, f)


def energy_checks() -> None:
    for modes in (2, 3):
        d = 2 * modes
        for _ in range(10):
            T = sp.eye(d)
            for i in range(d):
                for j in range(i + 1, d):
                    T[i, j] = sp.Rational(RNG.randrange(-2, 3), RNG.randrange(1, 4))
            J0 = sp.diag(*([sp.Matrix([[0, 1], [-1, 0]])] * modes))
            S0 = sp.diag(*[sp.Integer(RNG.randrange(1, 6)) for _ in range(d)])
            Ti = T.inv()
            J = T * J0 * T.T
            S = Ti.T * S0 * Ti
            C = S.inv()
            A = J * S
            O0 = sp.eye(d)[:2, :]
            O = O0 * Ti
            K = (J0 * S0)[:2, :2]
            R = T[:, 2:]
            P = O*C*O.T
            L = C*O.T*P.inv()
            N = sp.eye(d) - L*O
            check('energy_exact', J.T == -J and S.T == S)
            check('energy_exact', O*A == K*O)
            check('energy_exact', A*C + C*A.T == sp.zeros(d))
            check('energy_exact', O*L == sp.eye(2))
            check('energy_exact', A*L == L*K)
            check('energy_exact', L.T*S*L == P.inv())
            check('energy_exact', L.T*S*R == sp.zeros(2, d-2))
            check('energy_exact', N*N == N and A*N == N*A and O*N == sp.zeros(2, d))
            frame = L.row_join(R)
            check('energy_exact', frame.T*S*frame == sp.diag(P.inv(), R.T*S*R))
            Jr = O*J*O.T
            B = J*O.T
            check('energy_exact', Jr*K.T == B.T*S*B and Jr.det() != 0)
    # Positive energy is essential to the radical-exclusion theorem.
    J = sp.Matrix([[0, 1], [-1, 0]])
    S = sp.diag(1, -1)
    O = sp.Matrix([[1, 1]])
    K = sp.Matrix([[-1]])
    check('energy_hypothesis_counterexample', O*J*S == K*O and O*J*O.T == sp.zeros(1))


def weyl_checks() -> None:
    max_pair = max_recon = 0.0
    for d in range(1, 9):
        X = np.roll(np.eye(d, dtype=complex), 1, axis=0)
        Z = np.diag(np.exp(2j*np.pi*np.arange(d)/d))
        words = [np.linalg.matrix_power(X, a) @ np.linalg.matrix_power(Z, b)
                 for a in range(d) for b in range(d)]
        W = np.stack(words)
        pairing = np.einsum('pij,qij->pq', W.conj(), W)
        err = float(np.max(np.abs(pairing - d*np.eye(d*d))))
        max_pair = max(max_pair, err)
        check('weyl_numeric_pairing', err < 1e-10)
        for _ in range(5):
            A = NRNG.normal(size=(d,d)) + 1j*NRNG.normal(size=(d,d))
            coeff = np.einsum('pij,ij->p', W.conj(), A)/d
            rebuilt = np.einsum('p,pij->ij', coeff, W)
            err = float(np.max(np.abs(A-rebuilt)))
            max_recon = max(max_recon, err)
            check('weyl_numeric_reconstruction', err < 1e-10)
    max_errors.update(weyl_pairing=max_pair, weyl_reconstruction=max_recon)


def hidden_checks() -> None:
    max_err = 0.0
    for e in (2, 3):
        rho = np.array([[0.6, 0.2j], [-0.2j, 0.4]])
        sigma = np.diag([1.] + [0.]*(e-1))
        tau = np.eye(e)/e
        policy: dict[tuple[tuple[int, ...], int], np.ndarray] = {}
        for depth in range(4):
            for hist in itertools.product((0,1), repeat=depth):
                for x in (0,1):
                    policy[(hist,x)] = (NRNG.normal(size=(2,2))+
                                       1j*NRNG.normal(size=(2,2)))/3
        for length in range(5):
            for record in itertools.product((0,1), repeat=length):
                visible = rho.copy()
                joint0, joint1 = np.kron(rho,sigma), np.kron(rho,tau)
                hist: tuple[int,...] = ()
                for x in record:
                    k = policy[(hist,x)]
                    kb = np.kron(k,np.eye(e))
                    visible = k @ visible @ k.conj().T
                    joint0 = kb @ joint0 @ kb.conj().T
                    joint1 = kb @ joint1 @ kb.conj().T
                    hist += (x,)
                err = max(float(np.max(np.abs(joint0-np.kron(visible,sigma)))),
                          float(abs(np.trace(joint0)-np.trace(joint1))))
                max_err = max(max_err, err)
                check('hidden_adaptive_numeric', err < 1e-10)
    max_errors['hidden_adaptive'] = max_err
    for _ in range(300):
        L = Q(RNG.randrange(0,20), RNG.randrange(1,10))
        points = [Q(RNG.randrange(-20,40), RNG.randrange(1,8)) for _ in range(6)]
        numerators = [RNG.randrange(1,10) for _ in points]
        probs = [Q(k, sum(numerators)) for k in numerators]
        risk0 = sum(p*abs(x) for p,x in zip(probs,points))
        risk1 = sum(p*abs(x-L) for p,x in zip(probs,points))
        check('randomized_risk_exact', risk0+risk1 >= L and max(risk0,risk1) >= L/2)
        theta = L * Q(RNG.randrange(11),10)
        check('randomized_risk_exact', abs(L/2-theta) <= L/2)


def kl(p: np.ndarray, q: np.ndarray) -> float:
    positive = p > 0
    if np.any(q[positive] <= 0):
        return math.inf
    return float(np.sum(p[positive] * np.log(p[positive]/q[positive])))


def classical_checks() -> None:
    max_err = 0.0
    for _ in range(120):
        mu = NRNG.uniform(0.05, 1, size=(3, 4)); mu /= mu.sum()
        gr = NRNG.uniform(0.05,1,size=3); gr /= gr.sum()
        gh = NRNG.uniform(0.05,1,size=4); gh /= gh.sum()
        nu = mu.sum(axis=1)
        recovered = nu[:,None]*gh[None,:]
        gamma = gr[:,None]*gh[None,:]
        full, marginal, defect = kl(mu,gamma), kl(nu,gr), kl(mu,recovered)
        err = abs(full-marginal-defect)
        max_err = max(max_err, err)
        check('classical_kl_numeric', err < 1e-12 and defect >= -1e-14)
        check('classical_kl_numeric', abs(kl(recovered,gamma)-marginal) < 1e-12)
    # Support failure is infinity, not the totalized real log(0)=0 convention.
    check('classical_support_boundary', math.isinf(kl(np.array([1.,0.]),np.array([0.,1.]))))
    max_errors['classical_kl_chain'] = max_err


def oscillator_checks() -> list[dict[str, str]]:
    q = sp.Rational
    B = sp.Matrix([[0,1,0,0],[-1,0,0,0],[0,0,0,2],[0,0,-2,0]])
    C = sp.Matrix([[1,0,1,0]])
    D = sp.Matrix([[1,0,0,0],[0,0,1,0]])
    V = sp.Matrix.vstack(*[C*B**j/sp.factorial(j) for j in range(4)])
    expected = sp.Matrix([[1,0,1,0],[0,1,0,2],[-q(1,2),0,-2,0],[0,-q(1,6),0,-q(4,3)]])
    H = sp.Matrix(4,4,lambda i,j:q(1,i+j+1))
    sep = sp.Matrix([[1,q(1,2),0,0],[q(1,2),q(1,3),0,0],
                     [0,0,1,1],[0,0,1,q(4,3)]])
    check('oscillator_exact', V == expected)
    check('oscillator_exact', (C.T*C).trace() == (D.T*D).trace() == 2)
    check('oscillator_exact', V.det() == q(3,2))
    check('oscillator_exact', H.det() == q(1,6048000))
    check('oscillator_exact', (V.T*H*V).det() == q(1,2688000))
    check('oscillator_exact', sep.det() == q(1,36))
    T = sp.symbols('T', real=True)
    scale = sp.diag(1,T,T**2,T**3)
    check('oscillator_exact', sp.factor((T*V.T*scale*H*scale*V).det()) == T**16/2688000)
    # These are numeric diagnostics of the full trajectory, NOT limit proofs.
    mp.mp.dps = 80
    diagnostics=[]
    for t in ('0.1','0.05','0.02'):
        t=mp.mpf(t)
        funcs=(lambda s:mp.cos(s),lambda s:mp.sin(s),
               lambda s:mp.cos(2*s),lambda s:mp.sin(2*s))
        G=mp.matrix(4)
        for i in range(4):
            for j in range(i,4):
                v=mp.quad(lambda s:funcs[i](s)*funcs[j](s),[0,t])
                G[i,j]=G[j,i]=v
        Gsep=mp.matrix(4)
        for w,offset in ((mp.mpf(1),0),(mp.mpf(2),2)):
            Gsep[offset,offset]=t/2+mp.sin(2*w*t)/(4*w)
            Gsep[offset+1,offset+1]=t/2-mp.sin(2*w*t)/(4*w)
            Gsep[offset,offset+1]=Gsep[offset+1,offset]=(1-mp.cos(2*w*t))/(4*w)
        normalized_sum=mp.det(G)/t**16
        normalized_sep=mp.det(Gsep)/t**8
        target_sum=mp.mpf(1)/2688000; target_sep=mp.mpf(1)/36
        check('oscillator_high_precision_diagnostic', abs(normalized_sum/target_sum-1)<mp.mpf('0.02'))
        check('oscillator_high_precision_diagnostic', abs(normalized_sep/target_sep-1)<mp.mpf('0.02'))
        cov_sum=(mp.eye(4)+G/t**4)**-1
        cov_sep=(mp.eye(4)+Gsep/t**4)**-1
        diagnostics.append(dict(T=mp.nstr(t,8),det_sum_div_T16=mp.nstr(normalized_sum,30),
                                det_sep_div_T8=mp.nstr(normalized_sep,30),
                                beta1_risk_sum=mp.nstr(sum(cov_sum[i,i] for i in range(4))/2,30),
                                beta1_risk_sep=mp.nstr(sum(cov_sep[i,i] for i in range(4))/2,30)))
    return diagnostics


def strip_lean_comments(text: str) -> str:
    result=[]; i=0; depth=0
    while i<len(text):
        if text[i:i+2]=='/-': depth+=1; i+=2
        elif depth and text[i:i+2]=='-/': depth-=1; i+=2
        elif depth: i+=1
        elif text[i:i+2]=='--':
            end=text.find('\n',i); i=len(text) if end<0 else end
        else: result.append(text[i]); i+=1
    if depth: raise AssertionError('Unclosed Lean block comment')
    return ''.join(result)


def source_checks() -> dict[str, object]:
    modules=[]; all_decls=set()
    for relative_path in SOURCE_PATHS:
        p = ROOT/relative_path
        module=p.relative_to(ROOT).as_posix()[:-5]
        text=p.read_text()
        code=strip_lean_comments(text)
        check('source_static', not re.search(r'\b(sorry|admit|native_decide)\b',code))
        check('source_static', not re.search(r'^\s*(?:private\s+)?axiom\s',code,re.M))
        public=re.findall(r'^theorem\s+([A-Za-z0-9_]+)',code,re.M)
        all_decls.update(module+'.'+d for d in public)
        companion=ROOT/'Blueprint'/(module+'.scribe.cs')
        check('source_static', companion.is_file())
        modules.append(dict(path=module+'.lean',public_theorems=len(public),
                            sha256=hashlib.sha256(p.read_bytes()).hexdigest(),
                            scribe=companion.relative_to(ROOT).as_posix()))
    anchors=[]
    for relative_path in SOURCE_PATHS:
        p = ROOT/'Blueprint'/(relative_path[:-5]+'.scribe.cs')
        text=p.read_text()
        found=re.findall(r'DeclarationHandle\.Create\(\s*"([^"]+)"\s*\)',text)
        for anchor in found:
            check('scribe_anchor_static',anchor in all_decls)
            anchors.append(anchor)
        check('scribe_anchor_static',len(found)>0)
    return dict(modules=modules,public_theorem_declarations=len(all_decls),
                scribe_anchors=len(anchors),lean_kernel_verified=False,
                lean_elaboration_attempted=False,scribe_compiled=False,
                comment='Static text checks cannot detect Lean type errors or prove theorems.')


def main() -> None:
    start=time.monotonic()
    cnf_checks(); energy_checks(); weyl_checks(); hidden_checks(); classical_checks()
    diagnostics=oscillator_checks()
    sources=source_checks()
    result=dict(checks=checks,total_assertions=sum(checks.values()),
                numeric_max_absolute_errors=max_errors,oscillator_diagnostics=diagnostics,
                sources=sources,seed=8899,python=platform.python_version(),
                sympy=sp.__version__,numpy=np.__version__,mpmath=mp.__version__,
                elapsed_seconds=round(time.monotonic()-start,3),
                status='FINITE_CHECKS_AND_STATIC_SCAN_ONLY_NOT_KERNEL_VERIFICATION')
    OUT.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
