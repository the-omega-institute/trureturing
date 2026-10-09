---
slug: van-herstraeten-et-al-2025-beam-splitter-state-extremality
bibkey: vanherstraeten2025extremewigner
doi: null
url: https://arxiv.org/abs/2512.14831v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.result
---

# Finite-Fock beam-splitter states need not be extreme Wigner-positive states

## Problem

Z. Van Herstraeten, J. Davis, N. C. Dias, J. N. Prata, N. J. Cerf and
U. Chabaud, *Extreme non-negative Wigner functions*, arXiv:2512.14831v3,
Section 6, printed page 15, ask:

> This leads us to formulate the following open problem: for any two Fock-bounded pure states $\ket\psi,\ket\phi$ is the beamsplitter state $\hat\sigma(\psi,\phi)$ an extreme WPS?

The source is [the version-3 paper](https://arxiv.org/abs/2512.14831v3).
The Tier-1 statement, finite-matrix conventions and literature reading are
in [preregistration #14447](https://github.com/the-omega-institute/trureturing/issues/14447).
The answer is **Refuted**.

## Motivation

`D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.result` proves the literal negation of
`claim`, which quantifies every natural cutoff $N$ and all normalized
$\psi,\phi:\operatorname{Fin}(N+1)\to\mathbb C$.
The consumed private theorem `family_not_extreme` proves the counterexample
for every real $a>0$, using
$\psi_a=(|0\rangle+a|2\rangle)/\sqrt{1+a^2}$ and
$\phi_a=(|0\rangle-a|2\rangle)/\sqrt{1+a^2}$.
`result` uses $a=1/2$ and $N=2$.

## Gap

The published question extends the paper's theorem for two Fock-state
inputs to arbitrary Fock-bounded pure superpositions. The literature
reading in #14447 finds no prior settlement in its stated scope; it is
not an exhaustive absence claim. Finite-Fock support does not by itself
exclude a nonzero traceless direction whose two small displacements
remain positive semidefinite and Wigner-positive.

## Route

The module uses the source's Laguerre expansion, complex Wigner function,
positive semidefinite trace-one matrices and midpoint definition of
extremality. Its `bsState` applies the frozen `BeamSplitter.beamSplitter`
at transmissivity $1/2$ to the tensor input, then the frozen
`ThermofieldMarginalModularSpectrum.countablePartialTraceRight` to the
`PureStateHandshake.rankOneDensity` of the joint amplitude and restricts
both visible indices to $\operatorname{Fin}(2N+1)$.
`BeamSplitter.beamUnitary_fock` supplies the Fock-basis action used in
`balanced_fock`. The repository rotation and the source rotation differ
by second-mode parity. The even-supported inputs are fixed by input
parity, and output parity disappears under the partial trace.

Write $T=(1+a^2)^2$, $h=2a^2$ and $b=\sqrt6\,a^2/4$. Then

$$
S_a=\begin{pmatrix}
1+3a^4/8&0&0&0&-b\\
0&2a^2&0&0&0\\
0&0&a^4/4&0&0\\
0&0&0&0&0\\
-b&0&0&0&3a^4/8
\end{pmatrix},\qquad
H_a=\begin{pmatrix}
a^2/2&0&0&0&-b\\
0&a^2&0&0&0\\
0&0&a^2/2&0&0\\
0&0&0&0&0\\
-b&0&0&0&0
\end{pmatrix}.
$$

The output is $\sigma_a=S_a/T$. Set
$K_a=H_a-(h/T)S_a$ and
$\epsilon_a=\min(1/2,a^2/4,3a^4/[16(3+a^2/2)])$.
The endpoints
$E_a(t)=(S_a+tK_a)/T$ for $t=\pm\epsilon_a/2$ belong to WPS,
have midpoint $\sigma_a$, and the positive endpoint differs from
$\sigma_a$ at entry $(4,4)$.

## Falsifier

An encoding mismatch in the source's Wigner kernel, finite pure input,
mode traced out, normalization or midpoint condition would invalidate
application to the source question. A publication already settling the
same question in the literature scope would invalidate the novelty
premise. The compilation uses no additional axiom beyond the accepted
standard set. The general parameter-family proof has no numerical
sampling hypothesis.

## Evidence

The private declarations below are in the settling module and on
`result`'s elaborated dependency path. All six family obligations are
**proved in Lean**:

| obligation | status | kernel-checked declaration |
| --- | --- | --- |
| F1: balanced output coefficients | proved | `family_output` |
| F2: $\sigma_a=S_a/T$ | proved | `bsState_family` |
| F3: $S_a+uH_a$ is PSD for $|u|\le\epsilon_a$ | proved | `perturb_psd` |
| F4: the two Wigner polynomial identities | proved | `familyS_wigner`, `familyH_wigner` |
| F5: endpoint trace, PSD and Wigner non-negativity | proved | `end_trace`, `end_psd`, `end_mem_WPS` |
| F6: midpoint and distinctness | proved | `end_midpoint`, `end_ne_state`, `family_not_extreme` |

The public settling declaration is `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.result`.
The axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

## Triage

### What the settlement shows

- **Mechanism — proved in this module.** For every $a>0$ the
  Gaussian-stripped Wigner polynomial of $S_a$ is $R_a^2+I_a^2$, where
  $R_a=1-a^2+4a^2|\alpha|^2-2a^2|\alpha|^4$ and
  $I_a^2=32a^2\operatorname{Re}(\alpha)^2\operatorname{Im}(\alpha)^2$.
  `familyS_wigner` and `familyH_wigner` prove that $H_a$ carries only
  $I_a^2$ with the same Fock support. `perturb_psd` proves the required
  PSD allowance, and `end_mem_WPS`, `end_midpoint`, `end_ne_state` and
  `family_not_extreme` prove the nontrivial midpoint decomposition.
  A split with these support, PSD, trace and distinctness properties
  obstructs extremality by the source's midpoint definition; a
  sum-of-squares identity alone does not establish those extra properties.
- **Source's proved case — proved by the paper's argument.** Section 5,
  Theorem “Beam-splitter states are extreme WPS”, source label
  `theorem:beam-splitter-states-are-extreme`, and its appendix “Beam-splitter states” proof
  establish extremality for inputs $|m\rangle,|n\rangle$.
  The conclusion is compatible with the refutation: both counterexample
  inputs have two nonzero Fock components when $a>0$. This source theorem
  is not separately formalized in the settling module.
- **What survives — open.** Extremality with one Fock input and one
  superposition remains a follow-up question. Extremality when the Wigner
  polynomial admits no split with the required support and PSD allowance
  also remains a follow-up question. Neither is asserted by `result`.
- **Unaffected results — proved by the paper's arguments.** The
  Vertigo-map statements of Section 4 and the Krein–Milman statement in
  Section 2 (Theorem “Krein–Milman theorem for WPS”, source label
  `th:Krein-Milman`, attributed there to the companion paper's Theorem 40)
  do not assume the universal question's positive answer. Their stated
  hypotheses and conclusions are unaffected by this refutation; the
  settling module does not separately prove them.

### Exact computation at the base instance

**Computed**, with tested scope exactly $a=1/2$, output Fock levels
$0,1,2,3,4$ and both signs. Command: `python3 /tmp/op-wps/check.py`,
exit code 0. SHA-256: `c13d73a943bb98492b53a84326a313d80197eae5d755587370c62289e771a16a`.
The complete script below is the orchestrator's exact check, reproduced
without modification. Save it as `check.py` and run `python3 check.py`
with SymPy installed.

It yields trace-one $\sigma$ and

$$
200\sigma=\begin{pmatrix}
131&0&0&0&-8\sqrt6\\
0&64&0&0&0\\
0&0&2&0&0\\
0&0&0&0&0\\
-8\sqrt6&0&0&0&3
\end{pmatrix}.
$$

Both symbolic Wigner identities have ratio one. At
$\epsilon=3/800$, $S\pm\epsilon H$ have Wigner polynomials
$R^2+(1\pm\epsilon)I^2$ and traces $2503/1600$ and $2497/1600$,
respectively. Each matrix has the zero eigenvalue from Fock level three;
the smallest positive numerical eigenvalues are
$0.000366953590422222$ and $0.000682572034392364$.
These eigenvalue readings are computations, not uniform PSD proofs;
the latter are supplied by `perturb_psd` for every $a>0$.

```python
import sympy as sp
from sympy import sqrt, Rational as Q, factorial, exp, assoc_laguerre
x,y=sp.symbols('x y',real=True)
al=x+sp.I*y; alc=x-sp.I*y
N=5  # Fock 0..4 output support
# two-mode BS: a^dag -> (a^dag + b^dag)/sqrt2, b^dag -> (a^dag - b^dag)/sqrt2
A,B=sp.symbols('A B')
def state_poly(coeffs,var):  # sum c_k var^k/sqrt(k!)
    return sum(c*var**k/sqrt(factorial(k)) for k,c in coeffs.items())
def bs_output(psi,phi):
    # psi(a^dag) phi(b^dag)|0>, substitute
    P=sp.expand(state_poly(psi,(A+B)/sqrt(2))*state_poly(phi,(A-B)/sqrt(2)))
    poly=sp.Poly(P,A,B)
    amp={}  # amplitude for |m>_a |n>_b : coeff * sqrt(m! n!)
    for (m,n),c in poly.terms(): amp[(m,n)]=sp.nsimplify(c*sqrt(factorial(m)*factorial(n)))
    rho=sp.zeros(N,N)
    for (m,n),c in amp.items():
        for (m2,n2),c2 in amp.items():
            if n==n2 and m<N and m2<N: rho[m,m2]+=c*sp.conjugate(c2)
    return sp.simplify(rho)
def Wkl(k,l):
    # source eq. wigner_funcion_fock_mn without the positive factor 2/pi e^{-2|a|^2}
    r2=4*(x**2+y**2)
    if l>=k: return (-1)**k*sqrt(factorial(k)/factorial(l))*(2*al)**(l-k)*assoc_laguerre(k,l-k,r2)
    return sp.conjugate(Wkl(l,k))
def Wpoly(M):
    return sp.expand(sp.simplify(sum(M[k,l]*Wkl(k,l) for k in range(N) for l in range(N))))
a=Q(1,2)
psi={0:1/sqrt(1+a**2),2:a/sqrt(1+a**2)}; phi={0:1/sqrt(1+a**2),2:-a/sqrt(1+a**2)}
sig=bs_output(psi,phi)
print('sigma*200 =',sp.simplify(sig*200)); print('trace',sp.simplify(sig.trace()))
b=sqrt(6)*a**2/4
S=sp.diag(1+b**2,2*a**2,a**4/4,0,b**2); S[0,4]=S[4,0]=-b
print('S/(1+a^2)^2 == sigma:', sp.simplify(S/(1+a**2)**2-sig)==sp.zeros(N,N))
H=sp.diag(a**2/2,a**2,a**2/2,0,0); H[0,4]=H[4,0]=-b
WS=Wpoly(S); WH=Wpoly(H)
Ra=1-a**2+4*a**2*(x**2+y**2)-2*a**2*(x**2+y**2)**2; Ia2=32*a**2*x**2*y**2
# compare up to a constant factor
cS=sp.simplify(WS/(Ra**2+Ia2)); cH=sp.simplify(WH/Ia2)
print('W(S)/(R^2+I^2) =',cS,' W(H)/I^2 =',cH)
e=min(Q(1,2),a**2/4,3*a**4/(16*(3+a**2/2)))
for s in (1,-1):
    M=S+s*e*H
    ev=[sp.N(v) for v in M.eigenvals(multiple=True)]
    print('sign',s,'eigs',ev,'trace',sp.nsimplify(M.trace()))
    print('  W poly matches R^2+(1+-e)I^2 * c:', sp.simplify(Wpoly(M)-cS*(Ra**2+(1+s*e*cH/cS)*Ia2))==0, ' coef', sp.simplify(1+s*e*cH/cS))
```

## ASSUMED-UNVERIFIED

Literature absence is restricted to the sources and searches recorded in
#14447. The parity equivalence and finite-support embedding into the
source's full WPS set are source-level mathematical interpretations, not
separately formalized infinite-dimensional bridges in this module.
The Lean claim uses exactly the preregistered finite-matrix convention.
Information-escape registration is paused under CLAUDE.md section 3.9.
