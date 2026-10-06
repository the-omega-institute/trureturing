---
slug: caputa-di-giulio-loc-subsystem-lanczos-positivity
bibkey: caputadigiuliolo2026complexity
doi: 10.48550/arXiv.2606.20790
url: https://arxiv.org/abs/2606.20790v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.result
---

# Subsystem Lanczos positivity for general initial states

## Problem

P. Caputa, G. Di Giulio and T. Q. Loc, *Complexity Inequalities for Quantum
Subsystems*, arXiv:2606.20790v2, §3.1, printed p. 15 (PDF page 16), state:

> At present, however, we are unable to establish the sign of $\left(b_n^{(A)}\right)^2$ in full generality. Based on all the examples discussed in this manuscript, we conjecture that $\left(b_n^{(A)}\right)^2>0$ for every $n$, and hence that all the coefficients $b_n^{(A)}$ are real.

The source evolves a normalized pure state by $U(t)=e^{-\mathrm{i}Ht}$,
with a time-independent Hermitian Hamiltonian on a bipartite Hilbert
space. Its reduced density and fixed-normalization return amplitude are

$$
\rho_A(t)=\operatorname{Tr}_B(U(t)|\psi\rangle\langle\psi|U(t)^\dagger),
\qquad
R_A(t)=\frac{\operatorname{Tr}(\rho_A(t)\rho_A(0))}
 {\operatorname{Tr}(\rho_A(0)^2)}.
$$

Equations (3.3) and (3.5) define
$\mu_n^{(A)}=\partial_t^nR_A(t)|_{t=0}$ and
$(b_1^{(A)})^2=(\mu_1^{(A)})^2-\mu_2^{(A)}$.
The finite-dimensional $n=1$ clause quantifies over both subsystem
dimensions, every normalized pure state and every Hermitian Hamiltonian.
A negative first square disproves the full conjecture, including a
nonnegative reading that allows terminating zero coefficients.

## Motivation

The conjecture supplies the proposed reality of all subsystem Lanczos
coefficients. Preregistration
[#13270](https://github.com/the-omega-institute/trureturing/issues/13270)
classifies this explicitly published conjecture as Tier 1.
The declaration named in `motivation_gids` negates its first-coefficient
clause under the actual main-text definitions.

## Gap

The bounded literature qualification in #13270 is search-seat reported:
the v2 source retains the conjecture; the three inspected citing works
arXiv:2609.00126, 2607.21734 and 2606.21081 supplied no settlement.
The reported arXiv, MathDB and public formal-conjecture searches supplied
no equivalent solution. This is `not-found-in-searched-scope`; exhaustive
literature priority is `ASSUMED-UNVERIFIED`.

## Route

Use two qubits, ordered as $(00,01,10,11)$, with

$$
\psi=\frac35|00\rangle+\frac45|11\rangle,
\qquad H=X_A\otimes|0\rangle\langle0|_B.
$$

The Lean proof uses the existing `hamiltonianPropagator`,
`hamiltonianGenerator`, `rankOneDensity`, `partialTraceRight`, `qubitX`
and `basisProjector`. It differentiates the actual matrix exponential,
the conjugated density, partial trace and overlap. Its proof-local
readout is a continuous real-linear functional; it is not a substitute
public definition of the source amplitude or moments.

## Falsifier

The settlement requires normalization of this vector, Hermiticity of
this Hamiltonian, and the derivative computation from the fixed initial
purity denominator. A negative scalar supplied independently of those
definitions would not settle the question. The theorem has no explicit
premises and no auxiliary public identity theorem.

## Evidence

[`SubsystemLanczosPositivityRefutation.result`](../D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.lean)
proves `¬ claim`. Within that proof the normalized state and Hermitian
Hamiltonian give initial reduced purity $337/625$, first overlap
derivative zero, and second overlap derivative $126/625$. Therefore

$$
\mu_1^{(A)}=0,\qquad \mu_2^{(A)}=\frac{126}{337},\qquad
(b_1^{(A)})^2=-\frac{126}{337}<0.
$$

These values are proof-local facts used by `result`, not additional
exported declarations. The Scribe resolution claim records **Refuted**
against this dossier and the frozen theorem.

## Triage

Tier 1; **Refuted** by
`D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.result`.
The judgement form is `proof_shape: result: bind-only`,
`escape_witness: none`, and
`admission_basis: open-problem-resolution (#13270; Refuted)`.
The utility is `certified-instance` with a typed `refutes` edge to
`claim`. Information-escape registration is paused under CLAUDE.md §3.9.

### What the settlement shows

- **Proved in `result`:** the fixed initial overlap has positive second
  derivative $126/337$ and zero first derivative. The minus sign in the
  source's first-coefficient formula therefore gives a genuinely negative
  square, rather than a zero caused by termination. Normalization,
  Hermiticity, nonzero purity and both moments are established on the
  proof's live path.
- **Computed:** the full amplitude is
  $R_A(t)=1+(63/337)\sin^2t$, so $R_A(\pi/2)=400/337$.
  The reduced density is
  $\rho_A(t)=\frac1{25}\begin{pmatrix}9\cos^2t&9\mathrm{i}\cos t\sin t\\-9\mathrm{i}\cos t\sin t&16+9\sin^2t\end{pmatrix}$,
  with $\rho_A(\pi/2)=|1\rangle\langle1|$. Evolution purifies the
  initially mixed marginal. Its overlap with the initial marginal then
  exceeds the initial purity, explaining the positive second derivative.
- **Computed:** Appendix Eq. (128), with the printed
  $\mathcal L=\mathrm{i}[H,\cdot]$, evaluates to $+126/337$.
  With $\mathcal L=[H,\cdot]$ it evaluates to $-126/337$, agreeing with
  main-text Eq. (30), $(\mu_1^{(A)})^2-\mu_2^{(A)}$ (v2 Eq. (3.5)).
  This convention discrepancy does not alter the main-text definitions
  used by the refutation. The exact-check command below supports both
  computed items; it uses SymPy 1.14.0 and exits 0.
- **Computed:** the witness lies outside the appendix's commuting-state
  restriction. With $O=\rho_A(0)\otimes1_B$, the $(00,11)$ entry of
  $[O,\rho(0)]$ is $-84/625$ and the reverse entry is $84/625$.
  The exact command
  `python3 -c 'from fractions import Fraction as Q; print((Q(9,25)-Q(16,25))*Q(12,25))'`
  returns `-84/625`, exit 0. The initial mixed marginal permits a locally
  increasing overlap; this restriction matters to the sign argument.
- **Open in this module:** a classification of initial states and
  Hamiltonians ensuring nonnegativity. The nearest surviving statement
  is the source's Appendix C.1.1 commuting-state nonnegative result,
  including product initial states; it is literature-attested, not
  reproved here. Strict positivity additionally requires exclusion of
  stationary or terminating cases.
- **Open:** signs of higher coefficients under the commuting-state
  restriction and a general characterization of entangled states
  admitting a negative first coefficient. They are separate questions.
- **Proved scope and open consequences:** the single negative first
  coefficient refutes universal positivity under the main-text moment
  definitions. It does not refute the paper's individually computed
  examples or its restricted appendix result. Any general construction
  requiring real off-diagonal coefficients needs an additional condition;
  which broader complexity conclusions can be retained with complex
  coefficients remains open here.

### Exact computation

```sh
python3 - <<'PY'
import sympy as s
q, I = s.Rational, s.I
t = s.symbols('t', real=True)
psi = s.Matrix([q(3,5), 0, 0, q(4,5)])
H = s.kronecker_product(s.Matrix([[0,1],[1,0]]), s.diag(1,0))
assert H**3 == H and H == H.conjugate().T
U = s.eye(4) + (s.cos(t)-1)*H**2 - I*s.sin(t)*H
assert s.simplify(s.diff(U,t) + I*H*U) == s.zeros(4)
assert U.subs(t,0) == s.eye(4)
def trB(M):
    return s.Matrix(2,2,lambda a,c: sum(M[2*a+b,2*c+b] for b in range(2)))
rho0 = psi*psi.conjugate().T
psit = U*psi
rhoA = s.simplify(trB(psit*psit.conjugate().T))
A0 = trB(rho0)
purity = s.trace(A0*A0)
R = s.trigsimp(s.trace(rhoA*A0)/purity)
assert s.trigsimp(R - (1+q(63,337)*s.sin(t)**2)) == 0
assert R.subs(t,s.pi/2) == q(400,337)
assert rhoA.subs(t,s.pi/2) == s.diag(0,1)
mu1,mu2 = s.diff(R,t).subs(t,0),s.diff(R,t,2).subs(t,0)
eq30 = s.simplify(mu1**2-mu2)
def eq128(factor):
    L = lambda M: factor*(H*M-M*H)
    x = s.trace(trB(L(rho0))*A0)
    y = s.trace(trB(L(L(rho0)))*A0)
    return s.simplify((y*purity-x**2)/purity**2)
assert (eq128(I),eq128(1),eq30) == (q(126,337),-q(126,337),-q(126,337))
print('rhoA(t) =',rhoA)
print('R_A(t) =',R,'; R_A(pi/2) =',R.subs(t,s.pi/2))
print('rhoA(pi/2) =',rhoA.subs(t,s.pi/2))
print('Eq128 i[H,.] =',eq128(I),'; Eq128 [H,.] =',eq128(1),'; Eq30 =',eq30)
PY
```

Output: `R_A(t) = 1 + 63*sin(t)**2/337`, `R_A(pi/2) = 400/337`,
`rhoA(pi/2) = Matrix([[0, 0], [0, 1]])`,
`Eq128 i[H,.] = 126/337`, `Eq128 [H,.] = -126/337`,
and `Eq30 = -126/337`; exit 0. The checks derive the reduced state
from the propagator and verify its evolution equation, rather than
inserting the desired overlap values. These are exact symbolic
computations; the Lean theorem proves the moments needed for refutation.

## ASSUMED-UNVERIFIED

Exhaustive literature priority and all follow-up classifications are
unverified. The inherited literature readings are attributed to their
search producer in #13270. This module settles only the stated universal
positivity conjecture through its first-coefficient clause.
