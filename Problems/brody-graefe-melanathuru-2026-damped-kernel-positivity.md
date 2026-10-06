---
slug: brody-graefe-melanathuru-2026-damped-kernel-positivity
bibkey: brodygraefemelanathuru2026phasespace
doi: 10.48550/arXiv.2605.02696
url: https://arxiv.org/abs/2605.02696v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.result
---

# The damped angular-momentum kernel positivity conjecture

## Problem

D. C. Brody, E.-M. Graefe and R. Melanathuru, *Phase-space measurements and decoherence for angular momentum systems*, arXiv:2605.02696v1, Section VI, after equation (52):

> For J > 1/2 we do not have an exact result, but it seems reasonable to conjecture that positivity is ensured provided that the damped σ kernel in (44), due to decoherence, becomes no sharper than the Husimi (σ = −1) kernel. That is, if e^{−½γL(L+1)} ( C(2J,L)/C(2J+L+1,L) )^{−σ/2} ≤ ( C(2J,L)/C(2J+L+1,L) )^{1/2} (53) for all L, then we restore positivity.

Equation (44) includes the complex conjugate of the harmonic:

$$
F^\sigma(\theta,\phi,t)=a_J\sum_{L,k}e^{-\gamma L(L+1)t/2}
\left(\frac{\binom{2J}{L}}{\binom{2J+L+1}{L}}\right)^{-\sigma/2}
\rho_{Lk}(0)\overline{Y_L^k(\theta,\phi)},\qquad a_J=(2J+1)^{-1/2}.
$$

The tensor entries and multipoles follow equations (12) and (13); the harmonics have the Condon–Shortley phase and the paper's factor $\sqrt{4\pi}$ (footnote 1). Equation (53) omits $t$ in print. The refuting example has $t=1$, where the printed and time-dependent readings coincide.

## Motivation

The criterion would turn a comparison of kernel multipole coefficients into a positivity guarantee for every density matrix. The frozen declaration `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.result` refutes that implication.

## Gap

Preregistration issue [#12737](https://github.com/the-omega-institute/trureturing/issues/12737) identifies a Tier 1 explicit conjecture. Its literature readings report: arXiv v1 as the only version; INSPIRE record 3151205 with zero citations; no relevant result in the stated MathDB title, author and Stratonovich–Weyl searches. Semantic Scholar was rate-limited for the orchestrator; the search seat reported zero citing works. These are attributed preregistration readings, `not-found-in-searched-scope`, rather than an exhaustive literature claim.

The quantified encoding follows [claim v2](https://github.com/the-omega-institute/trureturing/issues/12737#issuecomment-5976309067). Its judgement form follows [proof shape v2](https://github.com/the-omega-institute/trureturing/issues/12737#issuecomment-5975649163).

## Route

Use $n=2J=3$, $\sigma=1$, $\gamma=\log(20/11)>0$, $t=1$, and the lowest-weight projector $\rho=|J,-J\rangle\langle J,-J|$. In the descending magnetic basis this is `Matrix.single 3 3 1` on `Fin 4`. The observation is the north pole $\theta=\phi=0$.

For $L=0,1,2,3$, the binomial ratios are $1,3/5,1/5,1/35$. With $q=e^{-\gamma}=11/20$, equation (53) reduces to $q^{L(L+1)/2}\le r_L$. The nonconstant cases satisfy

$$
\frac{11}{20}<\frac35,\qquad
\frac{1331}{8000}<\frac15,\qquad
\frac{1771561}{64000000}<\frac1{35}.
$$

Only $k=0$ contributes at the north pole, and conjugating its real harmonic changes nothing. The multipoles are $1/2,-3/(2\sqrt5),1/2,-1/(2\sqrt5)$, so

$$
F^1(0,0,1)=\frac{1-3q+5q^3-7q^6}{4}
=-\frac{760927}{256000000}<0.
$$

## Falsifier

The public `claim` quantifies over every natural $n\ge2$, $\sigma\in[-1,1]$, $\gamma>0$, $t\ge0$, every multipole $L\le n$, every positive-semidefinite trace-one complex matrix on `Fin(n+1)`, and every real pair of angles. Under the coefficient inequalities it requires a nonnegative real part of $F$. The public `result : ¬ claim` provides the explicit counterexample above. Refuting this necessary condition refutes positivity itself.

## Evidence

The Lean source is `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.lean`. It uses the general Racah Clebsch–Gordan formula, the associated-Legendre definition, and the conjugated-harmonic formula for all parameters, without special branches for the counterexample. All evaluation proofs are local to `result`; no companion theorem is delivered. The density predicate is reused from `D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity`.

## Triage

Tier 1; resolution `Refuted` by `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.result`. `proof_shape: bind-only`; `escape_witness: none`; `admission_basis: open-problem-resolution` (#12737). The utility is `certified-instance`, with the typed refutation of this module's `claim`.

### What the settlement shows

- **Proved in `result`:** the witness is a density matrix, satisfies every coefficient inequality, and has strictly negative $F^1$ at the north pole. Its alternating multipole signs $+,-,+,-$ show the failure mechanism: comparing coefficient magnitudes with the Husimi kernel does not control their signed sum against the state's multipoles.
- **Proved consequence for equation (54):** for these parameters the proposed time is $t^*_1=\log35/(6\log(20/11))<1$, since $35<(20/11)^6$. The exact logarithmic comparison is also kernel-checked by a transient application of Mathlib's `Real.log_lt_log` and `Real.log_pow`. The witness subgoals in `result` certify the premise and negative value at $t=1$. Thus (54) cannot guarantee positivity at and beyond its proposed threshold.
- **Computed:** $t^*_1=0.9911698498073679045754\ldots$. For this state and pole, the polynomial $1-3q+5q^3-7q^6$ has one root in $(0,1)$, $q_0=0.5285888360868594491787\ldots$, corresponding to $t_0=1.0664184317871078065\ldots$ at the specified $\gamma$. Reproducible computation: `python3 -c 'import sympy as s; q=s.symbols("q"); p=1-3*q+5*q**3-7*q**6; print(s.polys.polytools.intervals(p,eps=s.Rational(1,10**15))); print(s.nroots(p,n=40,maxsteps=200)); print(s.N(s.log(35)/(6*s.log(s.Rational(20,11))),40)); print(s.N(-s.log(s.nroots(p,n=40,maxsteps=200)[1])/s.log(s.Rational(20,11)),35))'`. The root calculation concerns this one state and point, not positivity for all states and angles.
- **Open:** a kernel-checked sharp positivity time for the whole $J=3/2$, $\sigma=1$ distribution, or a sufficient coefficient condition that controls signs for every state and angle.
- **Source result unaffected:** the independent exact $J=1/2$ criterion (52) is stated for a different spin and is not contradicted by this witness. Its proof is not re-formalized here.
- **Effect on dependent conclusions:** the sufficient-positivity interpretation of (53) and the general positivity-time guarantee inferred in (54) fail. The counterexample does not challenge the tensor expansion, decoherence evolution, or the independent $J=1/2$ result.

## ASSUMED-UNVERIFIED

The literature readings do not establish worldwide priority. Correspondence between the general Racah and harmonic formulas and the paper's conventions is checked against the source; no separate universal equivalence theorem to an external convention library is delivered. Numerical root and time values are computations, not Lean theorems. Information-escape registration is paused under CLAUDE.md §3.9.
