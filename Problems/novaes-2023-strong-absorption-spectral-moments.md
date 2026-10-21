---
slug: novaes-2023-strong-absorption-spectral-moments
bibkey: novaes2023absorption
doi: 10.1007/s10955-023-03183-7
url: https://arxiv.org/abs/2305.18235
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Transport/StrongAbsorptionMoments.result
---

# Novaes's strong-absorption spectral and Wigner moment conjectures

## Problem

M. Novaes, *Time delay statistics for chaotic cavities with absorption*,
arXiv:2305.18235v1, Section 5, p. 7, states: “We conjecture that
$(1/M)\langle\operatorname{Tr}(Q^n)\rangle$ is given by” Eq. (54) and that
$(1/M^n)\langle[\operatorname{Tr}(Q)]^n\rangle$ is given by Eq. (55), for every
positive integer $n$:

$$
\frac1{\gamma^n}-\frac n{\gamma^{n+1}}+\frac{n^2}{\gamma^{n+2}}
-\frac{(n+1)\bigl(n(5n-2)M^2+n(n+2)\bigr)}{6M^2\gamma^{n+3}}
+O(\gamma^{-n-4}),
$$

and

$$
\frac1{\gamma^n}-\frac n{\gamma^{n+1}}
+\frac{n\bigl((n+1)M^2+(n-1)\bigr)}{2M^2\gamma^{n+2}}
+O(\gamma^{-n-3}).
$$

Here $M\geq1$ is the channel number, $n\geq1$ is the order, and the model is
the finite-channel $\beta=2$ law with uniform absorption. The journal version
is *Journal of Statistical Physics* 190, 182 (2023), DOI
10.1007/s10955-023-03183-7.

### Statement echo

| Source clause | Formal counterpart |
| --- | --- |
| Every positive channel number | `claim54` and `claim55` quantify $M$ with $1\leq M$. |
| Every positive integer order | Both claims quantify $n$ with $1\leq n$. |
| Spectral observable $(1/M)\operatorname{Tr}(Q^n)$ | `traceQPow` is $(M:ℝ)^{-1}\sum_i(\gamma+p_1(i))^{-n}$. |
| Wigner observable $(1/M^n)[\operatorname{Tr}(Q)]^n$ | `tauW M γ p ^ n` is the normalized Wigner delay power. |
| Expectation under the stated law | Both integrals use `law M γ`. |
| The displayed coefficients and remainder orders | The two absolute remainder inequalities in `claim54` and `claim55` use the literal coefficients and powers. |
| The same external source conjectures both formulas | `claim` is the conjunction `claim54 ∧ claim55`. |

## Motivation

`D5/S3/Quantum/Transport/StrongAbsorptionMoments.result` proves the two
conjectured expansions for every $M\geq1$ and $n\geq1$, with constants that
may depend on $M$ and $n$.

## Gap

This is the named external conjecture preregistered in #19346. The screened
literature records the formulas as conjectures; completeness of that screen is
`ASSUMED-UNVERIFIED`.

## Route

The finite-channel law is expanded around the product Laguerre law. The first
two cross-density coefficients satisfy $E_0[D_2]=E_0[A D_2]=0$, while the
surviving finite-channel term is fixed by the cubic Laguerre moment
$E_0[C]=5M+1/M$. Polynomial moment jets and finite binomial truncation then
control every order $n$. The spectral and Wigner remainder estimates assemble
these identities into the two stated absolute bounds.

## Falsifier

The formal claim would fail if some $M\geq1$ or $n\geq1$ made either scaled
absolute error unbounded as $\gamma\to\infty$. A numerical discrepancy alone
would require checking the law, units and observable convention. The theorem
concerns the stated normalized law and these conventions.

## Evidence

The delivered modules are `D5/S3/Quantum/Transport/StrongAbsorption/SecondOrderDensity.lean`
and `D5/S3/Quantum/Transport/StrongAbsorptionMoments.lean`; the latter's
settling declaration is
`D5.S3.Quantum.Transport.StrongAbsorptionMoments.result`.
The supporting frozen owners are the Density, Foundations, LaguerreMoments and
StrongAbsorptionCumulants modules. The axiom closure of every public
declaration is contained in
$\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.

The four-slot escape audit for the newly public supporting theorems is
unfinished under [#19485](https://github.com/the-omega-institute/trureturing/issues/19485);
no `declared_validated` registration is asserted. The missing evidence is the
faithful source-family reconstruction, realization bridge, whole-family
intervention, sensitivity and observational-dependence evidence.

### Experiment

[The numerical check](https://github.com/the-omega-institute/trureturing-experiments/tree/a136bd997edd4f34114b1e7c17fecff5c7c920d1/docs/reports/novaes-2023-strong-absorption-moments-54-55)
is pinned to experiments commit `a136bd997edd4f34114b1e7c17fecff5c7c920d1`.
Command: `python3 check.py` in that directory; exit 0, `RESULT PASS`.
Script SHA-256: `959e27a9d059f1e44ecee913fbdb09b52df74f466eae7fd9f7bab49d74abe497`.
The tested scope is exactly Eq. (54) for $M=1,2$ with $n\leq4$ and $M=3$
with $n\leq3$, Eq. (55) for $M\leq3,n\leq3$, and the Eq. (52) comparison
at $n=2$ for every $M<20$. These finite computations corroborate the
all-$M,n$ Lean result without replacing it.

## Triage

### What the settlement shows

| Target item | Status and evidence |
| --- | --- |
| Mechanism: $E_0[D_2]=E_0[A D_2]=0$ | Proved in the kernel-checked path through `spectral_moments_low` and the density declarations used by `result`. |
| Mechanism: cubic Laguerre moment $E_0[C]=5M+1/M$ | Proved in the kernel-checked path through `laguerre_cubic_ibp`, `singleBaseExpectation_c`, and `pair_quadratic_sum`. |
| Escape live path through `result54`, `spectral_normalized_third_order`, `spectral_moments_low`, `baseExpectation_spectral_low`, `singleBaseExpectation_c`, `laguerre_cubic_ibp`, and `pair_quadratic_sum` | Proved: these declarations are used by the delivered settling proof. |
| Scope: Eqs. (54) and (55) for every $M\geq1,n\geq1$ | Kernel-checked: `D5.S3.Quantum.Transport.StrongAbsorptionMoments.result`. |
| Consequence with the pre-existing Eq. (58) settlement | Proved in the stated $\beta=2$ model: the spectral and Wigner moment orders are established alongside the cumulant result in `novaes-2023-strong-absorption-cumulants`. |
| Exact-series checker | Computed: the pinned experiment exits 0 with `RESULT PASS` on the finite scope listed in the experiment entry. |
| Uniformity of remainder constants as $M$ or $n$ varies | Open; the theorem permits constants depending on $M$ and $n$. |
| Higher asymptotic orders | Open; the result stops at the source's stated orders. |
| External prior-art completeness | Open and `ASSUMED-UNVERIFIED`; the literature screen does not establish worldwide completeness. |

The decisive structure is the cancellation of the first two cross-density
coefficients and the cubic Laguerre moment. Finite binomial truncation then
propagates the low-degree identities to every positive order. The proof does
not claim uniform constants, higher orders, or a settlement for other symmetry
classes.

## ASSUMED-UNVERIFIED

Literature-search completeness and the correspondence between the normalized
law and the physical random-matrix model remain `ASSUMED-UNVERIFIED`.
Numerical quadrature covers only the finite tested scope in the experiment
entry. Escape registration remains unfinished under #19485.
