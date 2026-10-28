---
slug: novaes-2023-strong-absorption-cumulants
bibkey: novaes2023absorption
doi: 10.1007/s10955-023-03183-7
url: https://arxiv.org/abs/2305.18235
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Transport/StrongAbsorptionCumulants.result
---

# Novaes's strong-absorption cumulant conjecture

## Problem

M. Novaes, *Time delay statistics for chaotic cavities with absorption*,
arXiv:2305.18235v1, Section 5, p. 7, states “we conjecture that, for n > 1,”
followed by Eq. (58):

$$
(-1)^n k_n(\gamma)
=\frac{(n-1)!}{M^{2n-2}\gamma^{2n}}
-\frac{(2n-1)n(n-1)!}{M^{2n-2}\gamma^{2n+1}}
+O(\gamma^{-2n-2}).
$$

Here $M\geq1$ is an integer channel number and $n\geq2$ is an integer
cumulant order. The symmetry class is $\beta=2$, with perfect coupling and
uniform absorption. The journal publication is *Journal of Statistical
Physics* 190, 182 (2023), DOI 10.1007/s10955-023-03183-7; its Eq. (65)
is the same conjecture.

### Statement echo

| Source clause | Formal counterpart |
| --- | --- |
| Every positive integer channel number | `claim` quantifies every natural `M` with `1 ≤ M`. |
| Every cumulant order greater than one | Every natural `n` with `2 ≤ n`. |
| Grabsch's inverse-rate law at $\beta=2$, $N=M$ | `Foundations.weight` is the literal joint density below; `Foundations.law` divides its measure by total mass. |
| Wigner time delay in dwell-time units | `Foundations.tauW` is $M^{-1}\sum_i(\gamma+x_i)^{-1}$. |
| The $n$th cumulant | `Foundations.kappa` is the $n$th derivative at zero of the observable's cumulant generating function. |
| Both coefficients of Eq. (58), including $(-1)^n$ | The literal unsimplified factorial, channel and absorption powers in `claim`. |
| $O(\gamma^{-2n-2})$ as $\gamma\to\infty$ | There exist real $C,\gamma_0$ with $\gamma_0>0$, and the absolute error is at most $C/\gamma^{2n+2}$ for every $\gamma\geq\gamma_0$. Constants may depend on $(M,n)$. |

Grabsch, arXiv:1909.01002v2, Eqs. (3)–(4), supplies the model law.
Writing the inverse delay rates as $\Gamma_i=\gamma+x_i$, its unnormalized
weight on $x_i\geq0$ and $0\leq y_j\leq\gamma$ is

$$
e^{-M(\sum_i x_i+\sum_j y_j)}\Delta(x)^2\Delta(y)^2
\prod_{i,j}(\gamma+x_i-y_j).
$$

The five conventions `weight`, `law`, `tauW`, `kappa`, `claim` are literal
to [#16825](https://github.com/the-omega-institute/trureturing/issues/16825).
The probability normalization and bounded observable are proved for this
law. Identification of this law with the physical random-matrix model is
the cited mathematical-model premise, rather than a theorem about a
physical cavity's dynamics.

## Motivation

`D5/S3/Quantum/Transport/StrongAbsorptionCumulants.result` proves `claim`.
The conclusion determines two coefficients for every finite channel number
and cumulant order, with an eventual absolute remainder estimate.

## Gap

This is the named external conjecture preregistered in #16825. No prior
all-order proof or refutation was found in the screened sources: Novaes's
later publications and Scholar list, arXiv:2604.13193, and the author-hosted
journal text. The journal's Eq. (65) matches arXiv v1's Eq. (58).
Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

The normalized inverse-rate law is a polynomial perturbation of two
Laguerre weights. Finite-product remainder estimates and exponentially
small cutoff tails give its first-order density expansion. Homogeneity
and polynomial integration by parts identify the ordinary and weighted
Laguerre moment generating functions. The observable's power remainder
then gives each rescaled moment to first order.

The triangular moment–cumulant recurrence transports this estimate by
strong induction in the order. Affine cumulant rescaling yields the
literal coefficients and the error exponent in Eq. (58). The supporting
content witnesses are `Foundations.pow_linear_remainder`,
`LaguerreMoments.cumulant_expansion_of_moments`, and
`Density.finiteProduct_remainder`; they are on `result`'s proof path.

## Falsifier

The formal claim would fail if, for some $M\geq1,n\geq2$, the scaled
absolute error were unbounded as $\gamma\to\infty$. A numerical discrepancy
alone would require checking the law, units and cumulant convention.
The theorem concerns the stated normalized law and these conventions.

## Evidence

The four mathematical modules and their Scribe mirrors are:

- `D5/S3/Quantum/Transport/StrongAbsorption/Foundations.lean`;
- `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.lean`;
- `D5/S3/Quantum/Transport/StrongAbsorption/Density.lean`;
- `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.lean`.

The settling theorem is `D5.S3.Quantum.Transport.StrongAbsorptionCumulants.result`.
The axiom closure of every public declaration is contained in
$\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.

The four-slot escape audit for all new public theorems, including `result`,
is unfinished under [#17044](https://github.com/the-omega-institute/trureturing/issues/17044).
The missing evidence is faithful source-family reconstruction, its
realization equivalence bridge, whole-family counter-intervention,
per-role sensitivity and actual observational dependence. No
`declared_validated` registration is asserted.

### Experiment

[The numerical check](https://github.com/the-omega-institute/trureturing-experiments/tree/58ac049c0008f37ced35f8e2920589b15c24b574/docs/reports/novaes-2023-strong-absorption-cumulants)
is pinned to experiments commit `58ac049c0008f37ced35f8e2920589b15c24b574`.
Command: `python3 check.py` in that directory; exit 0, `ALL_OK`.
Script SHA-256: `a539d2588b8f5d55e06d47d34f9dd5de046fa0327bb6e73b6c3d4999c0d4b82d`.

The tested scope is exactly $M=1$, 50-digit quadrature,
$\gamma\in\{50,100,200,400,800\}$, and orders $n=2,3,4,5$.
At $\gamma=800$, the error in the signed cumulant times
$\gamma^{2n+2}$ is respectively $30.782$, $302.426$, $2794.118$,
$26688.311$. The last three changes decrease in each tested order.
For $n=3$ the signed scaled error approaches $306$, corresponding to
$-306\gamma^{-8}$ in $k_3$, the $M=1$ coefficient of Eq. (56).
The second-moment error against Eq. (53), times $\gamma^6$, is $47.7022$
at $\gamma=800$. These are finite numerical readings, not a proof of
convergence or of a general next coefficient.

## Triage

### What the settlement shows

| Target item | Status and evidence |
| --- | --- |
| Mechanism: Laguerre perturbation and exact moments | Kernel-checked: `Density.law_polynomial_firstOrder`, `LaguerreMoments.laguerreH_near`, `LaguerreMoments.laguerreHw_near`, and `Foundations.observable_power_remainder` supply the density, weighted moments and observable estimates used by `result`. |
| Mechanism: propagation of the $O(\gamma^{-2n-2})$ error | Kernel-checked: `LaguerreMoments.cumulant_expansion_of_moments` uses strong induction through the triangular recurrence; `StrongAbsorptionCumulants.result` gives the final exponent. |
| Scope: every $M\geq1,n\geq2$ | Kernel-checked: `StrongAbsorptionCumulants.result`; constants may depend on both parameters. |
| Consequences for Eqs. (56)–(57) | Kernel-checked for their first two coefficients and the stated remainder only: specialize `result` to $n=3$ or $n=4$. The finer coefficients in those equations are outside this theorem. |
| Next coefficient at $n=3,M=1$ | Computed in the experiment entry: the tested signed scaled errors approach the source's value $306$. No convergence theorem or exact next coefficient is proved here. |
| General $\gamma^{-2n-2}$ coefficient | Open. The remainder estimate does not identify it. |
| Uniformity in $M$ | Open. The quantifier order permits constants depending on $M$. |
| Symmetry classes $\beta=1,4$ | Open. Their laws and coefficients are outside this statement. |
| Experiment | Computed: the pinned script, exit 0, `ALL_OK`, with exactly the scope and readings in the experiment entry. |
| Literature | Literature reading: the screened sources contain no prior all-order settlement; completeness is `ASSUMED-UNVERIFIED`. |

The decisive structure is a first-order moment estimate at every order,
combined with a recurrence that is triangular in that order. The proof
requires neither a uniform bound in $M$ nor the next asymptotic coefficient.
The source's uses of the conjectured first two coefficients have the stated
conditional formula discharged for this law; other source results gain no
additional coefficients or symmetry-class coverage from this theorem.

## ASSUMED-UNVERIFIED

Literature-search completeness and worldwide priority remain
`ASSUMED-UNVERIFIED`. The model-law correspondence uses Grabsch's published
law and Novaes's units. Numerical quadrature covers only the finite tested
scope and supplies no uniform or unbounded conclusion. Escape registration
is unfinished under #17044.
