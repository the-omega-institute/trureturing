---
slug: hiai-ruskai-2015-cq-contraction-coefficients
bibkey: hiairuskai2016contraction
doi: 10.1063/1.4936215
url: https://arxiv.org/abs/1508.03551v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.result
---

# Hiai–Ruskai Conjecture 6.3: exact qubit CQ contraction coefficients

## Problem

Hiai and Ruskai, *Contraction coefficients for noisy quantum channels*,
arXiv:1508.03551v1, Section 6, Theorem 6.2 and Conjecture 6.3 (PDF p. 19), state:

> Although the bounds in the above theorem are sufficient to disprove two conjectures as remarked below, we believe that they are optimal, i.e.,
>
> Conjecture 6.3. Equality holds in (45c) through (45e) above.

The map on complex qubit matrices is
$\Phi_{\alpha,\tau}(w_0I+\mathbf w\cdot\boldsymbol\sigma)
=w_0I+\alpha w_1\sigma_1+\tau w_0\sigma_3$.
For every $\alpha\geq0$, $0<|\tau|<1$ and $\alpha^2+\tau^2\leq1$,
the conjecture asks for the three equalities

$$
\begin{aligned}
\eta_{\widehat{\mathrm{WY}}}^{\mathrm{Riem}}(\Phi_{\alpha,\tau})
 &=\frac{\alpha^2(1+\sqrt{1-\tau^2})}{2(1-\tau^2)},\\
\eta_{x^{-1/2}}^{\mathrm{Riem}}(\Phi_{\alpha,\tau})
 &=\frac{\alpha^2}{\sqrt{1-\tau^2}},\\
\eta_{\mathrm{BKM}}^{\mathrm{Riem}}(\Phi_{\alpha,\tau})
 &=\frac{\alpha^2}{2\tau}\log\frac{1+\tau}{1-\tau}.
\end{aligned}
$$

The kernels are $(1+\sqrt{x})^2/(4x)$, $x^{-1/2}$ and
$\log(x)/(x-1)$, with the BKM value $1$ at $x=1$.
The contraction coefficient is the literal supremum of
$\langle\Phi(A),\Omega_{\Phi(\rho)}^\kappa(\Phi(A))\rangle/
\langle A,\Omega_\rho^\kappa(A)\rangle$ over all positive definite
trace-one $2\times2$ complex matrices $\rho$ and all nonzero traceless
Hermitian matrices $A$. The spectral action is
$(\Omega_\rho^\kappa(X))_{ij}=\kappa(\lambda_i/\lambda_j)X_{ij}/\lambda_j$.

## Motivation

`D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.result`
proves all three equalities over the stated parameter domain. The definitions
retain the full state and tangent optimization. The theorem includes
$\alpha=0$, negative $\tau$, and the completely positive boundary
$\alpha^2+\tau^2=1$ when $0<|\tau|<1$.

## Gap

[Preregistration #13774](https://github.com/the-omega-institute/trureturing/issues/13774)
identifies the Tier 1 external named conjecture and fixes the quantified
statement. Its literature reading reports MathDB problem 331132 with zero
solutions; Hirche–Rouzé–Stilck França, *Quantum* 6, 862 (2022), and
Ibarrondo–Sanz, arXiv:2607.04950, are cited as using the framework without
settling Conjecture 6.3. The latter citation checks are search-seat reported.
The source supplies lower bounds and the exact extreme-kernel formula (46).
The missing step for the three kernels is a matching upper bound over all
strict states and tangents.

The literature conclusion is `not-found-in-searched-scope`; it does not
establish exhaustive priority or the absence of an independent proof.

## Route

A spectral resolvent calculation evaluates the extreme metric for
$\kappa_s(x)=(1+s)(1/(x+s)+1/(1+sx))/2$. A scalar pinching identity gives
$4y_1^2/(1-w_1^2)$ as a common lower bound on the input metric. The
channel-output estimate bounds the numerator by this same quantity times
$\alpha^2/(1-((1-s)/(1+s))^2\tau^2)$.

Positive kernel representations integrate both inequalities without changing
the common denominator. The geometric representation uses
$4/(\pi(1+t^2))\,dt$ and $s=t^2$ on $[0,1]$; BKM uses
$2/(1+s)^2\,ds$; dual WY is the half mixture of the zero extreme kernel
and the geometric kernel. The pair $\rho=I/2$, $A=\sigma_1$ attains
all three upper bounds. Positivity of the input metric then makes the literal
supremum equal to the attained value.

## Falsifier

A counterexample to this statement would be an admissible pair
$(\alpha,\tau)$ and a strict density matrix with a nonzero traceless
Hermitian tangent whose ratio exceeds one of the displayed values, or a
failure of the matching lower bound. The common upper estimate covers every
such pair, and the centered state with the Pauli tangent realizes each value.
The singular output convention at $|\tau|=1$ is outside the statement.

## Evidence

The result is a kernel-checked theorem with type `claim`; no stronger
all-kernel public theorem is asserted. The geometric kernel directly reuses
`Real.rpow` at exponent $-1/2$. BKM directly reuses `dslope Real.log 1`,
which supplies the derivative value $1$ at the removable singularity.
`FiniteDimensional` supplies the Pauli matrices and
`ActualPureQubitGeometry` supplies `blochMatrix`.
The Library note `hiairuskai2016contraction` identifies the source, DOI,
definitions, and theorem locators.
For every Hermitian $\rho$, real-valued kernel $k$ and complex matrix $A$,
the live eigenbasis calculation proves
$\operatorname{Im}\operatorname{Tr}(A^*\Omega_\rho^k(A))=0$; hence
$\operatorname{Tr}(A^*\Omega_\rho^k(A))=(\mathrm{metric}(k,\rho,A):\mathbb C)$.
Information-escape registration is paused under CLAUDE.md §3.9.

## Triage

### What the settlement shows

- **Proved:** the three equalities above, including their sharpness, for all
  parameters in `admissible`. Evidence: the public `result` named in
  Motivation. Its private live proof path contains the pinching estimate,
  `geometric_pauli_bounds`, `bkm_pauli_bounds`, `dualWY_pauli_bounds`, the
  centered value identities and `eta_eq_of_metric_bound`. The mechanism
  retains all input states and tangents; it needs no assumption $\alpha>0$
  and treats both signs of $\tau$.
- **Open in Lean:** the general formula
  $\eta_\kappa^{\mathrm{Riem}}(\Phi_{\alpha,\tau})
  =\alpha^2\kappa((1-\tau)/(1+\tau))/(1+\tau)$ for every
  $\kappa\in\mathcal K$. The source's Proposition 2.1(ii) supplies the
  general representing measure, and the argument above gives the candidate
  route. This module instantiates only the three explicit kernels and does
  not formalize that arbitrary representing measure or the all-kernel
  conclusion.
- **Open in Lean:** monotonicity in the kernel for these channels,
  $\kappa_1\leq\kappa_2\Rightarrow
  \eta_{\kappa_1}^{\mathrm{Riem}}\leq\eta_{\kappa_2}^{\mathrm{Riem}}$.
  The source states this CQ property in Proposition 5.5 and remarks on it
  after Conjecture 6.3. The general formula would reduce it to evaluation at
  one positive argument. No general kernel-order theorem is delivered here.
- **Open in Lean:** the Lesniewski–Ruskai comparison with trace contraction
  and the Kastoryano–Temme geometric-maximality comparison. The two remarks
  immediately after Conjecture 6.3 already disprove them: the source gives
  $\eta_{\max}^{\mathrm{Riem}}=\alpha^2/(1-\tau^2)$ and
  $\eta^{\mathrm{Tr}}=\alpha$, so the former exceeds the latter when
  $\alpha>1-\tau^2$; on $\alpha^2+\tau^2=1$, $0<\alpha<1$, it gives
  $\eta_{x^{-1/2}}^{\mathrm{Riem}}=\alpha<1=\eta_{\max}^{\mathrm{Riem}}$.
  The settlement replaces all three lower bounds by exact coefficients
  throughout the admissible range, so comparisons involving the dual WY,
  geometric and BKM coefficients have their displayed exact values.
  Two explicit follow-up certification targets describe the additional
  comparisons: on $\alpha^2+\tau^2=1$, $0<\alpha<1$, certify
  $\eta_{\widehat{\mathrm{WY}}}^{\mathrm{Riem}}=(1+\alpha)/2>
  \alpha=\eta^{\mathrm{Tr}}$; for $\alpha>0$ throughout the non-unital
  admissible range, certify
  $\eta_{\widehat{\mathrm{WY}}}^{\mathrm{Riem}}-
  \eta_{x^{-1/2}}^{\mathrm{Riem}}=
  \alpha^2(1-\sqrt{1-\tau^2})/(2(1-\tau^2))>0$.
  These targets use the exact settled values rather than comparing two
  lower bounds. Formalized trace-contraction and maximal-metric comparators,
  and the certified comparison consequences, are not part of this module. The source's separate
  Theorem 6.4 disproof of Riemannian/relative-entropy coefficient equality
  also remains outside this delivery.
- **Open in Lean:** $\tau=0$. The source's unital-channel theorem gives the
  coefficient $\alpha^2$; the geometric and dual WY formulas specialize to
  it and the BKM expression has that limiting value. `admissible` excludes
  this endpoint, and the public `result` makes no endpoint claim.
- **Open in Lean:** $|\tau|=1$. The completely positive parameter condition
  forces $\alpha=0$, so the output state is pure and fails the strict output
  domain. Extending the metric to singular outputs needs a support or limiting
  convention. Neither such a convention nor an endpoint theorem is delivered.

The source's two cited disproofs already follow from its bounds and do not
require Conjecture 6.3. Their validity does not depend on this settlement.
Arbitrary-kernel, endpoint, trace, geodesic and relative-entropy extensions
are separate formalization targets.

## ASSUMED-UNVERIFIED

Worldwide novelty and priority are not proved by the scoped literature search.
The source and preregistration identify the external conjecture; the Lean
kernel establishes the stated three-kernel theorem within its formal system.
