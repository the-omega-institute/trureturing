---
slug: kalmykov-karp-pfq-conjecture-one-coefficients
bibkey: kalmykovkarp2017pfq
doi: 10.1007/s10476-017-0503-z
url: https://arxiv.org/abs/1611.06724
triage: theorem
motivation_gids:
  - D5/S3/Analytic/HypergeometricShiftTuran/Defs.claim
  - D5/S3/Analytic/HypergeometricShiftTuran/Result.result
---

# Coefficients of the shifted Gamma product Turanian

## Problem

S. I. Kalmykov and D. B. Karp, *Log-concavity and Turán-type inequalities
for the generalized hypergeometric function*, arXiv:1611.06724v1, Section 3,
Conjecture 1:

> All conclusions of Theorem 3 hold for all α, β ≥ 0 if µ ≥ 1.

For positive parameter vectors of lengths $p$ and $q$, put

$$
c(t)=\frac{\prod_{i=1}^p\Gamma(a_i+t)}{\prod_{j=1}^q\Gamma(b_j+t)},
\qquad
f(\mu;x)=\sum_{n=0}^{\infty}c(\mu+n)\frac{x^n}{n!}.
$$

Equation (9) defines

$$
\Delta_f(\alpha,\beta;x)=
f(\mu+\alpha;x)f(\mu+\beta;x)
-f(\mu;x)f(\mu+\alpha+\beta;x),
$$

and the coefficient of degree $m$ is

$$
\delta_m=\sum_{k=0}^m
\frac{c(\mu+\alpha+k)c(\mu+\beta+m-k)
-c(\mu+k)c(\mu+\alpha+\beta+m-k)}{k!(m-k)!}.
$$

For $p\le q$, condition (13) consists of

$$
\frac{e_{q-j}(\mathbf b)}{e_{p-j}(\mathbf a)}
\le\frac{e_{q-j-1}(\mathbf b)}{e_{p-j-1}(\mathbf a)}
\qquad(0\le j<p),
$$

where $e_0=1$. Empty parameter vectors are allowed; in particular, the
condition is vacuous at $p=0$. `Defs.claim` retains all parameter vectors and
all coefficient degrees with $\mu\ge1$, $\alpha,\beta\ge0$ and
$\alpha\le\beta+1$.

Formal correspondence. All Lean names below have prefix `D5.S3.Analytic.HypergeometricShiftTuran`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| Equation (10) coefficient ratio | `Defs.coeff` | Product of Gamma values for numerator parameters divided by the product for denominator parameters. |
| Equation (9) coefficient | `Defs.turanCoeff` | Exact finite Cauchy sum for the degree-$m$ coefficient of the shifted Turanian. |
| Condition (13) | `Defs.esymm`, `Defs.cond13` | Elementary symmetric functions and their consecutive ratio chain. |
| Conjecture 1 coefficient clause | `Defs.claim` | Universal nonnegativity for the printed parameter and shift range. |
| Negative coefficient family | `Result.half_parameter_family_neg` | For $p=0$, repeated $b_j=1/2$, $\mu=1$, $\alpha=\beta=1/2$, every $q\ge6$ gives $\delta_1<0$. |
| Refutation | `Result.result` | Exactly $\neg\,\texttt{Defs.claim}$. |

## Motivation

The coefficient conclusion is one of the conclusions asserted by the
conjecture. A single negative coefficient under these hypotheses suffices to
refute that assertion, independently of the value of the Turanian at
nonnegative real arguments.

## Gap

Status: **Refuted**. The coefficient clause fails for repeated denominator
parameters at $p=0$, while Theorem 3's integer-shift case remains outside this
counterexample. The first conclusion concerning the sign of $\Delta_f$ is
addressed below by finite numerical evidence only.

## Route

Take $p=0$, $b_j=1/2$, $\mu=1$, $\alpha=\beta=1/2$ and $m=1$. Then
$c(t)=\Gamma(t+1/2)^{-q}$, and the two summands give

$$
\delta_1=2(1/2)^q-
\left(\frac{16}{9\pi}\right)^q-
\left(\frac{16}{15\pi}\right)^q.
$$

The half-integer Gamma identities supply the displayed values. The bound
$\pi<3.15$ gives $32/(9\pi)>640/567>1$, and exact rational arithmetic gives
$(640/567)^6>2$. Monotonicity of natural powers gives
$(32/(9\pi))^q>2$ for $q\ge6$. Thus the middle term exceeds the positive
leading term, and the last term is strictly positive before subtraction.
Specialization at $q=6$ contradicts coefficient nonnegativity.

## Falsifier

A source mismatch concerning empty parameter vectors, the symmetric ratio
condition, or the conjecture's shift restrictions would invalidate this
correspondence. The finite sum must retain both degree-one terms and both
factorial denominators. The identity for the coefficient and the family
inequality must compile without additional hypotheses, proof placeholders, or
new axioms.

## Evidence

The mathematical source is arXiv:1611.06724v1, Section 3, with the journal
publication *Analysis Mathematica* 43 (2017), 567–580, DOI
10.1007/s10476-017-0503-z. The Lean sources are
`D5/S3/Analytic/HypergeometricShiftTuran/Defs.lean` and
`D5/S3/Analytic/HypergeometricShiftTuran/Result.lean`; both D5 modules build in
the repository CI. The registration mirror is compiled at landing. The axiom
closure of `Result.result` is to be recorded at landing, and is not stated here
as completed.

The refutation route was derived with the assistance of the ChatGPT Pro model.
OpenAlex citing works of the paper were checked. Sokal's arXiv:2204.01045
refutes Conjecture 3 of the same paper, not Conjecture 1. Liu's Zenodo record
concerns the 2012 reciprocal Gamma conjecture. This bounded literature scope
does not establish exhaustive citation-index coverage or priority.

## Triage

- **PROVED (Lean):** For $p=0$, $b=(1/2,\ldots,1/2)\in\mathbb R^q$,
  $\mu=1$, $\alpha=\beta=1/2$,
  $$\delta_1=2\cdot2^{-q}-\left(\frac{16}{9\pi}\right)^q-
  \left(\frac{16}{15\pi}\right)^q,$$
  and $\delta_1<0$ for every $q\ge6$; hence the coefficient clause of
  Conjecture 1 fails. Mechanism: $(32/(9\pi))^q>2$ for $q\ge6$, so the
  $k=1$ product term $\Gamma(5/2)^{-2q}$ exceeds the positive term.
- **COMPUTED (40-digit mpmath, not formalized):** $\delta_1<0$ already at
  $q=5$ ($\delta_1\approx-4.03\cdot10^{-5}$); with $b=1/2$ the least $q$
  giving $\delta_1<0$ at $\alpha=\beta=1/2$ is $5,7,8,10$ for
  $\mu=1,1.5,2,3$; for $q=6$, $b=1/2$, $\mu=1$ the sign of $\delta_1$ is
  negative on the grid points with $\alpha,\beta\le0.75$ sampled and
  nonnegative for $\alpha\ge1$ (consistent with Theorem 3); $p=1$,
  $a\in\{1,2,3\}$, $b=(1/2)^6$, $\mu=1$, $\alpha=\beta=1/2$ also give
  $\delta_1<0$ ($\delta_1/\delta_0\approx-0.0024,-0.0073,-0.0122$).
- **COMPUTED (50-digit mpmath, series truncated at 400 terms, $x$ on the
  grid of step $1/4$ in $[0,100)$):** With
  $b=(0.01,\ldots,0.01)\in\mathbb R^q$, $\mu=1$, $\alpha=\beta=1/2$,
  $\Delta_f$ itself is negative for $q\ge7$ on that grid, for example
  $\Delta_f/f(\mu;x)^2\approx-2.2\cdot10^{-4}$ at $(q,x)=(7,25.25)$ and
  $\approx-6.0\cdot10^{-3}$ at $(10,36.5)$; for $b=1/2$ and $b=1$ with
  $q\le11$ the scanned $\Delta_f$ stayed positive. This is finite numerical
  evidence that the first conclusion of Conjecture 1 also fails; it is not a
  theorem.
- **OPEN:** Whether the coefficient clause holds for $p=q$ (where
  log-concavity of the Gamma ratio is weaker); whether a lower bound on $\mu$
  depending on $q$ restores it; and Conjecture 2 of the same paper
  (log-concavity on $[1,\infty)$ for the two-block family).
- **PROVED in the source, not formalized here:** Theorem 3's integer-shift case ($\alpha\in\mathbb N$)
  is unaffected.
