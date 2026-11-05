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
`D5/S3/Analytic/HypergeometricShiftTuran/Result.lean`; `Result.result` has type
exactly `¬ Defs.claim`.

The counterexample family and the numerical readings were obtained with the
assistance of the Claude Opus 5.5 model, and the Lean proof was drafted with the
assistance of the gpt-6.1-sol model.
Searches covered the works citing the paper in OpenAlex, arXiv and general web
search. Sokal's arXiv:2204.01045 refutes Conjecture 3 of the same paper, not
Conjecture 1. Liu's Zenodo record 22729164 concerns the 2012 reciprocal Gamma
conjecture of the same authors. No settlement of Conjecture 1 was found in that
scope; this is not a priority certification.

The numerical programs are in the-omega-institute/trureturing-experiments at revision c07877042ab4e3330e285b869fbe5d9e632a1c4b, directory `experiments/kalmykov-karp-pfq-turanian`
(`common.py` sha256 `99d8d5329e2fd15025ebf1f46f67bbfa245787a2628075c93c10b48a98c5d2d2`,
`coeff_scan.py` sha256 `25ff5ca287cbae1bddc7deb49d652f5fb2f35f51557831470564572de435cd4b`,
`random_control.py` sha256 `42d60926364e157fc9793fffb066dab72ef0973f7bc2d13a96f00b38b3a6e596`,
`turanian_scan.py` sha256 `c03c640c50f9cd684e99bc690cd46e542894219ef58990e1a5e5af24a9f9610c`),
run from that directory with Python 3.12 and mpmath 1.4.1.

## Triage

### What the settlement shows

The conjecture fails through strong log-concavity of the Gamma ratio
$c(t)=\Gamma(t+1/2)^{-q}$ for large $q$: the degree-one coefficient pairs the
balanced product $c(2)^2=\Gamma(5/2)^{-2q}$ against the unbalanced products
$c(3/2)c(5/2)$, and since $(32/(9\pi))^q>2$ for $q\ge6$ the balanced product
dominates. In this family both shifts equal $1/2$. Theorem 3 of the source
covers $\alpha\in\mathbb N$ and gives no guarantee for noninteger shifts, including
noninteger $\alpha\ge1$; the threshold $\mu\ge1$ does not compensate once $q$ is
large. The nearest statements that survive are
the integer-shift case of Theorem 3 and, numerically, the regime of few
denominator parameters.

- **PROVED (Lean, `Result.half_parameter_family_neg`, `Result.result`):** For
  $p=0$, $b=(1/2,\ldots,1/2)\in\mathbb R^q$, $\mu=1$, $\alpha=\beta=1/2$,
  $$\delta_1=2\cdot2^{-q}-\left(\frac{16}{9\pi}\right)^q-
  \left(\frac{16}{15\pi}\right)^q,$$
  and $\delta_1<0$ for every $q\ge6$; hence the coefficient clause of
  Conjecture 1 fails.
- **PROVED in the source, not formalized here:** Theorem 3's integer-shift case
  ($\alpha\in\mathbb N$) is unaffected.
- **COMPUTED (40-digit mpmath, outside the Lean development; command
  `python3 coeff_scan.py`, exit 0):** the closed form above agrees with the
  direct sum for $q=1,\ldots,8$, and $\delta_1<0$ already at $q=5$
  ($\delta_1\approx-4.03\cdot10^{-5}$). With $b=1/2$ and $\alpha=\beta=1/2$
  the least $q$ giving $\delta_1<0$ is $5,7,8,10$ for $\mu=1,1.5,2,3$. For
  $q=6$, $b=1/2$, $\mu=1$, on the grid $\alpha\in\{0.1,0.25,0.5,0.75,1,1.25,1.5,2\}$,
  $\beta\in\{0.1,0.25,0.5,0.75,1,1.5,2\}$, $\delta_1<0$ occurs only at points with
  $\alpha,\beta\le0.75$ and never for $\alpha\ge1$. For $p=1$, $a\in\{1,2,3\}$,
  $b=(1/2)^6$, $\mu=1$, $\alpha=\beta=1/2$: $\delta_1/\delta_0\approx-0.0024,-0.0073,-0.0122$.
- **COMPUTED (40-digit mpmath, outside the Lean development; command
  `python3 random_control.py 3 3000`, exit 0):** of 3000 random draws with
  $p\le q\le4$, positive parameters, $\mu\ge1$ and $\alpha,\beta\in[0,3]$,
  2095 satisfy condition (13), and none of them has a negative $\delta_m$ for
  $m\le15$.
- **COMPUTED (50-digit mpmath, series truncated at 400 terms, $x\in\{0,1/4,\ldots,99.75\}$,
  outside the Lean development; commands `python3 turanian_scan.py 0.01 7 10`,
  `python3 turanian_scan.py 0.5 6 11`, `python3 turanian_scan.py 1 7 11`, each
  exit 0):** with $p=0$, $\mu=1$, $\alpha=\beta=1/2$ and $b=(0.01,\ldots,0.01)$,
  $\min_x\Delta_f/f(\mu;x)^2$ is $\approx-2.2\cdot10^{-4}$ (at $x=25.25$) for
  $q=7$ and $\approx-6.0\cdot10^{-3}$ (at $x=36.5$) for $q=10$; for $b=1/2$
  ($q=6,11$) and $b=1$ ($q=7,11$) the minimum over the grid is positive. This
  is finite numerical evidence that the first conclusion of Conjecture 1
  ($\Delta_f\ge0$ for $x\ge0$) also fails; it is not a theorem.
- **OPEN:** whether the coefficient clause holds for $p=q$, where the
  log-concavity of the Gamma ratio is weaker; whether a lower bound on $\mu$
  depending on $q$ restores it; a proof that $\Delta_f<0$ somewhere on
  $(0,\infty)$ for the parameters above; and Conjecture 2 of the same paper.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority are
unverified. The numerical readings are finite multiprecision observations, not
proofs; the sign of $\Delta_f$ itself is established only on the stated grid
and truncation.
Four-slot escape registrations of the shared public Gamma and power helpers (and, for the two-block module, of `first_coefficient_eq`) are not completed; the gap is recorded at https://github.com/the-omega-institute/trureturing/issues/20966.
