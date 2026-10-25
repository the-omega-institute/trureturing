---
slug: kalmykov-karp-pfq-conjecture-one-function
bibkey: kalmykovkarp2017pfq
doi: 10.1007/s10476-017-0503-z
url: https://arxiv.org/abs/1611.06724
triage: theorem
motivation_gids:
  - D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.claim
  - D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.result
---

# The function clause of the shifted Gamma Turanian conjecture

## Problem

S. I. Kalmykov and D. B. Karp, *Log-concavity and Turán-type inequalities
for the generalized hypergeometric function*, arXiv:1611.06724v1, Section 3,
Conjecture 1, page 6, states verbatim:

> Conjecture 1. All conclusions of Theorem 3 hold for all α, β ≥ 0 if µ ≥ 1.

The relevant branch of Theorem 3, page 5, states verbatim (line breaks joined):

> Theorem 3. If p ≤ q and conditions (13) are satisfied, then ∆f (α, β; x) ≥ 0 for x ≥ 0, µ, β ≥ 0 and α ∈ N, where ∆f (α, β; x) is defined in (9) with f from (10). Moreover, if α ≤ β + 1, then δm ≥ 0 for all m ∈ N0.

For positive parameter vectors with $p\le q$, equations (9) and (10) are

$$
c(t)=\frac{\prod_i\Gamma(a_i+t)}{\prod_j\Gamma(b_j+t)},\qquad
f(\mu;x)=\sum_{n=0}^\infty c(\mu+n)\frac{x^n}{n!},
$$

$$
\Delta_f(\alpha,\beta;x)=f(\mu+\alpha;x)f(\mu+\beta;x)
-f(\mu;x)f(\mu+\alpha+\beta;x).
$$

Condition (13) is

$$
\frac{e_{q-j}(\mathbf b)}{e_{p-j}(\mathbf a)}
\le\frac{e_{q-j-1}(\mathbf b)}{e_{p-j-1}(\mathbf a)}\quad(0\le j<p).
$$

This dossier concerns $\Delta_f\ge0$ for all $x\ge0$, $\mu\ge1$ and
$\alpha,\beta\ge0$. It has no extra $\alpha\le\beta+1$ restriction.
Section 2, page 3, says (source text `p.txt`, line 167, line breaks joined):

> We will always assume that a₂ is not empty (i.e. p₂ ≥ 1), while all other subvectors are allowed to be empty.

It then says:

> In this section we will consider log-convexity of the function f (µ; x) defined in (3) under these assumptions.

Section 3 sets $a_1,b_1$ empty, identifying $a=a_2$ in (10). The first
sentence admits a standing-scope reading; the next admits a section-local
reading. The source-scope ambiguity is unresolved. The encoded claim imposes
$1\le p$.
Its nonempty-numerator counterexample refutes both that restricted universal
claim and the broader claim allowing $p=0$.

| Source object | Lean name in `D5.S3.Analytic.HypergeometricShiftTuran` |
| --- | --- |
| Gamma product ratio | frozen `Defs.coeff` |
| Condition (13) | frozen `Defs.cond13`, using `Defs.esymm` |
| Equation (10), real infinite sum | `FunctionResult.fval` |
| Equation (9) | `FunctionResult.turanian` |
| Universal function clause | `FunctionResult.claim` |
| Its negation | `FunctionResult.result` |

## Motivation

A negative Taylor coefficient does not imply a negative value of the function.
The function clause therefore requires control of the infinite series itself.
The example here uses convergent positive series with certified upper and
lower bounds.

## Gap

Status: **Refuted**, by `FunctionResult.result : ¬ FunctionResult.claim`.
The witness is $p=1$, $a=(1)$, $q=12$, $b_j=1/2$, $\mu=1$,
$\alpha=\beta=1/2$ and $x=2000$.

## Route

Put $f(3/2;2000)=\sqrt\pi A'$, $f(1;2000)=\pi^{-6}R$ and
$f(2;2000)=\pi^{-6}S$. The positive rational series have terms

$$
A'_n=\frac{\Gamma(n+5/2)/\sqrt\pi}{((n+1)!)^{12}}\frac{2000^n}{n!},\quad
R_n=\frac{(n+1)!}{(\Gamma(n+3/2)/\sqrt\pi)^{12}}\frac{2000^n}{n!},\quad
S_n=\frac{(n+2)!}{(\Gamma(n+5/2)/\sqrt\pi)^{12}}\frac{2000^n}{n!}.
$$

Here $\Gamma(n+k+1/2)/\sqrt\pi=(2(n+k)-1)!!/2^{n+k}$.
The Gamma recurrence gives convergence of all three original series by a
ratio bound of $1/2$ after index eight. Write $A'_{10},R_{10},S_{10}$ for sums
over $0\le n<10$. For $n\ge9$,

$$
\frac{A'_{n+1}}{A'_n}=\frac{2000(n+5/2)}{(n+1)(n+2)^{12}}
\le\rho:=\frac{74}{10^{11}}<1.
$$

Thus $A'\le A'_{10}+A'_{10}^{\rm term}/(1-\rho)\le1672/1000$, where
$A'_{10}^{\rm term}$ is the term of index ten, not the partial sum.
Positivity and finite-sum lower bounds give $R\ge R_{10}\ge136700$ and
$S\ge S_{10}\ge69$; the latter bounds already follow from the first three
terms. With $\pi<3.1416$,

$$
\pi^{13}(1672/1000)^2<136700\cdot69\le R_{10}S_{10}\le RS.
$$

Consequently $\Delta_f(1/2,1/2;2000)=\pi A'^2-\pi^{-12}RS<0$.
Condition (13) reduces to $2^{-12}\le12\cdot2^{-11}$ because $e_1(a)=e_0(a)=1$.

## Falsifier

A mismatch in the nonempty numerator, condition (13), shifts,
or function series would invalidate the correspondence. The three series
must be summable, the midpoint needs an upper bound, and the two outer
values need lower bounds. Finite truncation without a tail bound cannot
settle the function sign.

## Evidence

The source is arXiv:1611.06724v1, pages 5–6, equations (9), (10), (13),
Theorem 3 and Conjecture 1, journal DOI 10.1007/s10476-017-0503-z.
The settling Lean module is
`D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.lean`.
It imports the frozen definitions, proves geometric summability and compares
actual infinite sums. Its only public theorem is `result`.

The supplied literature check examined 15 OpenAlex citing works and the
existing repository dossiers and found no settlement of this function clause
in that scope. Literature completeness and priority remain unverified.
The candidate and initial numerical witness are from the Claude Code
orchestrator using Claude Opus 5.5; the formal implementation is by a Codex
CLI seat.

The programs are in
[the-omega-institute/trureturing-experiments, revision
0893152ffc04212b0981f35dc990d2784cf34dfd](https://github.com/the-omega-institute/trureturing-experiments/tree/0893152ffc04212b0981f35dc990d2784cf34dfd/experiments/kalmykov-karp-pfq-function),
directory `experiments/kalmykov-karp-pfq-function`.

- Exact rational certificate: command `python3 kk1f-cert-p1.py`, exit 0;
  script sha256 `441765f64beb57dfee52887ae429b7d172bce1d1c6d7784d60e36a278d1d647f`.
  At $a=(1),q=12,x=2000,N=10$, it forms exact rational partial sums and
  $A'_{\rm up}=A'_{10}+A'_{10}^{\rm term}/(1-\rho_{\rm scan})$.
  Here $\rho_{\rm scan}$ is the exact maximum of the successive ratios
  at indices 9 through 39. It evaluates the exact rational comparisons
  $R_{10}S_{10}>3.1416^{13}(A'_{\rm up})^2$ and
  $R_{10}S_{10}/(3.1416^{13}(A'_{\rm up})^2)>117/100$; both return true.
  All printed decimal values, including the quotient, are floating
  approximations only. The finite ratio scan itself does not certify an
  infinite tail; the Lean proof separately proves the uniform bound
  $\rho=74/10^{11}$ and the resulting full-series inequality.
- Finite grid: command `python3 kk1f-scan-p1.py`, exit 0; Python 3 with
  mpmath 1.3.0, 80 decimal digits, 400 terms per series;
  script sha256 `3757ab8fb2898097001947407220ff9deed14864ba92fc4a22ec0d4cd624fb2d`.
  It scans $x=10^{i/20}$ for $i=0,\ldots,140$, at
  $a=(a_0)$ with $a_0\in\{1,1/2,3/2,2\}$,
  $q\in\{8,10,12,14,16,18,20\}$, $b=(1/2)^q$, $\mu=1$ and
  $\alpha=\beta=1/2$. The table below gives only the $a_0=1$ rows.

## Triage

### What the settlement shows

- **PROVED (Lean, `FunctionResult.result`):** the universal function clause
  with $1\le p$ is false, so both source-scope readings are refuted.
- **PROVED (Lean, `FunctionResult.witness_negative`):** for
  $a=(1)$ and repeated half denominator parameters, the midpoint square
  is strictly smaller than the outer product. The geometric tail estimate
  establishes this for the full series at $q=12,x=2000$, independently of
  any coefficient-sign argument.
- **PROVED (frozen Lean, `D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult.half_parameter_family_neg`;
  correspondence proved here in prose):** the coefficient clause of
  Conjecture 1 is also false under the $p\ge1$ reading. That declaration
  gives a negative first coefficient for $a_2=(1)$, $b_2=(1/2)^q$, $q\ge7$,
  $a_1=b_1=\varnothing$, $\mu=1$, $\alpha=\beta=1/2$.
  Empty unshifted products equal one, so equation (3) is exactly (10).
  The degree-one Cauchy coefficient is therefore the coefficient in
  Conjecture 1; condition (13) is $2^{-q}\le q2^{-(q-1)}$ and
  $\alpha\le\beta+1$ holds. Thus all its hypotheses hold while that
  coefficient is negative. This frozen coefficient result is not on
  `FunctionResult`’s dependency path.
- **COMPUTED:** the finite grid experiment in Evidence gives the following
  minima of $\Delta_f/f(3/2;x)^2$ for $a=(1)$. These are finite grid
  minima, not certified minima over all positive $x$.

  | $q$ | grid minimum | $x$ |
  | --- | --- | --- |
  | 8 | +0.0319582 | $10^7$ |
  | 10 | −0.00243539 | ≈ 562.341 |
  | 12 | −0.171339 | ≈ 1995.26 |
  | 14 | −0.414154 | ≈ 7079.46 |
  | 16 | −0.746124 | ≈ 28183.8 |
  | 18 | −1.18496 | ≈ 112202 |
  | 20 | −1.75772 | ≈ 446684 |

- **PROVED (source, Theorem 3):** the integer-shift theorem is unaffected;
  the counterexample has $\alpha=\beta=1/2$. Its proof and integer-shift
  hypothesis are separate from the conjectured extension.
- **OPEN:** the sharp denominator-multiplicity threshold over all $x$;
  whether a lower bound on $\mu$ depending on $q$ restores the function
  conclusion; conditions on the denominator parameters restoring the
  real-shift conclusion; the balanced case $p=q$. No downstream statement
  may use the unrestricted function clause as a premise after this refutation.

## ASSUMED-UNVERIFIED

Literature coverage, citation-index completeness and priority are unverified.
The grid is a finite multiprecision computation with a fixed truncation,
not a proof of a uniform threshold.
