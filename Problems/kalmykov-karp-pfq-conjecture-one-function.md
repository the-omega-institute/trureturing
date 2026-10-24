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
Empty numerator vectors are permitted and make condition (13) vacuous.

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
The witness is $p=0$, $q=12$, $b_j=1/2$, $\mu=1$,
$\alpha=\beta=1/2$ and $x=5000$.

## Route

Put $A=f(3/2;5000)$, $R=\pi^6 f(1;5000)$ and
$S=\pi^6 f(2;5000)$. Their terms are

$$
A_n=\frac{5000^n}{n!((n+1)!)^{12}},\quad
R_n=\frac{5000^n}{n!\big((2n+1)!!/2^{n+1}\big)^{12}},\quad
S_n=\frac{5000^n}{n!\big((2n+3)!!/2^{n+2}\big)^{12}}.
$$

The Gamma recurrence gives convergence of all three series by a ratio bound
of $1/2$ after index eight. Write $A_8,R_8,S_8$ for sums over $0\le n<8$.
For $n\ge8$,

$$
\frac{A_{n+1}}{A_n}=\frac{5000}{(n+1)(n+2)^{12}}
\le\rho:=\frac{5000}{9\cdot10^{12}}<1.
$$

Thus $A\le A_8+A_8^{\rm term}/(1-\rho)\le9/4$, where
$A_8^{\rm term}=5000^8/(8!(9!)^{12})$ denotes the term of index eight,
not the partial sum. Positivity and finite-sum lower bounds give
$R\ge R_8\ge161000$ and $S\ge S_8\ge34$. The latter rational bounds
already follow from the first two terms. With $\pi<3.1416$,

$$
\pi^{12}(9/4)^2<161000\cdot34\le R_8S_8\le RS.
$$

Consequently $\Delta_f(1/2,1/2;5000)=A^2-\pi^{-12}RS<0$.

## Falsifier

A mismatch in the source's empty-vector convention, condition (13), shifts,
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
in that scope. The implementation seat uses the supplied source text and
performs no network search. This is not an exhaustive literature or priority
claim. The candidate and initial numerical witness are from the Claude Code
orchestrator using Claude Opus 5.5; the formal implementation is by a Codex
CLI seat.

The programs are in the-omega-institute/trureturing-experiments at revision
ed97a20d9cffa80f649d016ef2f8f5fbe695e0b3, directory `experiments/kalmykov-karp-pfq-function`
(https://github.com/the-omega-institute/trureturing-experiments/tree/ed97a20d9cffa80f649d016ef2f8f5fbe695e0b3/experiments/kalmykov-karp-pfq-function).

- Exact rational certificate: command `python3 kk1f-cert.py`, exit 0;
  script sha256 `05a32f42fcfc62c1019fc72e8af647583c002cf985fef9b197dc320aafe4f3a5`.
  At $q=12,x=5000,N=8$, it checks
  $R_8S_8/(3.1416^{12}(A_8+A_8^{\rm term}/(1-\rho))^2)
  \ge1.2589$.
- Finite grid: command `python3 kk1f-scan.py`, exit 0; Python 3 with
  mpmath 1.3.0, 80 decimal digits, 400 terms per series;
  script sha256 `29176b8e5d52c1c84819fc7fd5b211c9843c6b30f38f9fdcfd6407e5b038acc6`.
  The grid is $x=10^{i/20}$ for $i=0,\ldots,120$, with
  $p=0$, $b=(1/2)^q$, $\mu=1$, $\alpha=\beta=1/2$.

## Triage

### What the settlement shows

- **PROVED (Lean, `FunctionResult.result`):** the universal function clause
  is false. For repeated small denominator parameters, reciprocal-Gamma
  weights can make the midpoint shift too weak at large positive $x$:
  here the midpoint square is strictly smaller than the outer product.
  The geometric tail estimate establishes this for the full series at
  $q=12,x=5000$, independently of any coefficient-sign argument.
- **COMPUTED:** the grid experiment above gives the following minima of
  $\Delta_f/f(3/2;x)^2$. Its command, exit code and script sha256 are in
  Evidence; programs: https://github.com/the-omega-institute/trureturing-experiments/tree/ed97a20d9cffa80f649d016ef2f8f5fbe695e0b3/experiments/kalmykov-karp-pfq-function.

  | $q$ | minimum | $x$ |
  | --- | --- | --- |
  | 9 | +0.0107104112229 | 707.945784384 |
  | 10 | −0.0612893268051 | 1258.92541179 |
  | 11 | −0.151378837043 | 2511.88643151 |
  | 12 | −0.258942746432 | 5011.87233627 |
  | 13 | −0.386446901146 | 8912.50938134 |
  | 14 | −0.535985171200 | 17782.7941004 |
  | 16 | −0.907908998656 | 70794.5784384 |
  | 18 | −1.39667800011 | 281838.293126 |

- **COMPUTED:** failure starts between $q=9$ and $q=10$ on this scanned
  grid. The same grid command and script sha256 apply; exit 0;
  https://github.com/the-omega-institute/trureturing-experiments/tree/ed97a20d9cffa80f649d016ef2f8f5fbe695e0b3/experiments/kalmykov-karp-pfq-function. This does not prove a sharp threshold over all $x$.
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
