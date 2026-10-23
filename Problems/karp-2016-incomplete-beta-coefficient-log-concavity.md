---
slug: karp-2016-incomplete-beta-coefficient-log-concavity
bibkey: karp2016incompletebeta
doi: 10.1007/s10958-016-2958-z
triage: theorem
motivation_gids:
  - D5/S3/Analytic/IncompleteBeta/Result.result
url: https://arxiv.org/abs/1509.05120v1
---

# Coefficient-wise Wright log-concavity of normalized incomplete beta functions

## Problem

Karp, *Normalized incomplete beta function: log-concavity in parameters
and other properties*, §3, Conjecture 1:

> Conjecture 1 The coefficients φ_k are positive for all a, b, α, β > 0 and x ∈ (0, 1), so that b → x^{−a}(1 − x)^{−b} I_x(a, b) is strictly coefficient-wise Wright log-concave on (0, ∞) for these values of parameters.

Here equations (1), (3) and (4) give

$$c_j(a,b)=\frac{\Gamma(a+b+j)}{\Gamma(b)\Gamma(a+j+1)},\qquad
\varphi_n=\sum_{k=0}^n
\bigl[c_k(a,b+\alpha)c_{n-k}(a,b+\beta)
-c_k(a,b)c_{n-k}(a,b+\alpha+\beta)\bigr].$$

### Formal reading

All Lean names below have prefix `D5.S3.Analytic.IncompleteBeta`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| $c_j(a,b)$ in (1) | `coeff` in `Defs` | Exactly the displayed Gamma quotient, with natural index $j$. |
| $\varphi_n$ in (3), (4) | `phi` in `Defs` | The finite convolution difference over $0\le k\le n$. |
| $C_n(s,t)$ | `convolution` in `Moment` | $\sum_{k=0}^n c_k(a,s)c_{n-k}(a,t)$, with $a$ explicit. |
| The symmetric beta kernel | `W` in `Moment` | The finite powered kernel used in the moment representation below. |
| Conjecture 1 | `claim`, `Result.result` | Every real $a,b,\alpha,\beta>0$ and every natural $n$, with strict positivity. |
| $x\in(0,1)$ | No additional coefficient hypothesis | $\varphi_n$ does not depend on $x$, so this source quantifier is vacuous for the coefficients. |

## Motivation

The settling declaration is `D5/S3/Analytic/IncompleteBeta/Result.result`.
The source note is `D5/L/Asymptotics/karp2016incompletebeta`.
The coefficient assertion strengthens pointwise Wright log-concavity
by requiring positivity at every coefficient separately.

## Gap

Status: **Proved** for all positive real $a,b,\alpha,\beta$ and all
natural $n$, including $n=0$. No integrality restriction on either
shift is imposed. Conjecture 2 is not addressed here.

## Route

For $S=s+t$ and $s,t>0$, define

$$W(u)=\sum_{k=0}^n
\frac{u^{a+k}(1-u)^{a+n-k}}{\Gamma(a+k+1)\Gamma(a+n-k+1)}.$$

Termwise beta integration gives

$$C_n(s,t)=\frac{\Gamma(2a+S+n)}{\Gamma(S)}
\frac{1}{B(s,t)}\int_0^1u^{s-1}(1-u)^{t-1}W(u)\,du.$$

The kernel is continuous on $[0,1]$, invariant under $u\mapsto1-u$,
and strictly increasing on $[0,1/2]$. The derivative telescopes to

$$W'(u)=\frac{[u(1-u)]^{a-1}\bigl((1-u)^{n+1}-u^{n+1}\bigr)}
{\Gamma(a)\Gamma(a+n+1)},\qquad 0<u<1.$$

For fixed $m>0$, fold the beta density with shapes $m+d,m-d$ onto
$(0,1/2)$. It becomes

$$2[u(1-u)]^{m-1}\cosh\!\left(d\log\frac{1-u}{u}\right).$$

For $0\le d<e<m$, the ratio of the folded density at $e$ to that at
$d$ strictly decreases with $u$. The positive iterated integral of
$(W(y)-W(x))(p(y)q(x)-q(y)p(x))$ then makes the normalized mean at $e$
strictly smaller. Hence $C_n(m+d,m-d)$ strictly decreases with $d$.

Take $m=b+(\alpha+\beta)/2$. The two convolutions defining $\varphi_n$
have nonnegative half differences $|\alpha-\beta|/2$ and
$(\alpha+\beta)/2$. The first is strictly smaller because both shifts
are positive. Symmetry of the convolution and strict comparison give
$\varphi_n>0$.

## Falsifier

Positive real $a,b,\alpha,\beta$ and a natural $n$ with
$\varphi_n\le0$ would contradict the statement. Zero parameters and
zero shifts are outside its hypotheses.

## Evidence

`D5/S3/Analytic/IncompleteBeta/Result.result` proves exactly `claim`.
Its principal dependency is `Result.convolution_strictAnti_imbalance`,
which uses `Moment.convolution_eq_betaMean`, `Moment.W_continuousOn`,
`Moment.W_symm`, `Moment.W_strictMonoOn` and
`Comparison.betaMean_strictAntiOn`. `Moment.W_hasDerivAt` supplies the
kernel derivative. The beta integral and its integrability are reused
from `D5.S3.Analytic.KummerRatio.BetaIntegral`.
The axiom closure of `Result.result` is
`{propext, Classical.choice, Quot.sound}`.

The proof route was derived with the assistance of the ChatGPT Pro model.
The source proves $\alpha\in\mathbb N$, $\beta\ge\alpha-1$ and states
the general positive-shift case as Conjecture 1. No settlement was found
in the supplied bounded literature scope: the source identifier and title,
coefficient-wise and Wright log-concavity of incomplete beta functions,
Kalmykov–Karp arXiv:2305.09029, Karp–Zhang (FCAA 2024),
Askitis arXiv:1710.09708 and the author's publication index.
The Kalmykov–Karp statement concerns a weaker claim for related series.
The author's 2023 seminar slides also present the conjecture as open.
This scope does not establish exhaustive citation-index coverage or priority.

## Triage

- **PROVED.** $\varphi_n>0$ for all $a,b,\alpha,\beta>0$ and every
  natural $n$, by `Result.result`.
- **PROVED.** $C_n(s,t)$ strictly decreases in $|s-t|$ at fixed $s+t$,
  by `Result.convolution_strictAnti_imbalance` and convolution symmetry.
- **PROVED.** The normalized beta mean of a bounded continuous function
  symmetric about $1/2$ and strictly increasing on $(0,1/2]$ strictly
  decreases in the imbalance, by `Comparison.betaMean_strictAntiOn`.
  Continuity on the compact unit interval supplies boundedness.
- **PROVED in prose.** Equations (1), (3), (4) and the Cauchy product give
  $\varphi_{a,b,\alpha,\beta}(x)=x^{2a}(1-x)^{2b+\alpha+\beta}
  \sum_{k\ge0}\varphi_kx^k$ for $0<x<1$; this series identity is not
  asserted as an additional Lean theorem.
- **OPEN.** Conjecture 2, the $a$-parameter coefficient-wise Wright
  log-convexity for $0<b<1$ and log-concavity for $b>1$, is not addressed here.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified. Independent external-source confirmation of the supplied
bounded literature findings is unverified.
