---
slug: bao-wang-qiu-2022-elliptic-tail-exponent
bibkey: baowangqiu2022ellipticparameter
doi: 10.7153/mia-2022-25-64
triage: theorem
motivation_gids:
  - D5/S3/Analytic/EllipticTailExponent/Result.result
url: https://arxiv.org/abs/2112.13993
---

# The supremum of the elliptic remainder parameter exponent

## Problem

Bao, Wang and Qiu, *Monotonicity properties of the generalized elliptic
integrals with respect to the parameter*, arXiv:2112.13993v1,
Open problem 3.5:

> (2) What is the value of λ̄₁₀ in Lemma 3.2 (4) for n ∈ ℕ?

Lemma 3.2(4) states:

> Let λ̄₁₀ = sup_{a∈(0,1/2]} {λ₁₀(a)} for n ∈ ℕ₀. Then λ̄₁₀ = 2 if n = 0.

Equation (3.2), specialized to $c=1$, gives

$$g_{6,k}(a)=a(a)_k(1-a)_k,\qquad
(a)_k=\prod_{j=0}^{k-1}(a+j).$$

Write $S_n(a)=\sum_{k=0}^n g_{6,k}(a)/((k+1)(k!)^2)$.
Equation (3.6) is

$$\lambda_{10}(a)=\frac{a}{1-a}
\frac{\sin(\pi a)+\pi(1-a)\cos(\pi a)
-\pi(1-a)^2\sum_{k=0}^n\frac{g'_{6,k}(a)}{(k+1)(k!)^2}}
{\sin(\pi a)-\pi(1-a)\sum_{k=0}^n\frac{g_{6,k}(a)}{(k+1)(k!)^2}}.$$

### Formal reading

All Lean names below have prefix `D5.S3.Analytic.EllipticTailExponent`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| $g_{6,k}(a)$ | `Defs.g6` | Exactly $a(a)_k(1-a)_k$, with empty products equal to one. |
| $S_n(a)$ | `Defs.S` | The finite sum through index $n$, inclusive; `deriv (S n)` is its real derivative. |
| $\lambda_{10}(a)$ in (3.6) | `Defs.lambda10 n a` | The same trigonometric quotient, with truncation order explicit. |
| $a\in(0,1/2]$ | `Set.Ioc 0 (1 / 2)` | The left endpoint is excluded and the right endpoint included. |
| $\bar\lambda_{10}=2$ for all $n\in\mathbb N_0$ | `Defs.claim`, `Result.result` | `IsLUB (lambda10 n '' Set.Ioc 0 (1 / 2)) 2` for every `n : ℕ`, including zero. |
| Positive denominator and strict upper bound | `Result.denominator_pos`, `Result.lambda10_lt_two` | Both hold at every point of the stated interval. |
| Limit at zero from the right | `Result.tendsto_lambda10` | `Tendsto (lambda10 n) (𝓝[>] 0) (𝓝 2)` for each natural $n$. |

## Motivation

The settling declaration is `D5/S3/Analytic/EllipticTailExponent/Result.result`.
The source note is `D5/L/Asymptotics/baowangqiu2022ellipticparameter`.
The exponent controls the upper parameter threshold for the generalized
elliptic remainder in Theorem 3.1(2).

## Gap

Status: **Proved** for every natural truncation order, including zero.
The exponent is defined by the source quotient, whose denominator is
strictly positive on $(0,1/2]$. Its supremum is two and is not attained.
Open problem 3.5(1), concerning $\lambda_3^*$, is a separate question.

## Route

Put $d_k=(a)_k(1-a)_k/(k!)^2$ and $t_k=ad_k/(k+1)$.
The recurrence

$$(k+1)d_{k+1}-kd_k=(1-a)t_k$$

telescopes. The endpoint coefficient has the finite-product expression

$$(N+1)d_{N+1}=a\left(1-\frac{a}{N+1}\right)
\prod_{j=1}^N\left(1-\frac{a^2}{j^2}\right)
\longrightarrow\frac{\sin(\pi a)}{\pi}.$$

Euler's sine product therefore identifies

$$R_n(a)=\frac{\sin(\pi a)}{\pi(1-a)}-S_n(a)
=\sum_{k>n}t_k(a)=a^2U_n(a),$$

where

$$b_k(a)=\frac{1-a/k}{k(k+1)}
\prod_{1\le j<k}\left(1-\frac{a^2}{j^2}\right),\qquad
U_n(a)=\sum_{k>n}b_k(a).$$

For $k\ge1$ and $0\le a\le3/4$, the coefficients satisfy
$0<b_k(a)\le1/(k(k+1))$, $b'_k(a)<0$ and
$|b'_k(a)|\le4/(k(k+1))$. These summable majorants justify continuity
through zero and differentiation on $(0,3/4)$. Thus $U_n>0$, $U'_n<0$
and $U_n(0)=1/(n+1)$. The derivative identity within $(0,1/2]$ includes
the right endpoint and gives

$$\lambda_{10}(a)=\frac{aR'_n(a)}{R_n(a)}
=2+\frac{aU'_n(a)}{U_n(a)}<2.$$

The uniform bound on $U'_n$ and the positive limit of $U_n$ give
$\lambda_{10}(a)\to2$ as $a\to0^+$, proving the least-upper-bound claim.

## Falsifier

A natural $n$ and $a\in(0,1/2]$ with nonpositive source denominator or
$\lambda_{10}(a)\ge2$ would contradict the corresponding strict result.
A natural $n$ and an upper bound strictly below two for all such $a$
would contradict the least-upper-bound claim. The endpoint $a=1/2$
and the truncation $n=0$ are included.

## Evidence

`D5/S3/Analytic/EllipticTailExponent/Result.result` proves exactly
`Defs.claim` without additional hypotheses. Its principal dependencies
are `Result.lambda10_lt_two` and `Result.tendsto_lambda10`, using
`Result.lambda10_eq`, `Result.denominator_pos`, `Tail.d_product`,
`Tail.tail_eq_tsum`, `Bounds.deriv_b_bounds`, `Bounds.hasDerivAt_U`,
`Bounds.U_pos`, `Bounds.deriv_U_neg`, `Bounds.continuousOn_U`,
`Bounds.U_zero` and `Bounds.norm_deriv_U_le`.
Euler's sine product is `Real.tendsto_euler_sin_prod`; differentiation
of the infinite sum uses `hasDerivAt_tsum_of_isPreconnected`.
The axiom closure of `Result.result` is
`{propext, Classical.choice, Quot.sound}`.

The proof route was derived with the assistance of the ChatGPT Pro model.
The source settles $n=0$ by trigonometric estimates and states in
Remark 3.4 that the general value is hard to compute. Wen–Ma treat the
$K_a-E_a$ remainder of Theorem 3.1(1), a different quantity;
Bao–Wang–Zhang, DOI 10.1007/s13398-022-01258-w, treat a different
parameter dependence. No answer to Open problem 3.5(2) was found in
the searched scope of these works and the authors, title and exponent.
This scope does not establish exhaustive literature coverage or priority.

## Triage

- **PROVED.** For every $n\ge0$, $\lambda_{10}(a)<2$ on $(0,1/2]$
  (`Result.lambda10_lt_two`) and $\lambda_{10}(a)\to2$ as $a\to0^+$
  (`Result.tendsto_lambda10`); hence $\bar\lambda_{10}=2$
  (`Result.result`). The source denominator is positive
  (`Result.denominator_pos`).
- **PROVED.** The identity
  $\sin(\pi a)/(\pi(1-a))-S_n(a)=\sum_{k>n}t_k(a)$ is
  `Tail.tail_eq_tsum`, through the telescoping coefficient recurrence
  and the finite Euler product `Tail.d_product`.
- **PROVED in prose.** The map $\lambda_{10}$ sends $(0,1/2]$ onto
  $[1,2)$ and $\lambda_{10}(1/2)=1$. For each $k\ge1$,
  $$\frac{at'_k(a)}{t_k(a)}=1+a\sum_{j=0}^{k-1}
  \left(\frac1{a+j}-\frac1{1-a+j}\right)\ge1,$$
  with equality precisely at $a=1/2$. The exponent of a positive tail
  is the weighted average of these logarithmic derivatives, so it is
  greater than one in the interior and equals one at the endpoint.
  Continuity and the limit two give the entire stated range.
  The same argument applies to any nonnegative weights $w_k$ on positive
  indices with $0<\sum_{k\ge1}w_k/(k(k+1))<\infty$: the majorants
  multiplied by $w_k$ justify the derivative, endpoint and limiting
  arguments for $\sum w_kt_k$. Consequently the monotonicity thresholds
  of Theorem 3.1(2) are exactly one and two for every $n$ and every
  $r\in(0,1)$. The range, weighted extension and threshold consequence
  are not asserted as Lean theorems here.
- **COMPUTED.** In double precision, at
  $a=0.01,0.05,0.2,0.4,0.5$, respectively, $\lambda_{10}$ equals
  $1.99338,1.96336,1.79268,1.36181,1.0$ for $n=0$, and
  $1.99683,1.97882,1.83089,1.38598,1.0$ for $n=1$.
- **OPEN.** The value $\lambda_3^*$ of Open problem 3.5(1).

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified. The bounded literature scope does not imply that no
other settlement exists.
