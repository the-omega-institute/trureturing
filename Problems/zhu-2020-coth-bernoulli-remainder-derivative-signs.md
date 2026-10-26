---
slug: zhu-2020-coth-bernoulli-remainder-derivative-signs
bibkey: zhu2020completelymonotonicdegrees
doi: 10.3934/math.2020224
triage: theorem
motivation_gids:
  - D5/S3/Analytic/CothBernoulliDegree/Result.result
url: https://www.aimspress.com/article/doi/10.3934/math.2020224
---

# Derivative signs of the power-weighted hyperbolic cotangent remainder

## Problem

Zhu, *Completely monotonic integer degrees for a class of special functions*,
Conjecture 6.4:

> Let m ≥ 1, n ≥ 2, and pₙ(t) be defined as (2.2). Then ((−1)ⁿ tᵐ pₙ(t))^{(m+2n−2)} > 0 holds for all t ∈ (0, ∞) and ((−1)ⁿ tᵐ pₙ(t))^{(m+2n−1)} > 0 is not true for all t ∈ (0, ∞).

Equation (2.2) is

$$p_n(t)=\frac{\coth t}{t}
-\sum_{k=0}^{n}\frac{2^{2k}B_{2k}}{(2k)!}t^{2k-2}.$$

Put $P(t)=(-1)^nt^mp_n(t)$ and $M=m+2n$. The first clause is (6.12),
and the failure of universal strict positivity in the second clause is (6.13).

### Formal reading

All Lean names below have prefix `D5.S3.Analytic.CothBernoulliDegree`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| $p_n(t)$ in (2.2) | `Defs.p` | The finite Bernoulli sum includes $k=0$ and $k=n$; its powers of $t$ are integer powers. |
| $P(t)=(-1)^nt^mp_n(t)$ | `Defs.P` | The sign and the natural power $t^m$ are retained. |
| Integers $m\ge1$, $n\ge2$ | Natural `m`, `n` with `1 ≤ m`, `2 ≤ n` | The domains coincide on the stated positive integer ranges. |
| $P^{(M-2)}(t)>0$ for all $t>0$ | First conjunct of `Defs.claim` | The derivative is `iteratedDeriv (m + 2 * n - 2) (P m n)`. |
| $P^{(M-1)}(t)>0$ is not true for all $t>0$ | Second conjunct of `Defs.claim` | The universal strict positivity assertion is negated, with the same real argument domain. |
| Both clauses | `Result.result` | Exactly `Defs.claim`, with no additional hypothesis. |

The value assigned by real division and integer powers at zero is immaterial:
`PartialFraction.hasSum_iteratedDeriv_P` uses neighborhood agreement at each
positive argument to transfer all iterated derivatives.

## Motivation

The settling declaration is `D5/S3/Analytic/CothBernoulliDegree/Result.result`.
The source note is `D5/L/Asymptotics/zhu2020completelymonotonicdegrees`.
The two consecutive derivative orders locate the loss of positivity for a
power-weighted Bernoulli remainder throughout the full integer parameter range.

## Gap

Status: **Proved** for all integers $m\ge1$, $n\ge2$ and all positive real
arguments in (6.12). For (6.13), a single explicit positive argument,
$t=5\pi/(m+2n)$, gives a strictly negative next derivative for each parameter pair.

## Route

The cotangent partial fractions at an imaginary argument, followed by finite
geometric division and the even zeta values, give

$$P(t)=2\sum_{k=1}^{\infty}
\frac{t^M}{(\pi k)^{2n}(t^2+(\pi k)^2)},\qquad t>0.$$

On bounded real intervals, the quadratic reciprocal has derivative bound
$|D^j(1/(t^2+a^2))|\le j!a^{-j-2}$. The product rule supplies locally uniform
summable majorants for every derivative order. Hence the representation can be
differentiated term by term at every positive argument.

For $a>0$, the rational kernel has certificates

$$D^N\!\left[\frac{t^{N+2}}{t^2+a^2}\right]
=N!\left(1-\operatorname{Re}(1+it/a)^{-N-1}\right),$$

$$D^{N+1}\!\left[\frac{t^{N+2}}{t^2+a^2}\right]
=\frac{(N+1)!}{a}(1+(t/a)^2)^{-(N+2)/2}
\sin((N+2)\arctan(t/a)).$$

At $N=M-2$ the first certificate is strictly positive when $t>0$, since
$|1+it/a|>1$. Every weighted summand is positive, which proves (6.12).

At $t=5\pi/M$, normalize the second derivative series by
$2(M-1)!/\pi^{2n+1}$. The first term is at most $-1/8$, because

$$ (1+(5/M)^2)^{-M/2}\sin(M\arctan(5/M))\le-\frac18
\qquad(M\ge5).$$

The remaining terms sum to at most
$\sum_{k=2}^{\infty}k^{-2n-1}\le1/16$. Multiplying back gives

$$P^{(M-1)}(5\pi/M)\le-\frac{(M-1)!}{8\pi^{2n+1}}<0,$$

which proves (6.13).

## Falsifier

Integers $m\ge1$, $n\ge2$ and $t>0$ with $P^{(m+2n-2)}(t)\le0$ would
contradict the first clause. A parameter pair in this range for which the next
derivative were strictly positive at every positive argument would contradict
the second clause. In particular, it would contradict the explicit bound at
$5\pi/(m+2n)$.

## Evidence

`D5/S3/Analytic/CothBernoulliDegree/Result.result` proves exactly `Defs.claim`.
Its principal dependencies are `PartialFraction.P_eq_tsum`,
`PartialFraction.hasSum_iteratedDeriv_P`, `PartialFraction.iteratedDeriv_P`,
`Kernel.kernel_deriv_N`, `Kernel.kernel_deriv_N_pos`,
`Kernel.kernel_deriv_succ`, `Kernel.phase_bound` and `Kernel.tail_bound`.
The private `Result.negative_phase_sum` and `Result.negative_mixture` combine
the negative first term with the tail estimate and restore the weighted scale.
The axiom closure of `Result.result` is
`{propext, Classical.choice, Quot.sound}`.

The proof route was derived with the assistance of the ChatGPT Pro model.
Mahmoud–Qi, *Math. Inequal. Appl.* 25(1) (2022), settle the related $m=1$
degree bounds for the remainder. Bouali, arXiv:2202.01801, treats $m=0$ or
$n\in\{0,1\}$. No settlement of Conjecture 6.4 was found in the searched
scope, which also includes Xu–Cen, Qi arXiv:2003.05300v2,
Mahmoud–Qi arXiv:1912.07989v3, Bouali arXiv:2206.01527, Moustafa (2024),
and Qi's bibliography (July 2026). This bounded scope does not establish
exhaustive citation-index coverage or priority.

## Triage

- **PROVED.** Clause (6.12) holds for every integer $m\ge1$, $n\ge2$ and
  every $t>0$, by `Result.result`.
- **PROVED in prose.** Clause (6.13) has the stronger bound
  $P^{(M-1)}(5\pi/M)\le-(M-1)!/(8\pi^{2n+1})<0$, where $M=m+2n$.
  The private `Result.negative_mixture` proves this bound for the weighted
  derivative series; `PartialFraction.iteratedDeriv_P` identifies that series
  with the derivative of $P$, as used in `Result.result`.
- **PROVED.** The partial-fraction representation
  $P(t)=2\sum_{k\ge1}(\pi k)^{-2n}t^M/(t^2+(\pi k)^2)$ for $t>0$
  is `PartialFraction.P_eq_tsum`.
- **COMPUTED.** Evaluation at 120 decimal digits gives
  $P^{(M-1)}(5\pi/M)\approx-0.0169$ for $(m,n)=(1,2)$ and
  $\approx-0.949$ for $(m,n)=(3,2)$. These numerical evaluations are separate
  from the exact inequalities.
- **OPEN.** The exact completely monotonic degree of $t^mp_n(t)$ when it
  is not an integer is not determined here.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority are
unverified. The supplied bounded literature assessment has not been
independently rechecked against remote sources; the formal statement and
definitions are those displayed above.
