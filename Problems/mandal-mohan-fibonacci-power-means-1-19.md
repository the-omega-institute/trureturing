---
slug: mandal-mohan-fibonacci-power-means-1-19
bibkey: mandalmohan2026integralmeans
doi: 10.48550/arXiv.2611.32519
url: https://arxiv.org/html/2611.32519v1#S1.Thmtheorem19
triage: theorem
motivation_gids:
  - D5/S3/Arith/Recurrence/MandalMohanFibonacciPowerMean.result
---

# Mandal and Mohan's Fibonacci Power Means Conjecture

## Problem

Conjecture 1.19 of Sagar Mandal and Mohan's *Integral Means of Fibonacci
Numbers: Divisibility, Density, and Arithmetic Structure* reads

> Let $k \geq 3$. Then
> $\frac{n^k}{1/F_1^k + 1/F_2^k + \cdots + 1/F_n^k} \in \mathbb N$
> if and only if $n=1,2$.

Here $n$ is the length of a nonempty prefix and $F_1=F_2=1$.
[Versioned source](https://arxiv.org/html/2611.32519v1#S1.Thmtheorem19)

## Motivation

The endpoint classifies the integrality of the stated rational quotient
for every natural prefix length $n \geq 1$ and exponent $k \geq 3$.
It extends the classification across exponents beyond Theorem 1.18.
[Theorem 1.18](https://arxiv.org/html/2611.32519v1#S1.Thmtheorem18)

## Gap

The source's 2-adic proof of Theorem 1.18 does not give the needed
obstruction for higher powers. A prime chosen separately for each prefix
can give an obstruction uniform in the exponent.

## Route

For $n \geq 11$, take a prime $r$ with
$\lceil n/2\rceil < r \leq n$ by Bertrand's postulate. Any prime divisor
$p$ of $F_r$ has first positive zero index $r$ by Fibonacci strong
divisibility, so $p$ is neither 2 nor 5. The rank divides $p-1$ or
$p+1$. That bound is even and $r$ is odd, so $p \geq 2r-1 > n$.
Only $F_r$ in the prefix is divisible by $p$.

Choose a common multiple $M$ of the Fibonacci numbers in the prefix.
If exactly one of the complementary factors $M/F_i$ is prime to $p$,
then their $k$-th powers sum to a number prime to $p$ for $k>0$.
If $p^e$ divides $M$, clearing denominators forces an integral quotient
to be a multiple of $p^{ek}$. For $p^e \geq n$ this contradicts the
quotient's strict bounds between zero and $n^k$.

For $n=5$ use the prime 5 at $F_5$. For $n=6$ use the power 8 at
$F_6$, with common multiple 120. For $7 \leq n \leq 10$ use the
prime 13 at $F_7$. At $n=4$ the cleared denominator
$2\cdot 6^k+3^k+2^k$ is greater than one and coprime to 24.
At $n=3$ integrality forces $2^{k+1}+1$ to be a power of three.
Reduction modulo eight forces an even exponent of three, and factoring
the difference of squares forces $k=2$. At $n=1,2$ the quotients
are $1$ and $2^{k-1}$.

## Falsifier

An admissible input $n \geq 3$, $k \geq 3$ with an integral quotient,
or a nonintegral quotient at $n=1$ or $n=2$ for an admissible exponent,
would falsify the corresponding direction of the equivalence.

## Evidence

`D5/S3/Arith/Recurrence/MandalMohanFibonacciPowerMean.result` proves both
directions with the quotient taken over the inclusive interval from 1 to
$n$. The proof uses the frozen first-zero characterization and prime
rank bound in `D5/S3/Arith/FibonacciRank`.

## Triage

- **Admission.** Tier 1, `open-problem-resolution`, with the positive
  settlement preregistered in [issue #34421](https://github.com/the-omega-institute/trureturing/issues/34421).

### What the settlement shows

- **Proved.** For every $n \geq 1$ and $k \geq 3$, the quotient is
  integral exactly at $n=1,2$.
  `D5/S3/Arith/Recurrence/MandalMohanFibonacciPowerMean.result`
- **Proved within the endpoint's proof.** If exactly one complementary
  factor after clearing denominators is prime to the prime $p$, the
  sum of the $k$-th powers of the complementary factors is prime to
  $p$ for every $k>0$. An integral quotient
  must then be divisible by $p^{ek}$ when $p^e$ divides the common
  multiple. The private declarations
  `pow_dvd_of_clearing_denominators`,
  `not_integral_of_cleared_denominators` and
  `not_integral_of_unique_prime_power` supply the divisibility and
  the contradiction when $p^e \geq n$ and $n \geq 2$.
  [Lean proof](../D5/S3/Arith/Recurrence/MandalMohanFibonacciPowerMean.lean)
- **Proved within the endpoint's proof.** For $k>0$, the length-four
  exclusion is `four_not_integral` and the lengths five through ten
  use `small_witness_not_integral`. For $n \geq 11$,
  `large_prime_witness` supplies a prime $p>n$ to
  `not_integral_of_unique_prime_power` in `conjecture_range`. The
  latter application needs only $k>0$.
  [Lean proof](../D5/S3/Arith/Recurrence/MandalMohanFibonacciPowerMean.lean)
- **Computed.** At $n=3,k=2$ the quotient is 4, so lowering the exponent
  bound to two would invalidate the classification $n=1,2$. The exact
  rational calculation prints `4`.

  ```sh
  python3 -c 'from fractions import Fraction; n, k = 3, 2; print(Fraction(n**k) / sum(Fraction(1, f**k) for f in (1, 1, 2)))'
  ```
- **Proved.** For nonempty prefixes and positive integer exponents,
  the integral cases are $n=1,2,3$ at $k=2$ and $n=1,2$ at every
  other exponent. Theorem 1.18 covers $k=1,2$ and
  `D5/S3/Arith/Recurrence/MandalMohanFibonacciPowerMean.result`
  covers $k \geq 3$. The prime-power obstruction handles the higher
  powers posed after Theorem 1.18.
  [Theorem 1.18](https://arxiv.org/html/2611.32519v1#S1.Thmtheorem18)
- **Open in this settlement.** Questions 1.20 and 1.21 concern
  arithmetic means and remain outside the reciprocal-power classification.
  [Question 1.20](https://arxiv.org/html/2611.32519v1#S1.Thmtheorem20)
  [Question 1.21](https://arxiv.org/html/2611.32519v1#S1.Thmtheorem21)

## ASSUMED-UNVERIFIED

The bounded prior-work screen in issue #34421 found the source preprint
and related results on primitive divisors. Priority beyond the screened
sources remains unverified.
