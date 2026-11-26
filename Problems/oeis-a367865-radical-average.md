---
slug: oeis-a367865-radical-average
bibkey: oeis2026a367865
doi: null
url: https://oeis.org/A367865
triage: theorem
motivation_gids:
  - D5/S3/Arith/EulerFormDivisorSum
---

# OEIS A367865 radical average

## Problem

Velin Yanev's conjecture in OEIS A367865 equates a divisor sum with a
radical-weighted average. For every positive natural number $n$, the
identity in the rationals is

$$
\sum_{d\mid n} d\,\varphi(d)\,\mu(d)^2
= \frac{\operatorname{rad}(n)}{n}
  \sum_{k=1}^{n} \frac{\operatorname{rad}(nk)}{\operatorname{rad}(k)}.
$$

Here $d$ ranges over positive divisors, $\varphi$ is Euler's totient,
$\mu$ is the Möbius function, and $\operatorname{rad}(n)$ is the product
of the distinct primes dividing $n$. At $n=1$ both sums consist of their
single term at one, and the radical is the empty product.
[Source note](../Library/PrimeForms/oeis2026a367865.md)

## Motivation

The Euler-form divisor-sum development expresses a squarefree divisor
sum using prime support. Yanev's identity relates that same squarefree
support to the distribution of radical quotients across a complete interval.

## Gap

The earlier unformalized derivation groups by $\gcd(n,k)$ and evaluates
the two multiplicative expressions at prime powers. The formal target
is the complete rational equality on positive indices.
[Earlier derivation](https://github.com/the-omega-institute/trureturing/issues/18615)
[Formalization problem](https://github.com/the-omega-institute/trureturing/issues/34637)

## Route

Set $m=\operatorname{rad}(n)$. The prime-factor product identity gives
$\operatorname{rad}(nk)/\operatorname{rad}(k)=m/\gcd(m,k)$ for $k>0$.
The function $k\mapsto m/\gcd(m,k)$ has period $m$. Since $m$ divides $n$,
the interval from $1$ through $n$ contains $n/m$ full periods, which
cancel against the factor $m/n$. Grouping one period by gcd and
reindexing by complementary divisors gives $\sum_{d\mid m}d\,\varphi(d)$.
On the left, $\mu(d)^2$ is one on squarefree divisors and zero elsewhere.
The squarefree divisors of $n$ are exactly the divisors of $m$, giving
the same totient-weighted sum.

## Falsifier

A positive natural $n$ at which the displayed rational values differ
would refute the identity.

## Evidence

The frozen theorem
`D5/S3/Arith/Divisors/OeisA367865RadicalAverage.result` uses
`Nat.divisors` and `Finset.Icc 1 n` for the two finite sums. Its axiom
closure is `Classical.choice`, `Quot.sound`, and `propext`.
[Canonical formula and proof](../Blueprint/D5/S3/Arith/Divisors/OeisA367865RadicalAverage.md)

## Triage

Theorem. The resolution covers every positive natural index, including one.

## ASSUMED-UNVERIFIED

Exact-source escape registration remains open. Historical priority is
unverified.
[Registration issue](https://github.com/the-omega-institute/trureturing/issues/34659)
