---
slug: mccormack-zelinsky-2023-question-43
bibkey: mccormackzelinsky2023weightedamgm
doi: 10.48550/arXiv.2312.11661
url: https://arxiv.org/abs/2312.11661v4
triage: theorem
motivation_gids:
  - D5/S3/Arith/Abundancy/StrongPseudoperfectDensity.result
---

# Strongly pseudoperfect integers have zero natural density

## Problem

McCormack and Zelinsky, arXiv:2312.11661v4, page 18, Question 43:

> Does SP have positive natural density?

Wang and Zelinsky, *Strongly Pseudoperfect Numbers*, arXiv:2609.36068v3,
Section 4, Question 22 repeat the same question. Their abstract defines a
strongly pseudoperfect number as a positive integer n with a subset S of its
positive divisors such that d belongs to S if and only if n/d belongs to S,
and the sum of S is 2n. The definition does not require 1 and n to belong to S.

The Lean predicate includes 0 < n and exactly these finite-subset conditions.
The counting function uses the interval 1 <= n <= X. The conclusion is

`Tendsto (fun X : Nat => (spCount X : Real) / X) atTop (nhds 0)`.

A positive limit for the same function would contradict uniqueness of real
limits. This is the negative answer to the question about positive density.

## Motivation

The source contrasts the positive density of ordinary pseudoperfect integers
with the zero density of perfect integers. It connects Question 43 to an
obstruction in the study of odd perfect numbers. A distribution statement for
all strongly pseudoperfect integers distinguishes these two density behaviors;
it does not decide the existence of odd perfect numbers.

## Gap

The condition p <= sigma(m) from Wang and Zelinsky's Proposition 4 bounds the
size of an allowed prime extension mp. It does not bound how many primes can
occur for each m strongly enough to give the density limit. Ordinary counting
bounds for exceptional cofactors also do not control their reciprocal mass.

## Route

For q prime and q not dividing m, let T be the intersection of a complementary
sum set for mq with the divisors of m. The set is the disjoint union of T and
its complements. Put A = sum over T of d and B = sum over T of m/d. Then

$$
A+qB=2mq,\qquad A>0,\qquad q=\frac{A}{2m-B}.
$$

The image of the powerset of the divisors of m therefore contains every
allowed q, and has cardinality at most 2^tau(m).

For Omega counting prime factors with multiplicity, tau(m) <= 2^Omega(m),
and 2^4 < (3/2)^7 gives tau(m)^(4/7) <= (3/2)^Omega(m). A finite Euler
product gives

$$
\sum_{1\le m\le X}\frac{(3/2)^{\Omega(m)}}m
\ll (\log X)^{3/2}.
$$

Its geometric ratio at p = 2 is 3/4. Comparing the square of each local factor
with (1-1/p)^(-3)(1+4/p^2), and applying the weak Mertens product bound, proves
the displayed estimate.

Let L = log X, a = 15/16, b = 31/32, z = exp(L^b), and Y = floor(z).
The four contributions to the count, after division by X, are bounded by
constant multiples of

$$
(1+L^b)e^{-L^{1/32}},\quad e^{-L^b},\quad
\exp((\log2)L^a-L^b),\quad L^{-1/224}.
$$

The first term counts (Y+1)-smooth integers by Rankin's inequality and the
existing tilted Euler-product bound. The second counts multiples of q^2 with
q > Y by a finite inverse-square sum. Every remaining integer has a
representation mq with q > Y prime and q not dividing m. For tau(m) <= L^a,
the finite prime image gives the third term. For the other cofactors, their
reciprocal mass is at most L^(-15/28) times the weighted Omega sum.
Chebyshev's bound applies at X/m >= Y+1 > z, and supplies the additional
factor L^(-b). The resulting exponent is 3/2 - 15/28 - 31/32 = -1/224.
All four terms tend to zero.

## Falsifier

The complementary subsets must not be restricted to contain 1 and n.
Omega must count multiplicity. The prime two must be retained in the weighted
Euler product. The Chebyshev logarithm can only be bounded below by log z
while m <= X/(Y+1). Passing from the count to a limit must include all positive
integers and every sufficiently large X.

## Evidence

**Proved in Lean:** `StrongPseudoperfectDensity.result` is the exact zero-density
limit for the positive-integer predicate and the inclusive counting interval.
Its proof includes the finite prime image, weighted moment, finite four-class
cover, Rankin bound, and eventual estimates. It has no additional number-theory
hypotheses.

**Proved on paper:** the displayed bound gives SP(X) << X/(log X)^(1/224).
The public Lean conclusion asserts the limit, not a separate Big-O theorem.

The literature assessment in preregistration #31684 searched the question,
authors, strongly pseudoperfect density, and related classical sparse sets.
Wang and Zelinsky v3 explicitly retain the question as Question 22. This bounded
assessment is not a claim of exhaustive literature coverage or worldwide priority.

## Triage

- **Proved in Lean:** Question 43 has a negative answer through the zero-density
  limit. The mechanism combines finite prime-subset encoding with a reciprocal
  weighted Omega moment, rather than Proposition 4 alone.
- **Proved on paper:** the quantitative upper bound SP(X) << X/(log X)^(1/224).
  The Lean intermediate envelope has four explicit vanishing terms; no separate
  public quantitative asymptotic declaration is asserted.
- **Literature:** Wang and Zelinsky Proposition 4 excludes mp when p > sigma(m).
  The finite prime-image argument controls the number of allowed primes instead.
  The proposition and the counting estimate serve different purposes.
- **Unresolved:** Wang and Zelinsky Question 21 about powers of a strongly
  pseudoperfect number. A zero-density limit neither constructs the required
  representations nor supplies a counterexample.
- **Unresolved:** Wang and Zelinsky Question 23. No answer to that adjacent
  question is asserted by this density theorem. The implications of the density
  result for Question 23 remain unverified.
- **Unresolved:** classification or existence questions specifically about
  strongly pseudoperfect perfect squares. Zero density among all integers does
  not control relative density among squares or classify their representations.
- **Literature; unresolved:** the odd-perfect-number motivation of Question 43.
  The density alternative is decided by the limit, but the structural
  obstruction and the existence of odd perfect numbers are not settled here.

## ASSUMED-UNVERIFIED

Worldwide priority and exhaustive coverage of subsequent literature are
unverified. The explicit sum 2n in the strongly pseudoperfect definition is
located in Wang--Zelinsky's abstract. The implications of the density result
for Question 23 and the odd-perfect-number motivation remain unverified.
No separate result about either is claimed beyond the density limit.
