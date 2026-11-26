---
slug: mccormack-zelinsky-2023-question-44
bibkey: mccormackzelinsky2023weightedamgm
doi: 10.48550/arXiv.2312.11661
url: https://arxiv.org/abs/2312.11661v4
triage: theorem
motivation_gids:
  - D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity.result
---

# Strong pseudoperfection is a strong restriction among Euler forms

## Problem

McCormack and Zelinsky, arXiv:2312.11661v4, page 19, Question 44:

> Is being a strongly pseudoperfect number a strong restriction, a weak restriction, or neither?

Pages 18--19 define E as the numbers q^s m^2, where q is prime,
q and s are congruent to one modulo four, and gcd(q,m) = 1.
The variables are positive integers; the definition does not separately impose
oddness on m. A property S is strong if E_S(x)/E(x) tends to zero, and weak
if the same quotient tends to one.

The Lean predicate `EulerForm` uses natural numbers q, s, m, with q prime,
q % 4 = s % 4 = 1, m positive, and q coprime to m. The congruence of s
implies that s is positive. The existing `StronglyPseudoperfect` predicate
requires a complementary-divisor-closed subset summing to twice the positive
integer; it does not require the subset to contain 1 or n.

Both counts use 1 <= n <= X and count integers rather than representations.
The conclusion is

`Tendsto (fun X : Nat => (eulerSPCount X : Real) / eulerCount X) atTop (nhds 0)`.

Real thresholds give the same counts at their natural-number floors, so the
natural-threshold limit expresses the source's relative-density definition.

## Motivation

Every odd perfect number has Euler's form. The source observes that finitely
many weak necessary properties cannot exclude almost all Euler forms. A strong
necessary property therefore supplies a different kind of restriction. Its
relative density must be measured inside E; ordinary density among all positive
integers does not answer this question.

## Gap

For fixed m, the prime-extension encoding gives a pointwise inequality
q <= sigma(m^2). A uniform bound on sigma(m^2) alone does not provide the
desired relative density. The argument needs its mean over square factors,
a count covering all exponents s congruent to one modulo four, and a
sufficiently large denominator for every large threshold.

## Route

For s=1, q does not divide m^2. The complementary-divisor encoding places q
in the image of the divisor powerset of m^2 under the natural-number quotient
A/(2m^2-B). Since this quotient is at most A, q <= sigma(m^2).

A divisor d of m^2 can be represented as ab^2 with a squarefree. The equivalence
ab^2 divides m^2 if and only if ab divides m needs no condition gcd(a,b)=1.
An injective choice of this representation and finite summation give

$$
\sum_{m\le T}\sigma(m^2)
\le T\sum_{a\le T}\lfloor T/a\rfloor^2
\le 2T^3\le3T^3.
$$

Count small square factors using this estimate, and large square factors using
the reciprocal-square tail. With T = floor(X^(1/4)), the s=1 contribution is
at most 5X^(3/4). For s >= 5, write s=5+4j and absorb q^(2j) into the square
factor. The count of the resulting images is at most sqrt(X). Thus

$$
E_{\mathrm{SP}}(X)\le6X^{3/4}\qquad(X\ge16).
$$

For the denominator, Mathlib's character modulo four has prefixes in {0,1}.
The Leibniz limit pi/4 and finite alternating partial-sum bounds give a harmonic
tail of at most 1/y. Finite Dirichlet convolution and ordinary Chebyshev bounds
then give an absolute bound of twelve on the signed weighted Mangoldt sum.
Combined with the existing Mertens estimate and the summable prime-power
correction, this bounds the weighted prime sum in the residue class one modulo
four within twelve of half log(x).

Apply that bound at x and x/exp(50). Their difference is at least one for
x >= exp(50), and counting the fixed-ratio prime window gives

$$
\pi(x;4,1)\ge e^{-50}\frac{x}{\log x}.
$$

Every prime congruent to one modulo four lies in E with s=m=1. The two bounds
therefore give a ratio at most 6exp(50) log(X)/X^(1/4), which tends to zero.

## Falsifier

Adding oddness of m, fixing s=1, or counting representations as distinct
integers would change the target or require a separate argument. The squarefree
decomposition must not impose coprimality of a and b. The harmonic character
series is conditionally convergent in its natural order, so unconditional
summability cannot be assumed. Every denominator estimate must hold for all
sufficiently large thresholds. The denominator is positive for X >= 5,
because 5 is an Euler form.

## Evidence

**Proved in Lean:** `StrongPseudoperfectEulerDensity.result` is the exact
relative-density limit for the source's Euler predicate. Its proof includes
the square-divisor mean, finite image counts, the modulus-four prime lower
bound, and eventual positivity of the denominator, with no additional
number-theory hypotheses.

The literature assessment in preregistration #31710 searched Question 44,
strong pseudoperfection, and subsequent work by Wang and Zelinsky. The latter
constructs infinitely many odd primitive strongly pseudoperfect numbers;
infinity alone does not determine relative density in E. This bounded search
is not a priority certification or an exhaustive literature search.

## Triage

- **Proved in Lean:** the mechanism compares a numerator O(X^(3/4)) with
  a denominator bounded below by a positive multiple of X/log(X).
- **Proved on paper:** the version additionally requiring odd m follows from
  the same numerator upper bound and the same prime denominator lower bound.
  The larger-set limit by itself would not imply this statement.
- **Proved in Lean; literature:** Question 43 concerns ordinary density among
  all integers, with a zero-density answer in `StrongPseudoperfectDensity.result`.
  That limit does not give relative density inside E; the present square-factor
  count supplies the additional estimate.
- **Literature:** the residue-class Mertens and Chebyshev bounds are classical.
  Upstream Mathlib has the stronger prime number theorem in arithmetic
  progressions; the pinned dependency supplies Dirichlet's theorem and the
  inputs used for the finite-convolution proof.
- **Unresolved:** improving the Euler-form numerator to X^(1/2+o(1)). The
  powerset fiber bound alone does not yield this estimate.

## ASSUMED-UNVERIFIED

Worldwide priority and exhaustive coverage of subsequent literature are
unverified. The odd-square-factor variant has the paper proof stated above;
no separate public Lean theorem for that variant is asserted.
