---
bibkey: zelinsky2021totalprimefactors
authors: Joshua Zelinsky
year: 2021
title: On the Total Number of Prime Factors of an Odd Perfect Number
doi: null
url: https://math.colgate.edu/~integers/v76/v76.pdf
claim: "Section 5, Question 5 asks whether a(n+1)-a(n) takes every positive integer value; Section 7 defines Euler-form relative strong properties and states Theorem 9 and Conjecture 1 for OR(alpha,beta)."
strata_touched:
  - D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity
  - D5/S3/Arith/Abundancy/ZelinskyNortonFirstDifference
license: citation-only
triage: anchor
---

# Prime-factor restrictions measured inside Euler forms

## Norton first differences

Section 5, Question 5 asks:

> Does a(n+1) − a(n) take on every positive integer value?

Here p_n is the n-th prime, with p_1=2, and a(n) is the least positive
integer k for which the product of p_r/(p_r−1), over n≤r≤n+k−1, exceeds 2.
The difference is between consecutive starting indices, not consecutive
prime arguments.

## Euler-form density assertions

Joshua Zelinsky, *On the Total Number of Prime Factors of an Odd Perfect
Number*, Integers 21 (2021), article A76, Section 7, printed pages 47--48.

The source defines

$$
E=\{p^a m^2:p\text{ prime},\ p\equiv a\equiv1\pmod4,\ (p,m)=1\}.
$$

The variables are positive integers. The definition does not separately require
that the square factor m be odd. Counts are counts of integers at most x,
rather than counts of their representations. For a property P, the source
calls P strong when E_P(x)/E(x) tends to zero and weak when this quotient tends
to one.

On page 48 it defines OR(alpha,beta)(n) as
Omega(n) >= alpha*omega(n)+beta, where Omega counts prime factors with
multiplicity and omega counts distinct prime factors. Theorem 9 asserts that
this is a strong property for every real alpha > 2 and real beta. It attributes
the assertion to Theorem 430 of Hardy and Wright.

The same page defines P to be substantially stronger than Q when every
Euler-form integer satisfying P satisfies Q and E_P(x)/E_Q(x) tends to zero.
Conjecture 1 states:

> Let alpha1, alpha2, beta1, beta2 be real numbers with alpha1 > alpha2 > 2.
> Then OR(alpha1,beta1) is substantially stronger than OR(alpha2,beta2).

The source's necessary conditions for odd perfect numbers are distinct from
its density assertions over all of E.

## Verified locator

- URL: https://math.colgate.edu/~integers/v76/v76.pdf
- Publication: Integers 21 (2021), article A76.
- Locator: Section 5, Question 5, Norton threshold first differences.
- Locator: Section 7, printed page 47, definition of E and strong/weak properties.
- Locator: Section 7, printed page 48, OR(alpha,beta), Theorem 9, substantially stronger, and Conjecture 1.
