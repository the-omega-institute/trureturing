---
slug: zelinsky-2021-conjecture-1-or-density
bibkey: zelinsky2021totalprimefactors
doi: null
url: https://math.colgate.edu/~integers/v76/v76.pdf
triage: theorem
motivation_gids:
  - D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.result
---

# Prime-factor inequalities retain positive relative density in Euler forms

## Problem

Joshua Zelinsky, *On the Total Number of Prime Factors of an Odd Perfect
Number*, Integers 21 (2021), A76, Section 7, printed page 48, Conjecture 1:

> Let alpha1, alpha2, beta1, beta2 be real numbers with alpha1 > alpha2 > 2.
> Then OR(alpha1,beta1) is substantially stronger than OR(alpha2,beta2).

Pages 47--48 define E to consist of the positive integers p^a m^2 with p prime,
p congruent to a congruent to 1 modulo 4, and gcd(p,m)=1. There is no separate
oddness condition on m. Omega(n) counts prime factors with multiplicity;
omega(n) counts distinct prime factors. The restriction is

$$
OR_{\alpha,\beta}(n)\quad\Longleftrightarrow\quad
\Omega(n)\ge\alpha\omega(n)+\beta.
$$

For any property P, E_P(x) counts the integers in E satisfying P and at most x.
The source says that P is substantially stronger than Q when both of the
following hold: every member of E satisfying P satisfies Q, and
E_P(x)/E_Q(x) tends to zero as x tends to infinity.

The formal claim retains all four real parameters, both strict slope
inequalities, the full inclusion clause, and the zero-limit clause. It reuses
`StrongPseudoperfectEulerDensity.EulerForm` and `eulerCount`. Its `orCount`
counts integers 1 <= n <= X, once each, with this Euler predicate and OR.
Real thresholds have the same counts as their natural-number floors, so a
natural-threshold limit expresses the source's density clause.

## Motivation

Every odd perfect number has Euler's form. The source proposes relative
density in E as a way to compare the force of necessary conditions on such
numbers. A normal-order result for unrestricted integers does not by itself
control density within this sparse set.

## Gap

The key comparison is between the full Euler-form count and a family with a
fixed square factor. A lower bound for infinitely many examples alone would
not refute a relative-density-zero claim. The count must control all allowed
Euler exponents, and both numerator and denominator bounds must hold at every
sufficiently large threshold.

## Route

Every n=p^a m^2 in E has odd positive a and can be written as p*s^2 by absorbing
p^((a-1)/2) into m. Consequently

$$
E(X)\le\sum_{1\le s\le\sqrt X}\pi(X/s^2).
$$

For s <= X^(1/4), the logarithm of X/s^2 is at least half log(X).
Chebyshev's upper bound and the convergent reciprocal-square sum bound this
part by a constant times X/log(X). For larger s, the estimate pi(y) <= y
and the reciprocal-square tail give O(X^(3/4)). Thus

$$
E(X)\ll X/\log X.
$$

Fix real alpha and beta. Choose an integer h >= 1 such that
1+2h >= 2alpha+beta and put M=3^(2h). For every prime q congruent to one
modulo four, q is different from 3 and

$$
n_q=Mq\in E,\qquad \omega(n_q)=2,\qquad\Omega(n_q)=1+2h.
$$

The map q to n_q is injective. The modulus-four prime lower bound supplies
a positive constant c_(alpha,beta) with

$$
E_{OR_{\alpha,\beta}}(X)\ge
c_{\alpha,\beta}\,X/\log X
$$

eventually. Comparing this lower bound with the full-set upper bound gives
the stronger target

$$
\forall\alpha,\beta\in\mathbb R\ \exists c>0\quad
cE(X)\le E_{OR_{\alpha,\beta}}(X)
\quad\text{for all sufficiently large }X.
$$

## Falsifier

Take (alpha1,beta1)=(4,0) and (alpha2,beta2)=(3,0). The inclusion clause
does hold, since omega(n) is nonnegative. The numerator has an eventual
positive lower bound relative to E, whereas the denominator is at most E.
The denominator is eventually positive by the corresponding lower bound
for (3,0) and positivity of E. Their quotient is therefore eventually at
least a fixed positive constant, which excludes convergence to zero.

For this parameter pair h=4 suffices: 1+2h=9 is at least both 8 and 6.
The fixed family 3^8*q already contradicts the density clause.

## Evidence

The public target `ZelinskyOmegaRatioDensity.relative_density_pos` is the
all-real-parameter eventual lower bound above. The designated `claim` is
Conjecture 1 with its inclusion and limit clauses, and the designated
`result : Not claim` uses this lower bound at the parameter pairs (4,0)
and (3,0). The count upper bound covers every Euler exponent congruent
to one modulo four.

The literature check associated with preregistration #31808 covered the journal
text, arXiv record, author page, and searches for Theorem 9, substantially
stronger properties, Euler-form density, and errata. No matching published
correction or refutation was identified within that search scope.

## Triage

- **Mathematical mechanism (paper consequence of Lean-proved bounds):**
  `ZelinskyOmegaRatioDensity.family_mem`, `family_count` and `or_count_lower`
  construct and count the family; `euler_count_upper` and
  `relative_density_pos` supply the full-set comparison. For each h >= 1
  chosen with 1+2h >= 2alpha+beta, the fixed-square-part family
  3^(2h)*q, with q prime and q congruent to one modulo four, already contributes
  a positive lower proportion of E. In this family the two prime-factor
  counts are bounded independently of X. Normal-order assertions for all
  positive integers therefore do not transfer to the source's counting
  measure on E.
- **Consequence of the Lean-proved `relative_density_pos` and the reused
  `eulerCount_pos`:** Theorem 9 on the same page fails for every real alpha > 2
  and real beta. This follows directly from these two statements. Its asserted
  strong property would require E_OR(X)/E(X) to tend to zero, contradicting the
  eventual positive lower bound. This conclusion concerns the source's
  exact definition of E without claiming existence of a density limit. It gives a
  positive lower limit bound, and does not concern the truth of a necessary
  inequality for actual odd perfect numbers.
- **Counting order (paper consequence of Lean-proved bounds):**
  `ZelinskyOmegaRatioDensity.euler_count_upper` gives the upper bound;
  `ModFourChebyshev.prime_count_lower` and
  `StrongPseudoperfectEulerDensity.primeCount_le_eulerCount` give the lower
  bound. Hence E(X) is bounded above and below by positive constant
  multiples of X/log(X) eventually. The upper bound includes all Euler
  exponents. The lower bound already follows from the primes congruent
  to one modulo four, with exponent and square factor equal to one.
- **Unresolved:** a replacement theorem on a specified subset of E,
  under a different sampling measure, or with a different counting
  convention. No such correction is identified with the printed theorem
  or conjecture without stating and proving its additional conditions.

## ASSUMED-UNVERIFIED

Worldwide priority and exhaustive coverage of subsequent literature are
unverified.
