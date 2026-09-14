---
bibkey: connelly2026qfibonomial
authors: Brendan B. Connelly; Ezekiel Ito; Thomas C. Martinez; Olha Shevchenko; Kacey Yang
year: 2026
title: Unimodality of q-Fibonomial coefficients for small cases
doi: null
url: https://arxiv.org/html/2605.12822v1
claim: Conjecture 5.4 asserts necessity of its divisibility-or-floor-bound condition when k is at most three or r is at most three.
strata_touched:
  - D5/S0/Certificates/Polynomials/QProductNecessityRefutation
license: citation-only
triage: anchor
---

# Unimodality of q-Fibonomial coefficients for small cases

This note attests the source assertion, not the truth of the conjecture.
Section 5.2, Conjecture 5.4, ends:

> Moreover, if k ≤ 3 or r ≤ 3, this condition is also necessary.

The condition is that some a_i is divisible by r, or b is at most one plus
the sum of the floors a_i/r. All a_i and b are positive, r ≥ 2 and k ≥ 1.
Corollary 4.3 explicitly uses "for some"; Conjecture 5.4 is introduced as its
generalization. This determines the existential reading of "for any".

The next sentence reports computational verification for k ≤ 5, r ≤ 6 and
max{a_i,b} ≤ 15. The following sentence gives ([3]_q)^4[2]_(q^4) as an example
where the condition is not necessary in general. That example has k=r=4,
outside both alternatives of the restricted necessity premise.

The repository refutes the restricted necessity clause using r=3, k=6,
all a_i=2 and b=2. Its sufficiency clause is outside this formalization.

## Verified locator

- DOI: 10.48550/arXiv.2605.12822
- Version read: https://arxiv.org/html/2605.12822v1
- Target: section 5.2, Conjecture 5.4, final "Moreover" sentence;
  both immediately following sentences were also read.
- Quantifier context: section 4.1, Corollary 4.3 and its proof.
- https://arxiv.org/abs/2605.12822 lists only v1, submitted 12 May 2026.

No exhaustive priority claim is made.
