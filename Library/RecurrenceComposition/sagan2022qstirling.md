---
bibkey: sagan2022qstirling
authors: Bruce E. Sagan and Joshua P. Swanson
year: 2022
title: "q-Stirling numbers in type B"
doi: 10.1016/j.ejc.2023.103899
url: https://arxiv.org/abs/2205.14078v1
claim: "Conjecture 7.6 asserts bottom heaviness of the coefficients of all four unshifted unsigned q-Stirling families."
strata_touched:
  - D5/S3/Combinatorics/QStirling/SaganSwansonBottomHeavy
license: citation-only
triage: anchor
---

# q-Stirling numbers in type B

## Verified locator

DOI: https://doi.org/10.1016/j.ejc.2023.103899

Source: https://arxiv.org/abs/2205.14078v1

The arXiv v1 text, Section 7.5, printed page 39, defines:

> A sequence is bottom heavy if aₖ ≥ aₙ₋ₖ for k < n/2.

Conjecture 7.6, printed page 40, states:

> For each n, k, the coefficients of S[n, k], c[n, k], S_B[n, k], and c_B[n, k] are all bottom heavy.

The coefficient list begins at exponent zero and ends at the actual polynomial
degree. The coefficient at a reflected exponent is compared to the lower
exponent for every strict-half index. The zero and constant cases are vacuous.
The separately shifted S-bar family is outside this assertion.

Section 1.1 says:

> Each recursion in this paper will always have n ∈ ℕ and k ∈ ℤ with the same boundary condition when n=0.

The source definitions read as follows.

Section 1.1, equation (2), printed page 3:

> We will call the (type A) q-Stirling numbers of the second kind the polynomials S[n, k] in the variable q obtained by replacing (1) with S[n,k] = S[n−1,k−1]+[k] S[n−1,k].

Section 1.1, equation (5), printed page 4:

> The (signless, type A) q-Stirling numbers of the first kind are the polynomials c[n, k] obtained by replacing (4) with c[n,k]=c[n−1,k−1]+[n−1] c[n−1,k].

Definition 1.5, equation (8), printed page 6:

> The type B q-Stirling numbers of the second kind are defined by replacing (1) with S_B[n,k]= S_B[n−1,k−1]+ [2k+1] S_B[n−1,k].

Definition 1.5, equation (9), printed page 6:

> The (signless) type B Stirling numbers of the first kind are defined by replacing (4) with c_B[n,k] = c_B[n−1,k−1] + [2n−1] c_B[n−1,k].

All four initial rows are the Kronecker delta at zero. For nonnegative a,
[a] is the sum of q^j over 0 ≤ j < a. The negative-k branches of the second-kind
families vanish; a negative-length q-integer is never encoded as a polynomial.
The Lean names SB and cB denote S_B and c_B, with the same recursive bodies.

The published article is European Journal of Combinatorics 118 (2024), 103899.
Its page 31 repeats Conjecture 7.6. Literature-screen completeness is
ASSUMED-UNVERIFIED; the bounded screen and experiment are identified in issue
https://github.com/the-omega-institute/trureturing/issues/21443.
