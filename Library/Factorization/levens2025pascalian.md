---
bibkey: levens2025pascalian
authors: Owen Levens
year: 2025
title: Polynomials Arising from Sorted Binomial Coefficients
doi: 10.48550/arXiv.2511.03082
url: https://arxiv.org/abs/2511.03082v1
claim: "Conjecture 6.4 asserts the full symmetric group for even Pascalian indices and the mth hyperoctahedral group at index 2m+1."
strata_touched:
  - D5/S3/Factorization/Galois/LevensPascalian
license: citation-only
triage: anchor
---

# Pascalian polynomials and their Galois groups

## Verified locator

DOI: 10.48550/arXiv.2511.03082

Source: https://arxiv.org/abs/2511.03082v1

The statements below are in Section 1, printed page 1, and Section 6.2,
printed page 20 of version 1.

## Source statements

Section 1: “let ⟨n k⟩ = C(n, ⌊(n−k)/2⌋) for 0 ≤ k ≤ n, call the ⟨n k⟩
triangle the Pascalian numbers, and let the nth Pascalian polynomial be
P_n(z) = Σ_{k=0}^{n} ⟨n k⟩ z^{n−k}.”

Conjecture 6.4: “P_n(z) has full Galois group for even n. For n = 2m + 1,
the Galois group of P_n(z) is the mth hyperoctahedral group.”

The formal proposition concerns the second sentence with natural m ≥ 1,
coefficients in ℚ, and an abstract group isomorphism. The hyperoctahedral
group is represented by the permutations of Fin m × Bool commuting with
the sign change. At m = 24, the square discriminant of the associated
binomial truncation constrains its root permutations to the alternating
group and gives a strict cardinality obstruction to that isomorphism.

## Related classical inputs and limits

The general discriminant formula is a specialization of Filaseta–Moy,
*On the Galois group over Q of a truncated binomial expansion*,
arXiv:1803.02754v1, Lemma 3, https://arxiv.org/abs/1803.02754v1.
No priority for that formula or the square-discriminant criterion is asserted.
The differential identity also belongs to the existing truncated-binomial
literature, including Scherbak, arXiv:math/0409329, Section 6.1, Lemma 6.

The literature screen in issue #19007 did not find a prior settlement of
Conjecture 6.4 at (n,m) = (49,24). Completeness is
ASSUMED-UNVERIFIED: the full text of Laishram–Yadav (IJNT 20, 2024) was
not accessed. The exact Galois group at 49, the even-index clause,
Conjecture 6.3, and a general Pell-family theorem are outside this result.
