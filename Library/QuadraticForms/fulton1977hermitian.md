---
bibkey: fulton1977hermitian
authors: John D. Fulton
year: 1977
title: Representations by Hermitian Forms in a Finite Field of Characteristic Two
doi: 10.4153/CJM-1977-017-5
url: https://doi.org/10.4153/CJM-1977-017-5
claim: A Hermitian matrix of arbitrary rank over a quadratic finite-field extension in characteristic two is congruent to an identity block and a zero block.
strata_touched:
  - D5/S3/QuadraticForms/FiniteHermitianCongruence
license: citation-only
triage: anchor
---

## Verified locator

John D. Fulton, *Representations by Hermitian Forms in a Finite Field of Characteristic Two*, Canadian Journal of Mathematics 29 (1), 169–179, page 170.

DOI: 10.4153/CJM-1977-017-5

URL: https://doi.org/10.4153/CJM-1977-017-5

## Hermitian congruence

For a finite field K with a nonidentity involution sigma, a Hermitian matrix B satisfies sigma(B)-transpose=B. The normalized congruence is T-transpose B sigma(T)=diag(I-rho,0), with rho the rank of B and T invertible. Fulton's characteristic-two setting includes matrices with a radical, and the stated page supplies the arbitrary-rank congruence.

The finite-field construction normalizes a nonzero self-pairing using the norm to the fixed field, splits off its orthogonal line, and recurses on dimension. A zero restriction supplies the radical basis. The Lean construction uses the finite-field norm and fixed-field interfaces and has no characteristic restriction. This is a formalization of established Hermitian-form mathematics, with no originality claim. The congruence alone supplies no character-sum evaluation or parity or entropy formula.
