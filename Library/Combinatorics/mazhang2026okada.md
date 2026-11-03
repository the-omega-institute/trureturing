---
bibkey: mazhang2026okada
authors: Ma, Haobo; Zhang, Wenlin
year: 2026
title: "Proofs of Okada's Conjectures 9.63 and 9.64 with constant-base-shift extensions"
doi: 10.5281/zenodo.23927424
url: https://doi.org/10.5281/zenodo.23927424
claim: "Theorem 2 classifies width-two unit-base, unit-weight, zero-shift pre-merged Gaussian determinants: almost palindromicity holds exactly when the smaller tuple gap is one."
strata_touched:
  - D5/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic
license: cc-by-4.0
triage: anchor
---

# Width-two pre-merged Gaussian determinants

Ma and Zhang, revision 2, 3 November 2026, Theorems 1–2.
For natural entries `0 ≤ a₁ < a₂ ≤ b₁ < b₂`, put
`A = [b₁ choose a₁]q [b₂ choose a₂]q`,
`B = [b₁ choose a₂]q [b₂ choose a₁]q`, and `P = A − B`.
Theorem 2 states that the nonzero coefficients of `P`, in increasing degree,
form a palindrome if and only if `min(a₂ − a₁, b₂ − b₁) = 1`.
Theorem 1 supplies the endpoint mismatch when both gaps are at least two.

The Lean owner uses the existing integer Gaussian polynomial, with unit base,
unit weight, and zero degree shift. Zero initial entries and touching tuples
are included. The source's counting and other parameter extensions are outside
this classification declaration and remain tracked in issue #26173.
The conjecture numbers refer to Okada's arXiv:2003.02112v2 §9.8.3;
Okada is the problem source author, and the proof note authors are Ma and Zhang.

Source ZIP SHA256: `da99d1f3682c59285a8d9f3e47f664b8a5f844ae5c45da303328e3fef6f4ffa0`.

## Verified locator

- DOI: https://doi.org/10.5281/zenodo.23927424
- Source: https://doi.org/10.5281/zenodo.23927424
