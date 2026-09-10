---
bibkey: codex2026a392714bridge
authors: Codex implementation worker
year: 2026
title: Alternating words and the A392714 residual intervals
doi: null
url: https://github.com/the-omega-institute/trureturing
claim: The blocked prefix rule on explicitly alternating words is equivalent to the interlaced residual condition.
strata_touched:
  - D5/S1/Words/Compositions/AlternatingResidualBridge
license: citation-only
triage: anchor
---

# Alternating words and residual intervals

## Verified locator

This is a repository derivation. Its source is
`D5/S1/Words/Compositions/AlternatingResidualBridge.lean`, specifically
`encode_rule_iff`, `encode_injective`, and `encoded_product_sign_sum`.
The prerequisite is `ResidualPermutationSign.signed_residual_sum` in the same directory.
The implementation report is `docs/reports/a392714bridge/report.md`.

For permutations a,b of 1,…,m, form w=(a₁,−b₁,…,aₘ,−bₘ,0).
Write Aᵢ and Bᵢ for their prefix sums. The height before block i is Aᵢ₋₁−Bᵢ₋₁.
The block endpoint is nonnegative exactly when Bᵢ≤Aᵢ. Its reversed order is
illegal exactly when Aᵢ₋₁<Bᵢ. Thus nonnegative prefixes and absence of a
swappable complete block are equivalent to the two residual inequalities.
Each positive and negative position recovers one entry of a or b, so this
encoding is injective. The frozen residual identity then evaluates the sum
of sign(a)sign(b) over these pairs as one, including m=0.

This does not identify that product with the sign of an ambient contribution
permutation. The general classification of unpaired words and the bridge
from Φ(n) remain to be proved. No resolution of the original conjecture is claimed.
The source context is arXiv:2605.11137v1, Remark 4; the corresponding statement
is still called a conjecture in v2, Remark 5. Current OEIS access returned HTTP 403.
