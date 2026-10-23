---
bibkey: kagey2021firstletter
authors: Peter Kagey
year: 2021
title: "Expected value of letters of permutations with a given number of k-cycles"
doi: 10.48550/arXiv.2112.05281
url: https://arxiv.org/abs/2112.05281v1
claim: "Conjecture 5.1: for fixed k and n > k, the expected first letter conditional on k inversions equals M(n + 1, k)/M(n, k)."
strata_touched:
  - D5/S3/Combinatorics/Permutation/KageyInversionFirstLetter
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2112.05281
Source: https://arxiv.org/abs/2112.05281v1

Section 5.2, page 20, Conjecture 5.1 and its preceding paragraph.

# First letters conditioned on inversion number

The preceding paragraph states:

> Because the expected value of the first letter is given by the weighted sum of the permutations with mah(w) = k divided by the number of such permutations, E[π(1) | π ∈ S_n, mah(π) = k] has a denominator that is (a factor of) M(n, k), the number of permutations of w ∈ S_n such that inv(w) = k.

Conjecture 5.1, page 20, reads:

> For fixed k and n > k, the expected value of the first letter of a permutation with a given number of inversions satisfies a rational function in n given by E[π(1) | π ∈ S_n, inv(π) = k] = M(n + 1, k)/M(n, k), where M(n, k), as above, is the number of permutations w ∈ S_n such that inv(w) = k.

Permutations are `Equiv.Perm (Fin n)`. The existing `PSW.word` is exactly
`List.ofFn (fun i => (π i).val + 1)`, so it gives the one-based letters in
one-line notation. The existing `ListInversions.inv` counts strict inversions.
`M` is the cardinality of the finite inversion fiber, and `E` is its rational
first-letter sum divided by that cardinality. The displayed conjecture includes
all natural `k,n` with `k < n`.

The numerator identity follows by deleting the first letter and counting two
successive insertion ranks of a fixed total. The source statement and its
objects are literature-attested; this proof is repository-derived. The
formal identity does not separately assert positivity of the denominator.

The inspected arXiv version and the author's dissertation chapter state the
conjecture. The inspected later papers arXiv:2210.17021v2 and
arXiv:2602.11061v1, and the OpenishProblems catalog, supplied no settlement
in the checked scope. Completeness of the literature screen is
`ASSUMED-UNVERIFIED`.
