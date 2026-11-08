---
bibkey: kagey2021firstletter
authors: Peter Kagey
year: 2021
title: "Expected value of letters of permutations with a given number of k-cycles"
doi: 10.48550/arXiv.2112.05281
url: https://arxiv.org/abs/2112.05281v1
claim: "Conjectures 5.1 and 5.2: inversion-conditioned first letters equal a Mahonian ratio; major-index-conditioned first letters have a monic rational form of degrees k + 1 and k."
strata_touched:
  - D5/S3/Combinatorics/Permutation/KageyInversionFirstLetter
  - D5/S1/Words/Permutations/KageyMajorIndexFirstLetter
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

# First letters conditioned on major index

Conjecture 5.2, page 20, states:

> For fixed k > 0 and n ≥ k, E[π(1) | π ∈ S_n, maj(π) = k] satisfies a rational function in n that is 1/(k + 1) times the quotient of a monic degree-(k + 1) polynomial by a monic degree-k polynomial.

Section 5.1, page 19, studies “the expected value of the first letter of a permutation”.
Section 5.2, page 20, gives the mean by the following sentence:

> Because the expected value of the first letter is given by the weighted sum of the permutations with mah(w) = k divided by the number of such permutations, E[π(1) | π ∈ S_n, mah(π) = k] has a denominator that is (a factor of) M(n, k), the number of permutations of w ∈ S_n such that inv(w) = k.

Section 5.2, page 19, names the two statistics:

> Below, we have given conjectures about two: the major index and the inversion number.

The major index sums the one-based positions of adjacent descents. Permutations
are `Equiv.Perm (Fin n)`, with letters `(π i).val + 1`. The conditional mean is
the sum of first letters over the permutations of major index `k`, divided by
the cardinality of that finite set, in the rational field.

The formal claim includes `k ≤ n` and nonzero conditioning cardinality. Thus it
includes the endpoint `n = k` whenever the mean is defined; it makes no claim
about an undefined conditional expectation. The quotient need not be reduced.

Increasing blocks give a falling-factorial count and a first-block-minimum
weighted count. Exact-descent inclusion–exclusion gives polynomials for the
cardinality and weighted sum. Only the cut pair `S = U = {k}` contributes to
their highest coefficients. Factorial scaling gives the asserted monic degrees.
The conjecture and statistical definitions are literature-attested; this proof
is repository-derived.

Henry Friedman’s 2023 thesis, *Long Increasing Subsequences*, was not retrieved (HTTP 403); literature completeness remains `ASSUMED-UNVERIFIED`.
