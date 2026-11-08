---
bibkey: kagey2021majorindex
authors: Peter Kagey
year: 2021
title: "Expected value of letters of permutations with a given number of k-cycles"
doi: null
url: https://arxiv.org/abs/2112.05281v1
claim: "Conjecture 5.2: the mean first letter at fixed positive major index is 1/(k + 1) times a quotient of monic polynomials of degrees k + 1 and k."
strata_touched:
  - D5/S1/Words/Permutations/KageyMajorIndexFirstLetter
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2112.05281
Source: https://arxiv.org/abs/2112.05281v1

Section 5.2, page 20, Conjecture 5.2 states:

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

The literature screen on issue #19720 inspected the arXiv version, the author's
dissertation chapter, arXiv:2210.17021v2, arXiv:2602.11061v1, the author's
OpenishProblems catalog, and the unweighted Mahonian discussion at
https://math.stackexchange.com/questions/4065815 . Conger's
arXiv:math/0508112 concerns conditioning on descent number. Henry Friedman's
2023 thesis, *Long Increasing Subsequences*, was not read because retrieval
returned HTTP 403. Completeness remains `ASSUMED-UNVERIFIED`.
