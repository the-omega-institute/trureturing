---
bibkey: onnis2022happyv1
authors: Luca Onnis
year: 2022
title: "On a variant of the happy numbers and their generalizations, arXiv:2203.03381v1"
doi: null
url: https://arxiv.org/abs/2203.03381v1
claim: "There are no perfect square that are term of the sequence with length of convergence equal to 3."
strata_touched:
  - D5/S1/Digit/OnnisSquareThreeStepRefutation
license: citation-only
triage: anchor
---

# Onnis's square convergence prohibition

## Verified locator

- URL: https://arxiv.org/abs/2203.03381v1
- Locator: Section 1.2, "Variant of happy numbers", and Section 3,
  "Conjecture 1", in the exact versioned source.

The exact source is arXiv:2203.03381v1. Section 1.2 defines the map by:

> To determine whether a given number k is a term of this sequence, start with k, take the square of the product of its nonzero digits, apply the same process to the result, and continue until 1 is reached or a loop is entered. If 1 is reached, k is a term of this sequence.

Section 3, headed "Conjecture 1", states:

> There are no perfect square that are term of the sequence with length of convergence equal to 3.

These sentences occur at lines 53 and 205 of `main.tex` in the versioned
source archive at <https://arxiv.org/src/2203.03381v1>. The archive's SHA256 is
`20f9d7c8f30cab5c24be34ab87d5daf524cbfed9c8d2099882fa37c8e0125927`.
The decimal examples in Section 1.2 and the positive `Range` domains in its
programs specify positive decimal integers. The five-arrow example in
Section 1.1 and the displayed chain `n0 -> n1 -> 10^(2h) -> 1` in Section 4
count iterations from the initial value at index zero. Reaching one means
first reaching it, rather than counting subsequent repetitions of the fixed
point.

The prohibition ranges over arbitrary perfect squares. Section 3 explicitly
discusses the root 7152, whose factorization contains 149, and distinguishes
it from possible products of nonzero decimal digits. Thus the source does
not restrict initial roots to primes at most seven or require initial
squares to lie in the image of the map.

The square `55225 = 235^2` has orbit `55225 -> 250000 -> 100 -> 1`.
Its nonzero digit products are respectively 500, 10 and 1, and none of the
first three states equals one. This refutes the whole Section 3 prohibition.
It does not refute Section 4's separate assertion about convergence in at
most three steps, classify any image-restricted family, or identify a least
counterexample. The counterexample is not claimed as a historical discovery.
