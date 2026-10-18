# Onnis's Square Convergence Prohibition Is False

## Abstract

A positive perfect square first reaches one after three iterations of the nonzero-decimal-digit-product square map.

**Definition 1.1 (Nonzero decimal digit product).**

$$\forall n \in \mathbb{N},\; \operatorname{P}\left(n\right) = \operatorname{prod}\left(\operatorname{FilterNonzero}\left(\operatorname{digits}\left(10, n\right)\right)\right)$$

*Formalization.* `D5/S1/Digit/OnnisSquareThreeStepRefutation.nonzeroDigitProduct` (`✓ std3`).

*Citation.* Luca Onnis (2022). *On a variant of the happy numbers and their generalizations, arXiv:2203.03381v1*. URL: <https://arxiv.org/abs/2203.03381v1>.

*Commentary.*

P(n) is the product of exactly the nonzero entries of Nat.digits 10 n. Mathlib stores digits from least to most significant; multiplication in the natural numbers is commutative, so this is the source's decimal digit product. Zeros are removed, rather than multiplied.

**Definition 1.2 (The square map).**

$$\forall n \in \mathbb{N},\; \operatorname{step}\left(n\right) = \operatorname{P}\left(n\right)^{2}$$

*Formalization.* `D5/S1/Digit/OnnisSquareThreeStepRefutation.step` (`✓ std3`).

*Citation.* Luca Onnis (2022). *On a variant of the happy numbers and their generalizations, arXiv:2203.03381v1*. URL: <https://arxiv.org/abs/2203.03381v1>.

*Commentary.*

Section 1.2 squares the product P(n), and repeats this map on the result. The definition applies to every natural input; the conjecture's domain consists of positive inputs.

**Definition 1.3 (Sequence membership).**

$$\forall n \in \mathbb{N},\; (\operatorname{SequenceMember}\left(n\right)) \Leftrightarrow (\exists t \in \mathbb{N},\; \operatorname{Iterate}\left(step, t, n\right) = 1)$$

*Formalization.* `D5/S1/Digit/OnnisSquareThreeStepRefutation.SequenceMember` (`✓ std3`).

*Citation.* Luca Onnis (2022). *On a variant of the happy numbers and their generalizations, arXiv:2203.03381v1*. URL: <https://arxiv.org/abs/2203.03381v1>.

*Commentary.*

A positive integer belongs to the sequence when a finite iterate reaches one. Iteration zero is the initial value itself. Iteration is mathlib's Function.iterate, with no auxiliary orbit restriction.

**Definition 1.4 (Exact convergence length).**

$$\forall n \in \mathbb{N},\; \forall t \in \mathbb{N},\; (\operatorname{FirstHit}\left(n, t\right)) \Leftrightarrow ((\operatorname{Iterate}\left(step, t, n\right) = 1) \land (\forall k \in \mathbb{N},\; (k < t) \Rightarrow (\neg \operatorname{Iterate}\left(step, k, n\right) = 1)))$$

*Formalization.* `D5/S1/Digit/OnnisSquareThreeStepRefutation.FirstHit` (`✓ std3`).

*Citation.* Luca Onnis (2022). *On a variant of the happy numbers and their generalizations, arXiv:2203.03381v1*. URL: <https://arxiv.org/abs/2203.03381v1>.

*Commentary.*

FirstHit(n,t) requires the value one at index t and excludes one at every earlier natural index, including index zero. Repeated terminal ones do not increase the first hitting time.

**Definition 1.5 (The whole Section 3 conjecture).**

$$(claim) \Leftrightarrow (\forall n \in \mathbb{N},\; (0 < n) \Rightarrow ((\exists r \in \mathbb{N},\; n = r^{2}) \Rightarrow ((\operatorname{SequenceMember}\left(n\right)) \Rightarrow (\neg \operatorname{FirstHit}\left(n, 3\right)))))$$

*Formalization.* `D5/S1/Digit/OnnisSquareThreeStepRefutation.claim` (`✓ std3`).

*Citation.* Luca Onnis (2022). *On a variant of the happy numbers and their generalizations, arXiv:2203.03381v1*. URL: <https://arxiv.org/abs/2203.03381v1>.

*Commentary.*

The original prohibition quantifies over all positive natural squares that are sequence members. The existential root is any natural number. There is no restriction to smooth roots or squares in the image of a preceding digit-product step.

**Theorem 1.6 (A square with first hitting time three).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/OnnisSquareThreeStepRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/onnis-2022-square-three-step-refutation` (refuted) by `D5/S1/Digit/OnnisSquareThreeStepRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"onnis-2022-square-three-step-refutation","declaration_gid":"D5/S1/Digit/OnnisSquareThreeStepRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Luca Onnis (2022). *On a variant of the happy numbers and their generalizations, arXiv:2203.03381v1*. URL: <https://arxiv.org/abs/2203.03381v1>.

*Commentary.*

The square 235^2 = 55225 has successive nonzero digit products 500, 10 and 1. Their squares give 55225 -> 250000 -> 100 -> 1. Nat.digits_ofDigits proves each decimal representation with its digit bounds and nonzero last digit. The iterate successor equations give the three transitions; indices zero, one and two have values different from one. Hence the positive square is a sequence member with exact first hitting time three, contradicting the whole Section 3 conjecture. This makes no assertion about Section 4's separate at-most-three statement, least examples or image-restricted families, and makes no historical-priority claim.

## References

- Truth anchor: `D5/S1/Digit/OnnisSquareThreeStepRefutation.FirstHit`
- Truth anchor: `D5/S1/Digit/OnnisSquareThreeStepRefutation.SequenceMember`
- Truth anchor: `D5/S1/Digit/OnnisSquareThreeStepRefutation.claim`
- Truth anchor: `D5/S1/Digit/OnnisSquareThreeStepRefutation.nonzeroDigitProduct`
- Truth anchor: `D5/S1/Digit/OnnisSquareThreeStepRefutation.result`
- Truth anchor: `D5/S1/Digit/OnnisSquareThreeStepRefutation.step`
