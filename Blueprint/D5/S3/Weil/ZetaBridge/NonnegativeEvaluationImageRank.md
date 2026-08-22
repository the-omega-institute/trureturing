# Rank Bound for a Nonnegative Evaluation Image

## Abstract

A nonnegative two-coordinate cross form has image dimension at most one.

**Theorem 1.1 (A nonnegative evaluation image has rank at most one).**

$$\forall T, \forall E: T \to C^{2}, \forall m\in\mathbb{N}, 0< m \land {\forall g\in T, 0\leq \operatorname{CrossValue}(m, E(g))} \Rightarrow\\{\operatorname{dim}_C(\operatorname{im}(E)) \leq 1 \land \neg\operatorname{Surjective}(E)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/NonnegativeEvaluationImageRank.nonnegative_evaluation_image_finrank_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let T be a complex vector space and E a complex-linear map into two complex coordinates. A positive natural multiplicity weights the canonical real cross value from the neighboring module.

Assume that cross value is nonnegative for every test. If the image had dimension two, the imported negative-direction theorem would produce a test with strictly negative cross value, a contradiction. The same rank bound rules out surjectivity onto both mirror coordinates.

The zero evaluation witnesses that the hypotheses are jointly satisfiable. The proof reuses the canonical cross value and does not redeclare an evaluation or Hermitian-form object.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/NonnegativeEvaluationImageRank.nonnegative_evaluation_image_finrank_le_one`
- Dependency: [D5/S3/Weil/ZetaBridge/TwoDimensionalEvaluationNegativeDirection](TwoDimensionalEvaluationNegativeDirection.md)
