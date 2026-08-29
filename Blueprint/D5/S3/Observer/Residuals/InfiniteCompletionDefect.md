# Infinite Completion Defect

## Abstract

A positive weighted defect series vanishes exactly when every finite defect vanishes.

**Theorem 1.1 (The infinite defect detects every finite defect).**

$$\begin{aligned}\forall State: \operatorname{Type},\\{}\forall D: State \to \left(\mathbb{N} \to \mathbb{R}\right), x: State,\\{}(\forall n: \mathbb{N}, 0 \leq \operatorname{apply}\left(D, x, n\right)) \Rightarrow\\{}(\sum_{n=0}^{\infty} 2^{-(n+1)} \cdot \frac{\operatorname{apply}\left(D, x, n\right)}{1+\operatorname{apply}\left(D, x, n\right)} = 0) \Leftrightarrow (\forall n: \mathbb{N}, \operatorname{apply}\left(D, x, n\right) = 0).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Residuals/InfiniteCompletionDefect.infinite_completion_defect_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let each state have a nonnegative real defect at every finite layer. Construct one scalar by normalizing each defect and weighting layer n by two to the negative n-plus-one power.

The normalized terms are nonnegative and bounded by a summable geometric series. If their total is zero, each individual term is zero, and the positive weights and denominators recover the original defects.

Repository searches found no prior normalized defect construction. The pinned library supplies the geometric summability and ordered-sum comparison steps used in the proof.

## References

- Truth anchor: `D5/S3/Observer/Residuals/InfiniteCompletionDefect.infinite_completion_defect_eq_zero_iff`
