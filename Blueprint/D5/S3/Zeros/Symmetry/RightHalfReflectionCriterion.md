# Right-Half Reflection Criterion

## Abstract

Reflection symmetry reduces a fixed-point claim to the right half.

**Theorem 1.1 (Reflection symmetry makes the right-half criterion sufficient).**

$$(\forall x\in K,\ P(1-x) \Leftrightarrow P(x)) \Rightarrow ((\forall x\in K,\ P(x) \Rightarrow x = \frac{1}{2}) \Leftrightarrow (\forall x\in K,\ P(x) \Rightarrow \frac{1}{2} \le x \Rightarrow x = \frac{1}{2})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/RightHalfReflectionCriterion.reflection_symmetric_right_half_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a linearly ordered field and P a predicate invariant under reflection x maps to one minus x. The global claim that every P-point equals one half is equivalent to its restriction to P-points at or to the right of one half. A point left of one half reflects to the right, where the restricted hypothesis fixes it; reflecting back then fixes the original point.

This closes only the symmetry-reduction sentence in the source clause. It does not assert the zeta functional equation, a zero-free region, the Riemann hypothesis, or any numerical window certificate.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/RightHalfReflectionCriterion.reflection_symmetric_right_half_iff`
