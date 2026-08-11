# Lagrange-Gram Identity

## Abstract

The Cauchy-Schwarz defect equals a manifestly nonnegative sum of squares (the coordinate Gram remainder).

**Theorem 1.1 (The Cauchy-Schwarz defect is a sum of squares).**

$$(\sum_{i} u_{i}^{2})(\sum_{i} v_{i}^{2})-(\sum_{i} u_{i}v_{i})^{2}=\frac{1}{2} \sum_{i} \sum_{j} (u_{i}v_{j}-u_{j}v_{i})^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/LagrangeGramIdentity.lagrange_gram_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real families u and v indexed by a finite set, the Cauchy-Schwarz defect (sum of u_i^2)(sum of v_i^2) - (sum of u_i v_i)^2 equals one half of the double sum over i and j of (u_i v_j - u_j v_i)^2. The right-hand side is a sum of squares, hence nonnegative, which is exactly the Cauchy-Schwarz inequality; it is the coordinate form of the Gram wedge-remainder G in the identity ||u||^2 ||v||^2 = |<u,v>|^2 + G.

The theorem establishes only this algebraic sum-of-squares identity; it does not instantiate the Cramer-Rao, Robertson-Schrodinger, or quantum Cramer-Rao specialisations of the note, which require the corresponding inner-product structures.

## References

- Truth anchor: `D5/S3/QuantumBounds/LagrangeGramIdentity.lagrange_gram_identity`
