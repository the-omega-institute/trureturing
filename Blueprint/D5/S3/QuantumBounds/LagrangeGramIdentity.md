# Lagrange-Gram Identity

## Abstract

The Cauchy-Schwarz defect equals a manifestly nonnegative sum of squares (the coordinate Gram remainder).

**Theorem 1.1 (The Cauchy-Schwarz defect is a sum of squares).**

$$\left(\sum_i u_i^2\right)\left(\sum_i v_i^2\right) - \left(\sum_i u_i v_i\right)^2 = \frac{1}{2}\sum_i \sum_j (u_i v_j - u_j v_i)^2$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/LagrangeGramIdentity.lagrange_gram_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real families u and v indexed by a finite set, the Cauchy-Schwarz defect (Σ u_i²)(Σ v_i²) − (Σ u_i v_i)² equals one half of the double sum over i and j of (u_i v_j − u_j v_i)². The right-hand side is a sum of squares, hence nonnegative, which is exactly the Cauchy-Schwarz inequality; it is the coordinate form of the Gram wedge-remainder G in the identity ‖u‖²‖v‖² = |⟨u,v⟩|² + G.

The theorem establishes only this algebraic sum-of-squares identity; it does not instantiate the Cramér-Rao, Robertson-Schrödinger, or quantum Cramér-Rao specialisations of the note, which require the corresponding inner-product structures.

## References
