# Pointed-Center Cyclic Monodromy

## Abstract

The order power of a self-half-braiding scalar gives the cyclic associator product.

**Theorem 1.1 (The scalar recurrence from the half-braiding hexagon).**

Lean statement: `D5/S3/FiniteGroups/Cyclic/PointedCenterMonodromy.halfBraidingScalar_mul`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/PointedCenterMonodromy.halfBraidingScalar_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the forward associator from (X(a) ⊗ X(b)) ⊗ X(c) to X(a) ⊗ (X(b) ⊗ X(c)) and Mathlib’s left half-braiding from X(g) ⊗ U to U ⊗ X(g). Assume X sends multiplication to tensor and the scalar functor to SingleObj A, for a commutative group A, preserves scalars under both whiskerings. Applying that functor to Mathlib’s half-braiding hexagon at X(h) and X(g) cancels the forward and inverse associators at (X(h), X(g), X(g)). The remaining recurrence is θ(h) θ(g) = α(g,h,g) θ(hg), with θ the half-braiding scalar and α the forward associator scalar.

**Theorem 1.2 (The cyclic product from the self-half-braiding).**

Lean statement: `D5/S3/FiniteGroups/Cyclic/PointedCenterMonodromy.pow_orderOf_eq_cyclicProduct`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/PointedCenterMonodromy.pow_orderOf_eq_cyclicProduct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Iterating the recurrence at h = g^i accumulates the factors α(g,g^i,g) for i from zero through orderOf(g) minus one. Since g^orderOf(g) = 1, the two endpoint factors θ(1) cancel. The cyclic product equals θ(g) raised to that order.

For the pointed-category and Drinfeld-center setting, see Drinfeld–Gelaki–Nikshych–Ostrik (DGNO), On braided fusion categories I, arXiv:0906.0620.

Application to the actual vertex operator algebra requires a ribbon comparison identifying the self-half-braiding scalar with the canonical ribbon twist of the corresponding central object.

## References

- Truth anchor: `D5/S3/FiniteGroups/Cyclic/PointedCenterMonodromy.halfBraidingScalar_mul`
- Truth anchor: `D5/S3/FiniteGroups/Cyclic/PointedCenterMonodromy.pow_orderOf_eq_cyclicProduct`
- Dependency: [D5/S3/FiniteGroups/Cyclic/CyclicAssociatorObstruction](CyclicAssociatorObstruction.md)
