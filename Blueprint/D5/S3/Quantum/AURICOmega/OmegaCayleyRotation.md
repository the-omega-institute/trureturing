# Adjoint and Cayley rotations

## Abstract

Exact rational three-dimensional rotations and the quaternion heap recurrence for Chapter 32, sections 32.7 and 32.8 and Appendix Q.

**Theorem 1.1 (The adjoint action preserves dot products).**

$$\forall p \in Quaternion,\; \forall u \in RatVec3, v \in RatVec3,\; \operatorname{Nonzero}\left(p\right) \Rightarrow \operatorname{Equivalent}\left(\operatorname{dot}\left(\operatorname{Ad}\left(p, u\right), \operatorname{Ad}\left(p, v\right)\right), \operatorname{dot}\left(u, v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaCayleyRotation.ad_dot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The action sends v to the imaginary coordinates of p times the pure quaternion v times the conjugate of p, divided by the squared norm of p.

**Theorem 1.2 (A signed quaternion scale leaves the adjoint action unchanged).**

$$\forall p \in Quaternion,\; \forall k \in \mathbb{Z},\; \forall v \in RatVec3,\; \left(\operatorname{Nonzero}\left(p\right) \land k \ne 0\right) \Rightarrow \operatorname{Equivalent}\left(\operatorname{Ad}\left(\operatorname{scale}\left(k, p\right), v\right), \operatorname{Ad}\left(p, v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaCayleyRotation.ad_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed scale contributes its square to the numerator and the denominator.

**Theorem 1.3 (Quaternion multiplication composes adjoint rotations).**

$$\forall p \in Quaternion, q \in Quaternion,\; \forall v \in RatVec3,\; \left(\operatorname{Nonzero}\left(p\right) \land \operatorname{Nonzero}\left(q\right)\right) \Rightarrow \operatorname{Equivalent}\left(\operatorname{Ad}\left(\operatorname{mul}\left(p, q\right), v\right), \operatorname{Ad}\left(p, \operatorname{Ad}\left(q, v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaCayleyRotation.ad_hom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conjugate reverses the product order and the squared norm of the product multiplies the denominators.

**Theorem 1.4 (The Cayley matrix satisfies the forward equation).**

$$\forall s \in RatVec3,\; \operatorname{Equivalent}\left(\operatorname{mul}\left(\operatorname{skewMinus}\left(s\right), \operatorname{Cayley}\left(s\right)\right), \operatorname{skewPlus}\left(s\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaCayleyRotation.cayley_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two skew factors are I−X and I+X, where X is the cross-product matrix of the rational parameter s. The equality is checked after clearing positive denominators.

**Theorem 1.5 (The Cayley matrix is orthogonal).**

$$\forall s \in RatVec3,\; \operatorname{Equivalent}\left(\operatorname{mul}\left(\operatorname{transpose}\left(\operatorname{Cayley}\left(s\right)\right), \operatorname{Cayley}\left(s\right)\right), I\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaCayleyRotation.cayley_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integer numerator has orthogonal columns with squared lengths equal to the square of the common denominator.

**Theorem 1.6 (The Cayley matrix has determinant one).**

$$\forall s \in RatVec3,\; \operatorname{Equivalent}\left(\operatorname{det}\left(\operatorname{Cayley}\left(s\right)\right), 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaCayleyRotation.cayley_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant of the integer numerator is the cube of the positive denominator.

**Theorem 1.7 (Repeated Cayley steps preserve squared norm).**

$$\forall s \in RatVec3, v \in RatVec3,\; \forall n \in \mathbb{N},\; \operatorname{Equivalent}\left(\operatorname{dot}\left(\operatorname{cayleyIterate}\left(s, v, n\right), \operatorname{cayleyIterate}\left(s, v, n\right)\right), \operatorname{dot}\left(v, v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaCayleyRotation.cayley_iterate_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each natural-number beat the same rational Cayley matrix acts once. The dot-product law applies at every beat.

**Theorem 1.8 (The signed quaternion heap recurrence stays on the unit sphere).**

$$\forall a \in PythSpinor, b \in PythSpinor,\; \forall n \in \mathbb{N},\; \operatorname{Equivalent}\left(\operatorname{spinorNormSq}\left(\operatorname{heapAt}\left(a, b, n\right)\right), 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaCayleyRotation.heap_norm_preserved` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sequence starts at a and b. The next element is the current element times the conjugate of the previous element times the current element. The squared norm is taken after dividing by the positive spinor radius.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaCayleyRotation.ad_dot`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaCayleyRotation.ad_hom`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaCayleyRotation.ad_scale`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaCayleyRotation.cayley_det`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaCayleyRotation.cayley_identity`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaCayleyRotation.cayley_iterate_norm`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaCayleyRotation.cayley_orthogonal`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaCayleyRotation.heap_norm_preserved`
