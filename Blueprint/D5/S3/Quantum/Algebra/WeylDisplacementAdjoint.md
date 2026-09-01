# The Adjoint of a Weyl Displacement Word

## Abstract

Conjugate-transposing a displacement word negates its index and costs one phase.

**Lemma 1.1 (A negated index inverts the shift power).**

$$\forall M: \mathbb{N},\ [\operatorname{NeZero}(M)],\ \forall a: \operatorname{ZMod}(M),\ \operatorname{shiftMatrix}\left(M\right)^{\operatorname{val}\left(-a\right)} \cdot \operatorname{shiftMatrix}\left(M\right)^{\operatorname{val}\left(a\right)} = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylDisplacementAdjoint.shiftMatrix_pow_neg_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two natural representatives sum to a multiple of the window cardinality, so the corresponding powers of the cyclic update annihilate to the identity by the frozen order relation.

**Lemma 1.2 (The adjoint of a shift power).**

$$\forall M: \mathbb{N},\ [\operatorname{NeZero}(M)],\ \forall a: \operatorname{ZMod}(M),\ \operatorname{star}\left(\operatorname{shiftMatrix}\left(M\right)^{\operatorname{val}\left(a\right)}\right) = \operatorname{shiftMatrix}\left(M\right)^{\operatorname{val}\left(-a\right)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylDisplacementAdjoint.star_shiftMatrix_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The adjoint and the negated power are both left inverses of the same power. In a finite matrix algebra a one-sided inverse is two-sided, so the two agree. Unitarity of each power comes from the frozen unitarity of the generator by induction.

**Theorem 1.3 (Adjoint law).**

$$\forall M: \mathbb{N},\ [\operatorname{NeZero}(M)],\ \forall a, b: \operatorname{ZMod}(M),\ \operatorname{star}\left(\operatorname{displacement}\left(M, a, b\right)\right) = \operatorname{windowRoot}\left(M\right)^{\operatorname{val}\left(a \cdot b\right)} \cdot \operatorname{displacement}\left(M, {-a}, {-b}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylDisplacementAdjoint.displacement_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugate-transposing reverses the two factors and negates each index. Restoring the original order is one application of the frozen composition law, and it costs exactly the phase whose exponent is the product of the two original indices.

The proof uses only the public composition law: the reversed product is the product of the words at (0, -b) and (-a, 0), so no separate commutation argument is needed.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/WeylDisplacementAdjoint.displacement_adjoint`
- Truth anchor: `D5/S3/Quantum/Algebra/WeylDisplacementAdjoint.shiftMatrix_pow_neg_mul`
- Truth anchor: `D5/S3/Quantum/Algebra/WeylDisplacementAdjoint.star_shiftMatrix_pow`
- Dependency: [D5/S3/Quantum/Algebra/WeylDisplacement](WeylDisplacement.md)
