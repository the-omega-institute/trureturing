# The doubled-coordinate subgroup and E4 quotient

## Abstract

The doubled-coordinate subgroup and E4 quotient

**Definition 1.1 (Reduction of exactly two coordinates).**

Lean statement: `D5/S3/FiniteGroups/HeadleyDoubledCoordinates.quotientHom`

*Formalization.* `D5/S3/FiniteGroups/HeadleyDoubledCoordinates.quotientHom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The homomorphism reduces the two selected positive coordinates modulo two and ignores all remaining coordinates.

**Theorem 1.2 (Every E4 coset occurs).**

Lean statement: `D5/S3/FiniteGroups/HeadleyDoubledCoordinates.quotientHom_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/HeadleyDoubledCoordinates.quotientHom_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two canonical cyclic reductions are surjective. The remaining coordinates can be set to zero, so the paired reduction is onto E4.

**Definition 1.3 (The subgroup has the lowered coordinate type).**

Lean statement: `D5/S3/FiniteGroups/HeadleyDoubledCoordinates.kernelEquiv`

*Formalization.* `D5/S3/FiniteGroups/HeadleyDoubledCoordinates.kernelEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal subgroup kernel is additively equivalent to the original coordinate product with exactly the selected two exponents lowered by one. Product-kernel and subgroup-product equivalences retain every other factor.

**Definition 1.4 (The actual quotient is E4).**

Lean statement: `D5/S3/FiniteGroups/HeadleyDoubledCoordinates.quotientEquiv`

*Formalization.* `D5/S3/FiniteGroups/HeadleyDoubledCoordinates.quotientEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first isomorphism theorem identifies the quotient by this literal kernel with ZMod 2 times ZMod 2. No additive splitting of the extension is assumed.

**Theorem 1.5 (The kernel is the doubled-coordinate range).**

Lean statement: `D5/S3/FiniteGroups/HeadleyDoubledCoordinates.kernel_eq_doubled_range`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/HeadleyDoubledCoordinates.kernel_eq_doubled_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugating doubling on the two selected coordinates by the coordinate chart gives an endomorphism of the original product. Its range is exactly the selected kernel.

## References

- Truth anchor: `D5/S3/FiniteGroups/HeadleyDoubledCoordinates.kernelEquiv`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyDoubledCoordinates.kernel_eq_doubled_range`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyDoubledCoordinates.quotientEquiv`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyDoubledCoordinates.quotientHom`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyDoubledCoordinates.quotientHom_surjective`
- Dependency: [D5/S3/FiniteGroups/HeadleyCoordinateKernel](HeadleyCoordinateKernel.md)
