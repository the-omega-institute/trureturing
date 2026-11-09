# Finite Discriminant Fusion Algebra

## Abstract

The finite pointed fusion algebra carried by the discriminant group. The normalized Weil `S`-kernel supplies the addition law, which is packaged as the genuine finite based algebra `ℂ[Discriminant D]`. This is an algebraic consequence of the finite Verlinde coefficients; it does not assert a tensor-category or vertex-operator-algebra construction.

**Definition 1.1 (Finite fusion algebra).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.FusionAlgebra`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.FusionAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an original positive even integral lattice `D`, `FusionAlgebra D` is the complex additive monoid algebra of the finite discriminant group.

**Definition 1.2 (Discriminant basis).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The basis vector indexed by a discriminant class is the monoid-algebra single at that class with coefficient `1`.

**Theorem 1.3 (Pointed multiplication).**

Lean statements: `basis_mul`, `basis_zero`, `basis_mul_comm`, `basis_mul_assoc`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis_mul`, `basis_zero`, `basis_mul_comm`, and `basis_mul_assoc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication of basis vectors is indexed by addition in the discriminant group. The unit is the zero class, and the resulting pointed multiplication is commutative and associative.

**Theorem 1.4 (Structure constants are finite Verlinde coefficients).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis_mul_coeff_eq_fusionCoefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis_mul_coeff_eq_fusionCoefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient of the basis class `c` in the product of the classes `a` and `b` is exactly the normalized finite Verlinde coefficient. Thus the algebra multiplication consumes the Weil `S`-kernel computation rather than introducing independent structure constants.

**Definition 1.5 (Augmentation).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.augmentation`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.augmentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The augmentation is the algebra homomorphism sending every discriminant basis element to `1`.

**Theorem 1.6 (Augmentation on basis vectors).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.augmentation_basis`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.augmentation_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.FusionAlgebra`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis_mul_coeff_eq_fusionCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.augmentation`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.augmentation_basis`
- Dependency: [D5/S3/VertexAlgebra/Characters/LatticeDiscriminantVerlinde](LatticeDiscriminantVerlinde.md)
