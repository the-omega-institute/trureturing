# Finite Discriminant Fusion Algebra

## Abstract

The finite pointed fusion algebra carried by the discriminant group.

**Definition 1.1 (Finite fusion algebra).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.FusionAlgebra`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.FusionAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an original positive even integral lattice D, FusionAlgebra D is the complex additive monoid algebra of the finite discriminant group. This is a finite algebraic package of the Weil S-kernel coefficients; it does not assert a tensor-category or vertex-operator-algebra construction.

**Definition 1.2 (Discriminant basis).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The basis vector indexed by a discriminant class is the monoid-algebra single at that class with coefficient 1.

**Theorem 1.3 (Pointed multiplication).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis_mul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication of basis vectors is indexed by addition in the discriminant group.

**Theorem 1.4 (Zero class is the unit).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The basis vector indexed by the zero discriminant class is the algebra unit.

**Theorem 1.5 (Commutative pointed multiplication).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis_mul_comm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis_mul_comm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pointed basis multiplication is commutative.

**Theorem 1.6 (Associative pointed multiplication).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis_mul_assoc`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis_mul_assoc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pointed basis multiplication is associative.

**Theorem 1.7 (Structure constants are finite Verlinde coefficients).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis_mul_coeff_eq_fusionCoefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis_mul_coeff_eq_fusionCoefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient of the basis class c in the product of the classes a and b is exactly the normalized finite Verlinde coefficient computed from the Weil S-kernel.

**Definition 1.8 (Augmentation).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.augmentation`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.augmentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The augmentation is the algebra homomorphism sending every discriminant basis element to 1.

**Theorem 1.9 (Augmentation on basis vectors).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.augmentation_basis`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.augmentation_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The augmentation sends every discriminant basis vector to 1.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.FusionAlgebra`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.augmentation`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.augmentation_basis`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis_mul`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis_mul_assoc`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis_mul_coeff_eq_fusionCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis_mul_comm`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.basis_zero`
- Dependency: [D5/S3/VertexAlgebra/Characters/LatticeDiscriminantVerlinde](LatticeDiscriminantVerlinde.md)
