# Normalized native Leech half-Fock currents

## Abstract

Normalized native Leech half-Fock currents

For each frequency k, the negative mode indexed by -k-1 creates a polynomial variable and the mode indexed by k differentiates with coefficient k + 1/2. The proof starts with the existing integral-coordinate native current and the norm-four Leech frame.

**Definition 1.1 (Polarized native modes).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.polarizedCurrent`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.polarizedCurrent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Extend the native modes complex-linearly in the current vector.

**Theorem 1.2 (Standard basis polarization).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.polarizedCurrent_standardBasis`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.polarizedCurrent_standardBasis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The standard basis coefficient sum recovers the original native mode.

**Definition 1.3 (Current in polynomial coordinates).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.coordinateCurrent`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.coordinateCurrent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugate the polarized native mode by the frequencywise polynomial equivalence.

**Theorem 1.4 (Action of the conjugated current).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.coordinateCurrent_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.coordinateCurrent_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the inverse coordinate change before the native mode and the forward change after it.

**Theorem 1.5 (Creation modes).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.coordinateCurrent_negative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.coordinateCurrent_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compute the image of the original linear generator under the coordinate change. Multiplication by this generator becomes multiplication by the chosen variable.

**Theorem 1.6 (Annihilation modes).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.coordinateCurrent_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.coordinateCurrent_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use polynomial induction to transport the old derivative. The derivations agree on constants and variables, and the Leibniz rule extends the equality to products. The orthonormal Gram matrix selects the corresponding partial derivative, with scale k + 1/2.

**Theorem 1.7 (Factors on other coordinates).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.coordinateCurrent_mul_of_notMem_vars`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.coordinateCurrent_mul_of_notMem_vars` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For creation use associativity. For annihilation use the Leibniz rule and the vanishing of a partial derivative outside the variable support.

**Definition 1.8 (Orthonormal Leech basis).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.orthonormalBasis`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.orthonormalBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Scale the actual norm-four basis by one half.

**Theorem 1.9 (Normalized frame vector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.orthonormalBasis_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.orthonormalBasis_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The basis vector is one half of the corresponding actual Leech frame vector.

**Theorem 1.10 (Normalized Gram pairing).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.orthonormalBasis_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.orthonormalBasis_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bilinearity scales the original Gram matrix by one quarter, yielding the identity.

**Theorem 1.11 (Leech creation mode).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.current_negative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.current_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Specialize creation to the normalized actual Leech frame.

**Theorem 1.12 (Leech annihilation mode).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.current_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.current_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the normalized Leech Gram pairing to identify each native annihilation mode.

**Theorem 1.13 (Leech current on disjoint variables).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.current_mul_of_notMem_vars`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.current_mul_of_notMem_vars` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The multiplication rule applies to each frame vector and any factor supported outside its coordinate.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.coordinateCurrent`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.coordinateCurrent_apply`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.coordinateCurrent_mul_of_notMem_vars`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.coordinateCurrent_negative`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.coordinateCurrent_nonnegative`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.current_mul_of_notMem_vars`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.current_negative`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.current_nonnegative`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.orthonormalBasis`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.orthonormalBasis_apply`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.orthonormalBasis_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.polarizedCurrent`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents.polarizedCurrent_standardBasis`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame](ActualLeechNormFourFrame.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentNormal](../../LatticeHalfFockCurrentNormal.md)
