# Tensor splitting of the actual Leech half-Fock space

## Abstract

Tensor splitting of the actual Leech half-Fock space

Fix one normalized Leech frame direction. The actual oscillator space splits as a polynomial tensor product on that direction and its complement. Native currents act on their respective factors, and the actual twisted tensor carries the product of the two oscillator signs with the identity on the ground module.

**Definition 1.1 (Partition of oscillator variables).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.variableSplit`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.variableSplit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Separate each pair of frame index and frequency according to whether its frame index is the chosen one.

**Definition 1.2 (Joining the tensor factors).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.join`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.join` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the polynomial tensor equivalence for a sum of variable types and rename by the inverse variable partition.

**Definition 1.3 (Splitting the native oscillators).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.nativeSplit`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.nativeSplit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose the normalized frame coordinates with the polynomial tensor splitting.

**Theorem 1.4 (Joining a chosen-coordinate variable).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.join_X_tmul_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.join_X_tmul_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The variable in the first factor joins to the corresponding oscillator variable.

**Theorem 1.5 (Joining a complement variable).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.join_one_tmul_X`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.join_one_tmul_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A variable of the second factor joins to the oscillator variable indexed by its complementary frame coordinate.

**Theorem 1.6 (Splitting a chosen-coordinate variable).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.split_X_single`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.split_X_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse equivalence places the variable in the first factor.

**Theorem 1.7 (Splitting a complement variable).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.split_X_complement`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.split_X_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse equivalence places the variable in the second factor.

**Theorem 1.8 (Joining arbitrary pure tensors).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.join_tmul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.join_tmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Prove the two tensor inclusions agree with the variable renamings on generators. Multiply the resulting images.

**Definition 1.9 (Single-factor oscillator modes).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.oscillatorMode`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.oscillatorMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use multiplication by the indexed variable for negative modes and the frequency-scaled derivative for nonnegative modes.

**Theorem 1.10 (Coordinate mode formula).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.coordinateCurrent_eq_oscillatorMode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.coordinateCurrent_eq_oscillatorMode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Match the two integer mode branches to the normalized Leech current formulas.

**Theorem 1.11 (Current on the first factor).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.current_join_tmul_single`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.current_join_tmul_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complementary polynomial has no variables in the chosen coordinate. The current passes through that factor and commutes with the first factor's variable renaming.

**Theorem 1.12 (Current on the second factor).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.current_join_tmul_complement`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.current_join_tmul_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first polynomial has no variables in any complementary coordinate. Use the same support argument and the complementary renaming.

**Theorem 1.13 (First-factor conjugation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.split_coordinateCurrent_single`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.split_coordinateCurrent_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply tensor extensionality to the chosen-coordinate current formula on pure tensors.

**Theorem 1.14 (Second-factor conjugation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.split_coordinateCurrent_complement`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.split_coordinateCurrent_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply tensor extensionality to a complementary current formula on pure tensors.

**Theorem 1.15 (Native current in the first factor).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.nativeSplit_current_single`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.nativeSplit_current_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compose the current transport with the native frame equivalence.

**Theorem 1.16 (Native current in the second factor).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.nativeSplit_current_complement`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.nativeSplit_current_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compose the complementary current transport with the native frame equivalence.

**Definition 1.17 (Polynomial sign change).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.polynomialSign`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.polynomialSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Send each variable to its negative by polynomial evaluation.

**Theorem 1.18 (Sign on generators).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.polynomialSign_X`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.polynomialSign_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial sign action negates each variable.

**Theorem 1.19 (Sign involution).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.polynomialSign_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.polynomialSign_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The square of the algebra homomorphism fixes every variable.

**Theorem 1.20 (Product of factor signs).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.split_polynomialSign`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.split_polynomialSign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the commutation with renaming and multiplicativity to transport the sign on pure tensors.

**Theorem 1.21 (Native sign in frame coordinates).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.orthonormal_coordinates_sigma`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.orthonormal_coordinates_sigma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse frame map sends each coordinate variable to a homogeneous linear polynomial. Negation commutes with that map on all generators.

**Theorem 1.22 (Native oscillator parity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.nativeSplit_sigma`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.nativeSplit_sigma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugate the native sign into frame coordinates and then into the two tensor factors.

**Definition 1.23 (Splitting the twisted tensor module).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.nativeTensorSplit`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.nativeTensorSplit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Tensor the oscillator equivalence with the identity of the ground module.

**Theorem 1.24 (Actual twist parity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.nativeTensorSplit_actualParity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.nativeTensorSplit_actualParity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Extend the oscillator conjugation to the actual twisted tensor by linearity and tensor extensionality.

**Definition 1.25 (Tensor parity sector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.tensorParitySector`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.tensorParitySector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the submodule spanned by pure tensors from the two specified eigenspaces.

**Theorem 1.26 (Disjoint parity sectors).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.tensorParitySector_disjoint_left`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.tensorParitySector_disjoint_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Embed each tensor sector into the eigenspace of the first-factor endomorphism and use disjointness for different eigenvalues.

**Theorem 1.27 (Positive oscillator parity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.splitParity_eigenspace_pos`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.splitParity_eigenspace_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For involutions A and B, use the ranges of the signed sums of their operators. Adding the two matching-sign tensor maps yields twice the positive signed sum of the product operator. Each range lies in the required eigenspace.

**Theorem 1.28 (Negative oscillator parity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.splitParity_eigenspace_neg`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.splitParity_eigenspace_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the signed-sum argument with opposite signs on the two factors.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.coordinateCurrent_eq_oscillatorMode`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.current_join_tmul_complement`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.current_join_tmul_single`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.join`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.join_X_tmul_one`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.join_one_tmul_X`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.join_tmul`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.nativeSplit`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.nativeSplit_current_complement`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.nativeSplit_current_single`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.nativeSplit_sigma`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.nativeTensorSplit`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.nativeTensorSplit_actualParity`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.orthonormal_coordinates_sigma`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.oscillatorMode`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.polynomialSign`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.polynomialSign_X`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.polynomialSign_involutive`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.splitParity_eigenspace_neg`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.splitParity_eigenspace_pos`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.split_X_complement`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.split_X_single`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.split_coordinateCurrent_complement`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.split_coordinateCurrent_single`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.split_polynomialSign`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.tensorParitySector`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.tensorParitySector_disjoint_left`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit.variableSplit`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents](LeechOrthogonalHalfFockCurrents.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockParityT](../../LatticeHalfFockParityT.md)
