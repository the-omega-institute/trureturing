# Quadratic modes on a selected Leech frame factor

## Abstract

Quadratic modes on a selected Leech frame factor

For two arbitrary oscillator jet orders, the corrected neutral quadratic field has a normal-ordered current sum and a scalar contraction. On a unit Leech frame direction the scalar contraction has Gram factor one. Under the native tensor equivalence every coefficient acts on the selected polynomial factor, so it commutes with the currents on the complementary factor.

**Definition 1.1 (Doubled exponent of a quadratic mode).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.doubledExponent`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.doubledExponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Shift the integer mode by the two creation weights and multiply by negative two.

**Definition 1.2 (Neutral quadratic source).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.quadraticSource`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.quadraticSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the two polarized oscillator polynomials and place the product in lattice charge zero.

**Definition 1.3 (Polarized twisted tensor current).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.polarizedTensorCurrent`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.polarizedTensorCurrent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Extend the polarized half-Fock current by the identity on the actual twisted ground module.

**Definition 1.4 (Normal order of two current modes).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.normalProduct`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.normalProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Place the first mode on the left at negative indices and on the right at nonnegative indices.

**Definition 1.5 (Finite current summation interval).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.modeInterval`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.modeInterval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For mode parameter m and truncation bound R, the first index ranges inclusively from the smaller of m minus R and zero to R minus one.

**Theorem 1.6 (Corrected quadratic coefficient at even exponent).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.quadratic_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.quadratic_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the Gram determinant is a unit and every standard native current of index at least R kills the input. For any two polarizations and jet orders, the coefficient is the corresponding finite normal-ordered sum with both jet scalars. The neutral pair contraction contributes the pair scalar times the Gram pairing at mode parameter zero. The two labelled occurrences preserve the contraction when their labels coincide.

**Theorem 1.7 (Vanishing at odd doubled exponent).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.quadratic_coefficient_odd`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.quadratic_coefficient_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two half-integral current indices give an even doubled exponent. The scalar correction also has even doubled exponent, so the odd coefficient is the zero endomorphism.

**Definition 1.8 (Quadratic mode of a unit direction).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.singleQuadraticMode`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.singleQuadraticMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each input polynomial gives a finite support for the normally ordered current sum. This defines a linear endomorphism with the norm-one scalar correction at mode parameter zero.

**Theorem 1.9 (Finite evaluation of the unit-direction mode).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.singleQuadraticMode_interval`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.singleQuadraticMode_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the single normalized current kills the input at every index at least R, the sum is over the interval for that cutoff.

**Definition 1.10 (Leech frame index).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.FrameIndex`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.FrameIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Index the directions of the verified norm-four Leech frame.

**Definition 1.11 (Selected frame quadratic source).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.frameQuadraticSource`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.frameQuadraticSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the same normalized frame vector in both slots of the neutral quadratic state.

**Definition 1.12 (Extension of a selected-factor operator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.onSingle`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.onSingle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Tensor the selected polynomial endomorphism with the identities on the complementary polynomial factor and the ground module.

**Theorem 1.13 (Selected current conjugation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.nativeTensorSplit_current_single`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.nativeTensorSplit_current_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transport the native selected current by the oscillator equivalence and extend the conjugation to the twisted ground tensor.

**Theorem 1.14 (Complementary current conjugation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.nativeTensorSplit_current_complement`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.nativeTensorSplit_current_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complementary current acts on the second polynomial factor after transport, with identity on the selected factor and the ground module.

**Theorem 1.15 (Transport of the finite coefficient sum).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.nativeTensorSplit_quadratic_interval`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.nativeTensorSplit_quadratic_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given a current truncation bound on the native input, conjugate each ordered pair in the finite sum. Orthonormality gives the scalar contraction of a unit direction.

**Theorem 1.16 (Quadratic mode on the selected factor).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.nativeTensorSplit_quadratic_mode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.nativeTensorSplit_quadratic_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On each pure tensor take the maximum of a native current bound and a bound for the selected polynomial. The resulting common finite sum proves the operator equality by tensor extensionality.

**Theorem 1.17 (Transport at every doubled exponent).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.nativeTensorSplit_quadratic_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.nativeTensorSplit_quadratic_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At even exponent recover the unique integer mode by halving the negative exponent and subtracting the two creation weights. At odd exponent the operator vanishes. The even coefficient and a complementary current act on separate tensor factors, so their compositions agree on pure tensors.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.FrameIndex`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.doubledExponent`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.frameQuadraticSource`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.modeInterval`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.nativeTensorSplit_current_complement`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.nativeTensorSplit_current_single`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.nativeTensorSplit_quadratic_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.nativeTensorSplit_quadratic_interval`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.nativeTensorSplit_quadratic_mode`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.normalProduct`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.onSingle`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.polarizedTensorCurrent`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.quadraticSource`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.quadratic_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.quadratic_coefficient_odd`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.singleQuadraticMode`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport.singleQuadraticMode_interval`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit](LeechHalfFockTensorSplit.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCorrectedConformal](../../LatticeHalfFockCorrectedConformal.md)
