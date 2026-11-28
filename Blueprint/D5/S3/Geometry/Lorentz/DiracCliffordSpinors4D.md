# Dirac, Weyl and Majorana spinors

## Abstract

The time-positive chiral gamma matrices, their matrix basis, and the spinor and real structures of the Lorentz cover.

Time has positive signature. The upper Pauli block of the real slash matrix follows the determinant-one conjugation action on Hermitian two-by-two matrices. The lower block is its adjugate, which fixes the dual Weyl action.

**Definition 1.1 (Dirac matrices).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.Mat4`

*Formalization.* `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.Mat4` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Use the algebra of four-by-four complex matrices with indices zero through three.

**Definition 1.2 (Dirac spinors).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.Spinor`

*Formalization.* `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.Spinor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

A spinor has four complex coordinates in an ordered pair of Weyl blocks.

**Definition 1.3 (Chiral gamma matrices).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.γ`

*Formalization.* `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.γ` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The time matrix has identity off-diagonal blocks. The spatial matrices have the corresponding Pauli matrix in the upper-right block and its negative in the lower-left block.

**Definition 1.4 (Clifford metric).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.η`

*Formalization.* `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.η` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Use the diagonal entries one, minus one, minus one and minus one over the complex numbers.

**Theorem 1.5 (Clifford anticommutator).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford_anticommutator`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford_anticommutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

For every pair of spacetime indices, the sum of the two orders of the product is twice the metric entry times the identity.

**Theorem 1.6 (Adjoint of a gamma matrix).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma_hermitian_conjugate`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma_hermitian_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

For each spacetime index its gamma matrix has adjoint equal to conjugation by the time matrix.

**Theorem 1.7 (Single gamma trace).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma_trace_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma_trace_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Every gamma matrix has trace zero.

**Theorem 1.8 (Trace of two gamma matrices).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma_two_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma_two_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The trace of the product at indices μ and ν is four times the metric entry at μ and ν.

**Theorem 1.9 (Trace of four gamma matrices).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma_four_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma_four_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

For ordered indices μ, ν, ρ and σ, the trace is four times the sum of the pairings (μν)(ρσ) and (μσ)(νρ) minus the pairing (μρ)(νσ). Each pairing is a product of metric entries.

**Definition 1.10 (Slash matrix).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.slash`

*Formalization.* `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.slash` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Sum the four gamma matrices weighted by the corresponding complex coordinates.

**Theorem 1.11 (Square of a slash matrix).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.feynman_slash_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.feynman_slash_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

For every complex coordinate vector, the square of its slash matrix is the identity times the sum of its squared coordinates weighted by the diagonal metric.

**Theorem 1.12 (Real slash square).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.minkowski_slash_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.minkowski_slash_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

For every real four-vector, the square of its slash matrix equals its Minkowski squared norm in the Pauli cover times the identity.

**Definition 1.13 (Chirality matrix).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma5`

*Formalization.* `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma5` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Multiply the four gamma matrices in time, x, y, z order and scale by the imaginary unit.

**Theorem 1.14 (Chirality in the Weyl basis).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma5_explicit`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma5_explicit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The chirality matrix has diagonal entries minus one, minus one, one and one.

**Theorem 1.15 (Square of chirality).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma5_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma5_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The square of the chirality matrix is the identity.

**Theorem 1.16 (Adjoint of chirality).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma5_hermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma5_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The chirality matrix equals its Hermitian adjoint.

**Theorem 1.17 (Trace of chirality).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma5_trace_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma5_trace_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The chirality matrix has trace zero.

**Theorem 1.18 (Gamma matrices exchange chiralities).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma5_anticommutes`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma5_anticommutes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Every gamma matrix anticommutes with the chirality matrix.

**Definition 1.19 (Left chirality projection).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.PL`

*Formalization.* `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.PL` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Subtract the chirality matrix from the identity and divide by two.

**Definition 1.20 (Right chirality projection).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.PR`

*Formalization.* `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.PR` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Add the chirality matrix to the identity and divide by two.

**Theorem 1.21 (Orthogonal Weyl projections).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chiral_projectors_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chiral_projectors_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Both projections are idempotent and Hermitian, their two ordered products vanish, and their sum is the identity. Every gamma matrix intertwines the left projection with the right projection.

**Definition 1.22 (Sixteen Clifford matrices).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford16`

*Formalization.* `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford16` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The family has a scalar, four vectors, six tensors, four axial vectors and a pseudoscalar.

**Definition 1.23 (Antisymmetric gamma tensor).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gammaTensor`

*Formalization.* `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gammaTensor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Scale the commutator of the two gamma matrices by half the imaginary unit.

**Theorem 1.24 (Ordered Clifford matrices).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford16_components`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford16_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The order is the identity, the four gamma matrices from zero to three, the tensors at 01, 02, 03, 12, 13 and 23, the four gamma matrices right-multiplied by chirality, and the chirality matrix.

**Theorem 1.25 (Hilbert–Schmidt pairing).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford16_trace_orthogonal`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford16_trace_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The trace of the adjoint of the first basis matrix times the second is four for equal indices and zero for distinct indices.

**Theorem 1.26 (Independent Clifford matrices).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford16_linearIndependent`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford16_linearIndependent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The sixteen Clifford matrices are linearly independent over the complex numbers.

**Definition 1.27 (Clifford basis).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford16_basis`

*Formalization.* `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford16_basis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The ordered Clifford family gives a complex basis of the full matrix space.

**Theorem 1.28 (Clifford completeness).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford16_span_top`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford16_span_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The complex span of the Clifford family is the full space of four-by-four matrices.

**Definition 1.29 (Bispinor matrix).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor`

*Formalization.* `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

A determinant-one two-by-two matrix acts on the first Weyl block and its inverse adjoint acts on the second.

**Theorem 1.30 (Identity bispinor action).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_one`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The identity of the two-component spinor group acts as the identity on Dirac spinors.

**Theorem 1.31 (Multiplicativity).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The bispinor action maps each product to the product of the actions in the same order.

**Theorem 1.32 (Bispinor determinant).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_det_one`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_det_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Every bispinor matrix has determinant one.

**Theorem 1.33 (Inverse action).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The inverse matrix of a bispinor action is the action of the inverse spinor group element.

**Theorem 1.34 (Preservation of the Dirac form).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_gamma0_intertwine`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_gamma0_intertwine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Multiplying the time gamma matrix on the left by the adjoint action and on the right by the action recovers the time gamma matrix.

**Theorem 1.35 (Preservation of chirality).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_commutes_gamma5`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_commutes_gamma5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Every bispinor matrix commutes with the chirality matrix.

**Theorem 1.36 (Pauli slash covariance).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_slash_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_slash_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

For each real four-vector, conjugating the slash matrix by the bispinor action gives the slash matrix of its image under the Lorentz cover.

**Theorem 1.37 (Inverse columns for upper gamma indices).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_lorentz_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_lorentz_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Conjugate an upper-index gamma matrix by the inverse bispinor matrix. Its expansion in the gamma family has coefficients from the corresponding column of the inverse Lorentz matrix.

**Definition 1.38 (Lowered gamma index).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gammaLower`

*Formalization.* `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gammaLower` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The time gamma matrix keeps its sign and the three spatial gamma matrices change sign.

**Theorem 1.39 (Lorentz rows for lowered gamma indices).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_lorentz_covariance_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_lorentz_covariance_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Conjugate a lowered-index gamma matrix by the inverse bispinor matrix. Its expansion in the lowered family has coefficients from the corresponding row of the Lorentz matrix.

**Definition 1.40 (Dirac adjoint).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.diracAdjoint`

*Formalization.* `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.diracAdjoint` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Conjugate the spinor components and multiply the resulting row by the time gamma matrix.

**Definition 1.41 (Matrix-inserted Dirac bilinear).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.diracBilinear`

*Formalization.* `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.diracBilinear` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Pair the Dirac adjoint of the first spinor with the result of applying the inserted matrix to the second spinor.

**Theorem 1.42 (Scalar invariance).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.dirac_scalar_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.dirac_scalar_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Simultaneously transforming both spinors preserves the bilinear with the identity insertion.

**Theorem 1.43 (Pseudoscalar invariance).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.dirac_pseudoscalar_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.dirac_pseudoscalar_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Simultaneously transforming both spinors preserves the bilinear with the chirality insertion.

**Theorem 1.44 (Vector covariance).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.dirac_vector_covariant`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.dirac_vector_covariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The bilinears with lowered gamma insertions transform by the rows of the Lorentz matrix on simultaneous bispinor transformation.

**Theorem 1.45 (Axial vector covariance).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.dirac_axial_vector_covariant`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.dirac_axial_vector_covariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The bilinears with lowered gamma insertions right-multiplied by chirality transform by the rows of the Lorentz matrix on simultaneous bispinor transformation.

**Definition 1.46 (Charge-conjugation matrix).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeMatrix`

*Formalization.* `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Multiply the second spatial gamma matrix by the time gamma matrix and scale by the imaginary unit.

**Theorem 1.47 (Unitary antisymmetric charge matrix).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj_unitary_antisymm`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj_unitary_antisymm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The adjoint times the charge matrix is the identity, its transpose is its negative, and its square is minus the identity.

**Theorem 1.48 (Transposed gamma matrices).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj_gamma`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj_gamma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Conjugating each gamma matrix by the charge matrix produces minus its transpose.

**Definition 1.49 (Spinor charge conjugation).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj`

*Formalization.* `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Conjugate the spinor coordinates and apply the second spatial gamma matrix scaled by the imaginary unit.

**Theorem 1.50 (Charge conjugation through the Dirac adjoint).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj_eq_diracAdjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj_eq_diracAdjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Applying the charge matrix to the transpose of the Dirac adjoint gives spinor charge conjugation.

**Theorem 1.51 (Majorana reality involution).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Applying spinor charge conjugation twice recovers the original spinor.

**Theorem 1.52 (Charge conjugation exchanges the Weyl projections).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj_flips_chirality`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj_flips_chirality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Charge conjugation after the left projection equals the right projection after charge conjugation.

**Theorem 1.53 (Intersection of Majorana and left Weyl conditions).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.no_majorana_weyl_4d`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.no_majorana_weyl_4d` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

A charge-conjugation fixed spinor in the left Weyl subspace is zero.

**Theorem 1.54 (Lorentz equivariance of Majorana reality).**

Lean statement: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj_lorentz_equivariant`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj_lorentz_equivariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Charge conjugation commutes with the bispinor action for every determinant-one spinor group element.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.Mat4`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.PL`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.PR`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.Spinor`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_commutes_gamma5`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_det_one`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_gamma0_intertwine`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_inverse`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_lorentz_covariance`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_lorentz_covariance_lower`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_mul`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_one`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.bispinor_slash_covariance`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj_eq_diracAdjoint`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj_flips_chirality`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj_gamma`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj_involutive`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj_lorentz_equivariant`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeConj_unitary_antisymm`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chargeMatrix`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.chiral_projectors_spec`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford16`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford16_basis`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford16_components`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford16_linearIndependent`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford16_span_top`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford16_trace_orthogonal`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.clifford_anticommutator`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.diracAdjoint`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.diracBilinear`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.dirac_axial_vector_covariant`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.dirac_pseudoscalar_invariant`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.dirac_scalar_invariant`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.dirac_vector_covariant`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.feynman_slash_sq`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma5`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma5_anticommutes`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma5_explicit`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma5_hermitian`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma5_sq`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma5_trace_zero`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gammaLower`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gammaTensor`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma_four_trace`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma_hermitian_conjugate`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma_trace_zero`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.gamma_two_trace`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.minkowski_slash_sq`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.no_majorana_weyl_4d`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.slash`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.γ`
- Truth anchor: `D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D.η`
- Dependency: [D5/S3/Geometry/Lorentz/SL2CLorentzCover4D](SL2CLorentzCover4D.md)
