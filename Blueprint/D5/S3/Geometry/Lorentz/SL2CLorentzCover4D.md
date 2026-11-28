# The spinor double cover of the proper orthochronous Lorentz group

## Abstract

Pauli conjugation defines a surjective homomorphism onto the proper orthochronous Lorentz matrices with kernel ±I.

Use the metric diag(1, −1, −1, −1). A four-vector specifies a Hermitian Pauli matrix, and the determinant of that matrix is the Minkowski squared norm. Determinant-one complex matrices act by conjugation with the adjoint. Euler rotations and an axial boost produce a spinor lift of each proper orthochronous Lorentz matrix.

**Definition 1.1 (Real four-vectors).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.V4`

*Formalization.* `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.V4` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Use four real coordinates in time, x, y, z order.

**Definition 1.2 (Complex two-by-two matrices).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.H2`

*Formalization.* `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.H2` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Use two rows and two columns indexed from zero.

**Definition 1.3 (The spinor group).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.SL2C`

*Formalization.* `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.SL2C` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Take the group of complex two-by-two matrices with determinant one.

**Definition 1.4 (The Minkowski metric).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.eta`

*Formalization.* `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.eta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The four diagonal entries are one, minus one, minus one and minus one.

**Definition 1.5 (Minkowski quadratic form).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.minkowskiNormSq`

*Formalization.* `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.minkowskiNormSq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Subtract the sum of the three squares of the spatial coordinates from the square of the time coordinate.

**Definition 1.6 (Hermitian Pauli coordinates).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm`

*Formalization.* `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

For coordinates (t, x, y, z), use diagonal entries t + z and t − z and off-diagonal entries x − iy and x + iy.

**Definition 1.7 (Minkowski coordinates).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.minkowski_from_pauliHerm`

*Formalization.* `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.minkowski_from_pauliHerm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Use half the real diagonal sum, the real and negated imaginary parts of the upper-right entry, and half the real diagonal difference.

**Theorem 1.8 (Hermitian image).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm_isHermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The Pauli matrix of every real four-vector equals its conjugate transpose.

**Theorem 1.9 (Recovery of the four-vector).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm_minkowski_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm_minkowski_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Taking Minkowski coordinates of the Pauli matrix recovers the original real four-vector.

**Theorem 1.10 (Recovery of the Hermitian matrix).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.minkowski_pauliHerm_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.minkowski_pauliHerm_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

For each Hermitian two-by-two complex matrix, taking Minkowski coordinates and forming the Pauli matrix recovers that matrix.

**Theorem 1.11 (Minkowski squared norm).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm_det`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The determinant of the Pauli matrix equals t² − x² − y² − z² embedded into the complex numbers.

**Theorem 1.12 (Time coordinate).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The trace of the Pauli matrix equals twice the time coordinate embedded into the complex numbers.

**Definition 1.13 (Action on four-vectors).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzVec`

*Formalization.* `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzVec` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Conjugate the Pauli matrix by the spinor matrix and its adjoint, then take Minkowski coordinates.

**Definition 1.14 (Spinor-to-Lorentz map).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C`

*Formalization.* `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The columns are the actions of spinor conjugation on the four coordinate basis vectors.

**Theorem 1.15 (Pauli covariance).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm_lorentzVec`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm_lorentzVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Encoding the transformed four-vector gives the original Pauli matrix multiplied on the left by the spinor matrix and on the right by its adjoint.

**Theorem 1.16 (Matrix action).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_mulVec`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Multiplication by the matrix of basis images agrees with spinor conjugation on every four-vector.

**Theorem 1.17 (Identity).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_one`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The identity spinor matrix maps to the identity Lorentz matrix.

**Theorem 1.18 (Multiplication).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The image of a product of spinor matrices is the product of their images in the same order.

**Theorem 1.19 (Minkowski norm preservation).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_preserves_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_preserves_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The determinant-one and Hermitian conjugation identities give preservation of the Minkowski squared norm.

**Theorem 1.20 (Metric preservation).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_preserves_minkowski`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_preserves_minkowski` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Polarization of the squared norm gives Lᵀ η L = η for each spinor image L.

**Theorem 1.21 (Time orientation).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_orthochronous`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_orthochronous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The time-time coordinate is at least one. It is half the sum of the four squared entry norms and dominates the norm of the spinor determinant.

**Theorem 1.22 (Exact two-element kernel).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_ker_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_ker_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The identity has preimages I and −I. Fixing the time basis matrix makes the spinor matrix unitary. Fixing the diagonal and off-diagonal Pauli matrices forces it to be scalar, and the square of the scalar is one.

**Theorem 1.23 (Exact fibers).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Two spinor matrices have the same image exactly when one is the other or its negative.

**Definition 1.24 (Proper orthochronous matrices).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.IsProperOrthochronous`

*Formalization.* `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.IsProperOrthochronous` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The matrix preserves the Minkowski metric, has determinant one, and has a strictly positive time-time entry.

**Theorem 1.25 (Spinor image of a z rotation).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_rotZ`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_rotZ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The image fixes time and z. On x and y, the rows are (cos θ, −sin θ) and (sin θ, cos θ).

**Theorem 1.26 (Spinor image of a y rotation).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_rotY`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_rotY` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The image fixes time and y. On x and z, the rows are (cos φ, sin φ) and (−sin φ, cos φ).

**Theorem 1.27 (Spinor image of a z boost).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_boostZ`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_boostZ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The image fixes x and y. On time and z, the diagonal entries are cosh η and the off-diagonal entries are sinh η.

**Theorem 1.28 (Determinant of a z rotation).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_rotZ_det`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_rotZ_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The spinor image of every z rotation has determinant one.

**Theorem 1.29 (Determinant of a y rotation).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_rotY_det`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_rotY_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The spinor image of every y rotation has determinant one.

**Theorem 1.30 (Determinant of a z boost).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_boostZ_det`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_boostZ_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The spinor image of every z boost has determinant one by cosh squared minus sinh squared.

**Theorem 1.31 (Lift of spatial rotations).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.so3_spinor_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.so3_spinor_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Every real three-by-three orthogonal matrix of determinant one is the spatial block of the Lorentz image of a unitary spinor matrix of determinant one.

**Theorem 1.32 (Hermitian Gram matrix of a spinor transformation).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.sl2c_gram_properties`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.sl2c_gram_properties` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The product of a determinant-one spinor matrix with its adjoint is positive definite, has determinant one, and has real trace at least two.

**Theorem 1.33 (Spinor Cartan factorization).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.sl2c_cartan_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.sl2c_cartan_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Every determinant-one spinor matrix is a product of two unitary determinant-one spinor matrices with a z boost between them.

**Theorem 1.34 (Determinant one).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_det_one`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_det_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Every spinor image has determinant one. Rotations align the spatial part of the Hermitian matrix A Aᴴ, and an axial boost removes its two positive reciprocal eigenvalues. The resulting spinor is unitary, so the spinor factors into rotations and a boost.

**Theorem 1.35 (Proper orthochronous image).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_isProperOrthochronous`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_isProperOrthochronous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Every spinor image preserves the Minkowski metric, has determinant one, and has a positive time-time entry.

**Theorem 1.36 (Constructive surjectivity).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

For a proper orthochronous Lorentz matrix, rotate the spatial part of its time column onto the nonnegative z axis and remove it with a boost. The remaining matrix fixes the time vector and has a spatial rotation block. Lift the spatial rotation by Euler angles and undo the boost and the first rotation.

**Definition 1.37 (Spinor outer product in Minkowski coordinates).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.spinor_to_future_null`

*Formalization.* `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.spinor_to_future_null` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Form the Hermitian outer product of a two-component spinor with its adjoint and take Minkowski coordinates.

**Theorem 1.38 (Recovery of the outer product).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm_spinor_outer`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm_spinor_outer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The Pauli matrix of the resulting vector has entries ψᵢ times the conjugate of ψⱼ.

**Theorem 1.39 (Nullity).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.spinor_to_future_null_null`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.spinor_to_future_null_null` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The squared Minkowski norm of the spinor image is zero because the outer product has determinant zero.

**Theorem 1.40 (Nonnegative time coordinate).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.spinor_to_future_null_time_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.spinor_to_future_null_time_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

The time coordinate of the spinor image is half the sum of the two squared spinor entry norms.

**Theorem 1.41 (Spinor-to-null equivariance).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.spinor_to_future_null_equivariant`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.spinor_to_future_null_equivariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

Transforming a spinor before taking its outer product gives the same Minkowski vector as acting on the original null vector by the associated Lorentz matrix.

**Definition 1.42 (Celestial Möbius transformation).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.sl2c_celestial_mobius`

*Formalization.* `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.sl2c_celestial_mobius` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

For the matrix with rows (a, b) and (c, d), the affine transformation is z ↦ (az + b)/(cz + d).

**Theorem 1.43 (Affine celestial equivariance).**

Lean statement: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.sl2c_celestial_mobius_equivariant`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.sl2c_celestial_mobius_equivariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Tong (2007). *Quantum Field Theory*. URL: <https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf>.

*Commentary.*

When the second coordinates of both the original and transformed spinor are nonzero, their coordinate ratios are related by the corresponding Möbius transformation.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.H2`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.IsProperOrthochronous`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.SL2C`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.V4`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.eta`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_boostZ`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_boostZ_det`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_det_one`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_eq_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_isProperOrthochronous`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_ker_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_mul`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_mulVec`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_one`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_orthochronous`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_preserves_minkowski`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_preserves_norm`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_rotY`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_rotY_det`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_rotZ`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_rotZ_det`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzOfSL2C_surjective`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.lorentzVec`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.minkowskiNormSq`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.minkowski_from_pauliHerm`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.minkowski_pauliHerm_inverse`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm_det`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm_isHermitian`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm_lorentzVec`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm_minkowski_inverse`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm_spinor_outer`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.pauliHerm_trace`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.sl2c_cartan_factorization`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.sl2c_celestial_mobius`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.sl2c_celestial_mobius_equivariant`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.sl2c_gram_properties`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.so3_spinor_lift`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.spinor_to_future_null`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.spinor_to_future_null_equivariant`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.spinor_to_future_null_null`
- Truth anchor: `D5/S3/Geometry/Lorentz/SL2CLorentzCover4D.spinor_to_future_null_time_nonneg`
