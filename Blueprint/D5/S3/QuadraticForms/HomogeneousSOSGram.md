# Positive Gram matrices and closed homogeneous SOS cones

## Abstract

Positive Gram matrices and closed homogeneous SOS cones

The polynomial cone uses the native unrestricted real sum-of-squares predicate. Homogeneous square extraction and genuine PSD Gram factorization supply its finite representation. These results supply polynomial prerequisites for GNP; the tensor-extension characterization is a separate obligation.

**Definition 1.1 (Fixed-degree monomials).**

Lean statement: `D5/S3/QuadraticForms/HomogeneousSOSGram.Exponent`

*Formalization.* `D5/S3/QuadraticForms/HomogeneousSOSGram.Exponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All finitely supported nonnegative integer exponents with the prescribed total degree are retained, including degree zero and the empty variable type.

**Definition 1.2 (Actual homogeneous coefficient form).**

Lean statement: `D5/S3/QuadraticForms/HomogeneousSOSGram.form`

*Formalization.* `D5/S3/QuadraticForms/HomogeneousSOSGram.form` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient vector is expanded in the ordinary monomials, without multinomial weights or normalization factors.

**Definition 1.3 (Actual Gram polynomial).**

Lean statement: `D5/S3/QuadraticForms/HomogeneousSOSGram.gram`

*Formalization.* `D5/S3/QuadraticForms/HomogeneousSOSGram.gram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix entry indexed by exponents a,b multiplies the monomial with exponent a+b. Positivity is ordinary real matrix positive semidefiniteness.

**Theorem 1.4 (Native SOS iff positive Gram representation).**

Lean statement: `D5/S3/QuadraticForms/HomogeneousSOSGram.homogeneous_sos_iff_gram`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/HomogeneousSOSGram.homogeneous_sos_iff_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every homogeneous real form of degree twice d is a native sum of squares exactly when it is the actual Gram polynomial of a PSD real matrix on all degree-d monomials. The forward direction uses homogeneous square representatives; the converse factors the PSD matrix.

**Definition 1.5 (Gram coefficient map).**

Lean statement: `D5/S3/QuadraticForms/HomogeneousSOSGram.gramMap`

*Formalization.* `D5/S3/QuadraticForms/HomogeneousSOSGram.gramMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This real linear map extracts the actual degree-2d coefficients of the Gram polynomial.

**Definition 1.6 (Native homogeneous SOS coefficient cone).**

Lean statement: `D5/S3/QuadraticForms/HomogeneousSOSGram.sosCoefficients`

*Formalization.* `D5/S3/QuadraticForms/HomogeneousSOSGram.sosCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Membership means that the corresponding actual homogeneous polynomial is a native sum of squares; it is not defined as a closure or a relaxed cone.

**Theorem 1.7 (Closedness of the native homogeneous SOS cone).**

Lean statement: `D5/S3/QuadraticForms/HomogeneousSOSGram.sosCoefficients_closed`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/HomogeneousSOSGram.sosCoefficients_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A zero Gram polynomial with PSD Gram matrix forces every square representative, hence the matrix, to vanish. Compactness of the cone's unit slice then bounds lifts under the coefficient projection and proves its image closed. This closedness does not remove the closure from the ordinary DPS polar-sum identity.

## References

- Truth anchor: `D5/S3/QuadraticForms/HomogeneousSOSGram.Exponent`
- Truth anchor: `D5/S3/QuadraticForms/HomogeneousSOSGram.form`
- Truth anchor: `D5/S3/QuadraticForms/HomogeneousSOSGram.gram`
- Truth anchor: `D5/S3/QuadraticForms/HomogeneousSOSGram.gramMap`
- Truth anchor: `D5/S3/QuadraticForms/HomogeneousSOSGram.homogeneous_sos_iff_gram`
- Truth anchor: `D5/S3/QuadraticForms/HomogeneousSOSGram.sosCoefficients`
- Truth anchor: `D5/S3/QuadraticForms/HomogeneousSOSGram.sosCoefficients_closed`
- Dependency: [D5/S3/QuadraticForms/HomogeneousSOS](HomogeneousSOS.md)
