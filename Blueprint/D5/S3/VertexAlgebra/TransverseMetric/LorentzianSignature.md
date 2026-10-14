# Lorentzian inertia and native transverse positivity

## Abstract

Lorentzian inertia and native transverse positivity

A real invertible null-pair frame splits the original ambient quadratic form into a hyperbolic plane and the actual transverse row Gram. The argument applies to every supported rank and does not require the frame to be orthonormal, its entries to be integral, or the ambient Gram to be positive definite. The ambient signature is the actual positive-minus-negative inertia count. The resulting strict positivity statements concern the original algebraic transverse polynomial image and its native degree-one tensor states. Physical-image equivalence, quotient positivity, the neutral radical, a full no-ghost theorem and the string or AdS/CFT bridge are separate conclusions not supplied here.

**Definition 1.1 (Null axes and the transverse coordinates).**

Lean statement: `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.axisEquiv`

*Formalization.* `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.axisEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two distinct axes partition all ambient coordinates into the two null coordinates and the literal transverse subtype.

**Theorem 1.2 (Dimension of the transverse sector).**

Lean statement: `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.transverse_card`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.transverse_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The partition proves that the transverse cardinality plus two is exactly the ambient rank, including rank two.

**Definition 1.3 (The actual coordinate splitting).**

Lean statement: `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.coordinateEquiv`

*Formalization.* `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.coordinateEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward map evaluates the two null coordinates and restricts to the transverse coordinates. Its inverse inserts exactly these coordinates.

**Definition 1.4 (The real frame matrix).**

Lean statement: `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.realFrame`

*Formalization.* `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.realFrame` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every matrix entry is the real part of the original complex frame entry. Star-fixed entries recover the original frame without changing its normalization.

**Theorem 1.5 (Hyperbolic plane and the literal transverse Gram).**

Lean statement: `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.ambient_equivalent_split`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.ambient_equivalent_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The supplied frame inverses give a real invertible change of basis. The two dual-row laws fix the hyperbolic block to two times the product of the null coordinates and annihilate the cross terms with every transverse coordinate. No orthonormality or diagonal transverse matrix is assumed.

**Theorem 1.6 (Lorentzian inertia implies transverse positivity).**

Lean statement: `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.transverseGram_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.transverseGram_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hyperbolic block has signature zero. Signature additivity and invariance therefore give transverse signature equal to its dimension. The maximal positive subspace then has full dimension and is the whole transverse space. The mostly-plus convention is positive-minus-negative signature equal to ambient rank minus two.

**Theorem 1.7 (Strict native polynomial positivity).**

Lean statement: `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.nativePolynomial_positive_of_lorentzian`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.nativePolynomial_positive_of_lorentzian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proved Gram positivity is inserted into the original finite-support complex polynomial Fock theorem. Every nonzero native transverse polynomial has a strictly positive real norm and zero imaginary part, without a fixed energy or occupation cutoff.

**Theorem 1.8 (The original degree-one negative right-C0 pairing).**

Lean statement: `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.native_degree_one_negative_C0_positive_of_lorentzian`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.native_degree_one_negative_C0_positive_of_lorentzian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same Gram theorem supplies the original native State and J-eigenvalue-one theorem with both Gram inverse laws and both frame inverse laws. The sign is exactly the negative of the original right-C0 Hermitian pairing; neither a physical cohomology quotient nor its positivity is inferred.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.ambient_equivalent_split`
- Truth anchor: `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.axisEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.coordinateEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.nativePolynomial_positive_of_lorentzian`
- Truth anchor: `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.native_degree_one_negative_C0_positive_of_lorentzian`
- Truth anchor: `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.realFrame`
- Truth anchor: `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.transverseGram_posDef`
- Truth anchor: `D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.transverse_card`
- Dependency: [D5/S3/QuadraticForms/ActualSignature](../../QuadraticForms/ActualSignature.md)
- Dependency: [D5/S3/VertexAlgebra/TransverseMetric/NativePositivity](NativePositivity.md)
