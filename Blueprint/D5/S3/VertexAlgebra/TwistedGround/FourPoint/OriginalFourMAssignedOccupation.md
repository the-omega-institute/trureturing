# Compact affine coefficients of the original chart fields

## Abstract

Signed four-point overlap in native occupations

**Definition 1.1 (Tagged native mode).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactMode`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Send a surviving mode to its colour and oscillator index in the common finite support, with leg and orientation selected by the chart flags at its puncture.

**Definition 1.2 (Compact native covariance).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactCovariance`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactCovariance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict the slit covariance of A or B, or the true D-lip covariance, to the compact tagged support and evaluate it at the chart parameter.

**Definition 1.3 (Compact native mean).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactMean`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactMean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the chart's native linear entry at a tagged oscillator by the lattice pairing of its unit colour charge with the fixed charge. Use the slit entry in A and B and the true lip entry in D.

**Theorem 1.4 (Native arrays in compact coordinates).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.mode_array_pullback`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.mode_array_pullback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For lattice data, a charge, a chart, a real chart argument and a finite support containing every assigned mode, the native covariance is the submatrix of the compact covariance indexed by the tagged mode map on both sides. The native mean is the compact mean composed with that map.

**Definition 1.5 (Compact word evaluation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactWordReadout`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactWordReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluate the compact affine coefficient at the four occupations of the mapped word and multiply by their four factorial weights.

**Theorem 1.6 (Symmetry in the radial slit charts).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactCovariance_ab_symm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactCovariance_ab_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In A or B, at a real argument whose complex chart parameter has norm less than one, the two compact covariance entries with interchanged indices are equal.

**Theorem 1.7 (Symmetry at the true D lip).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactCovariance_d_symm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactCovariance_d_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real argument strictly between zero and one, the true D-lip compact covariance entries with interchanged indices are equal. Continue the slit entry symmetry from the radial disk and take the one-sided limit at the reciprocal of the chart argument.

**Definition 1.8 (Compact charge summand).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactChargeTerm`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactChargeTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In the upper chart selection keep the period normalization, charge exponential, correction contractions and lifted scales of the physical partition sum. Read each surviving assignment by its four compact occupations and the actual signed covariance and charge-linear mean.

**Definition 1.9 (Product of puncture polynomials).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.punctureChargeTerm`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.punctureChargeTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filter the marked word at each puncture. Within each subword, sum over correction endpoints and surviving occurrences. Multiply the signed correction weight by the product of the signed linear mode rows of the survivors, all in one compact oscillator algebra. Multiply the four puncture polynomials before applying the affine occupation readout, then multiply by the upper chart period and charge factors.

**Theorem 1.10 (Factorization of the compact charge summand).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compact_charge_eq_punctures`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compact_charge_eq_punctures` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a finite label type with decidable equality. Fix a charge and a finite support containing every assigned mode. For a real argument strictly between zero and one, use A or B inside the radial disk or the true D lip. For every labelled word, the single compact positional partition sum equals the affine readout of the product of the four puncture polynomials with the same normalization. Factoring complementary subwords preserves the order within each endpoint subword and counts repeated positional choices with their full multiplicity.

**Theorem 1.11 (Rank-24 signed Fourier overlap in compact occupations).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compact_fourier_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compact_fourier_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the lattice have rank 24, unit Gram determinant and positive definite real Gram form. Fix a real argument strictly between zero and one and an A-parameter square root of norm less than one. Take any word of distinct labels from a finite decidable type, with puncture, colour and spatial degree assigned to each label and a finite support containing all assigned modes. The charge terms of every chart are absolutely summable on every mod-two charge fibre. Write V for the sum over the fibre of the full puncture charge term, including the normalized affine readout of the product, the period and the charge exponential. For any class a, V(D,a) is 2⁻¹² times the sum of V(A,b) with Fourier sign at (a,b). V(B,a) is the corresponding sum with the extra quadratic sign of b and the inverse twelfth power of the A period root. Use the true D lip and the upper chart selection throughout. The proof replaces each surviving word using `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeOccurrenceReadout.native_occurrence_readout`, using `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactCovariance_d_symm` in chart D. It then applies `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compact_charge_eq_punctures` before invoking `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap.assigned_fourier_overlap`.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactChargeTerm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactCovariance`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactCovariance_ab_symm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactCovariance_d_symm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactCovariance_d_symm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactMean`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactMode`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compactWordReadout`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compact_charge_eq_punctures`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compact_charge_eq_punctures`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.compact_fourier_overlap`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.mode_array_pullback`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation.punctureChargeTerm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap.assigned_fourier_overlap`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeOccurrenceReadout.native_occurrence_readout`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap](OriginalFourMAssignedOverlap.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCurrentRegression](OriginalFourMCurrentRegression.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeOccurrenceReadout](OriginalFourMNativeOccurrenceReadout.md)
