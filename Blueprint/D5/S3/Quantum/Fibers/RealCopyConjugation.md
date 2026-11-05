# Real Copy Statistics and Conjugation

## Abstract

Every complete real joint measurement on at least two independent copies determines a complex density state up to conjugation in the specified real basis.

**Definition 1.1 (Native density-state matrix coordinates).**

Lean statement: `D5/S3/Quantum/Fibers/RealCopyConjugation.stateMatrix`

*Formalization.* `D5/S3/Quantum/Fibers/RealCopyConjugation.stateMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input is the native density-state subtype: a positive complex matrix with trace one. Matrix coordinates use its star algebra equivalence. No purity, invertibility, or nonzero imaginary coordinate is required.

**Definition 1.2 (The entire real effect interval).**

Lean statement: `D5/S3/Quantum/Fibers/RealCopyConjugation.RealEffect`

*Formalization.* `D5/S3/Quantum/Fibers/RealCopyConjugation.RealEffect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An effect is a positive semidefinite complex matrix whose complement in the identity is positive semidefinite and whose entries have zero imaginary part. Positivity supplies Hermitian symmetry, so these are exactly the real symmetric operators between zero and the identity in the specified basis.

**Definition 1.3 (A projection onto two basis vectors).**

Lean statement: `D5/S3/Quantum/Fibers/RealCopyConjugation.pairEffect`

*Formalization.* `D5/S3/Quantum/Fibers/RealCopyConjugation.pairEffect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For distinct basis indices, take one half of the outer product of their sum with its conjugate. This is a real effect: the matrix and its complement are positive semidefinite, and its entries are real.

**Definition 1.4 (Physical trace probabilities).**

Lean statement: `D5/S3/Quantum/Fibers/RealCopyConjugation.probability`

*Formalization.* `D5/S3/Quantum/Fibers/RealCopyConjugation.probability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The probability is the real part of the trace of the effect times the state, with its membership in the closed unit interval proved from positivity and trace normalization. Positivity of this trace also gives its zero imaginary part.

**Definition 1.5 (Equality on every real effect).**

Lean statement: `D5/S3/Quantum/Fibers/RealCopyConjugation.SameRealStatistics`

*Formalization.* `D5/S3/Quantum/Fibers/RealCopyConjugation.SameRealStatistics` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Statistical equality quantifies over every effect in the real effect interval. The coordinate projectors and the normalized projectors on sums of two basis vectors are valid effects. Their probabilities recover all entries of the real symmetric part; they are separate measurement settings.

**Definition 1.6 (The physical conjugate state).**

Lean statement: `D5/S3/Quantum/Fibers/RealCopyConjugation.conjugate`

*Formalization.* `D5/S3/Quantum/Fibers/RealCopyConjugation.conjugate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On Hermitian input, transpose is entrywise complex conjugation. Transpose preserves positivity, trace, and rank, including on every singular stratum.

**Definition 1.7 (Joint product-basis labels).**

Lean statement: `D5/S3/Quantum/Fibers/RealCopyConjugation.CopyIndex`

*Formalization.* `D5/S3/Quantum/Fibers/RealCopyConjugation.CopyIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Zero copies use a singleton basis, one copy uses the original basis, and successive copies use Cartesian products. This construction allows an arbitrary finite basis type, including an empty carrier.

**Definition 1.8 (Independent identically prepared tensor copies).**

Lean statement: `D5/S3/Quantum/Fibers/RealCopyConjugation.copies`

*Formalization.* `D5/S3/Quantum/Fibers/RealCopyConjugation.copies` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each positive copy count is constructed recursively with the native productState Kronecker product, preserving positivity and trace one. The zero-copy matrix is the identity on the singleton carrier. Empty input carriers have no trace-one density states.

**Theorem 1.9 (Complete classification and fixed and rank strata).**

$$\forall n\in\operatorname{Type}(),[\operatorname{Fintype}(n)] [\operatorname{DecidableEq}(n)],\\\forall \rho,\sigma\in\operatorname{DensityState}(n),\\(\operatorname{SameRealStatistics}(\operatorname{copies}(\rho,2),\operatorname{copies}(\sigma,2)) \iff (\sigma=\rho \lor \sigma=\operatorname{conjugate}(\rho))) \land\\((\forall k\geq1,\operatorname{SameRealStatistics}(\operatorname{copies}(\rho,k),\operatorname{copies}(\sigma,k))) \iff (\sigma=\rho \lor \sigma=\operatorname{conjugate}(\rho))) \land\\(\forall k\geq2,(\operatorname{SameRealStatistics}(\operatorname{copies}(\rho,k),\operatorname{copies}(\sigma,k)) \iff (\sigma=\rho \lor \sigma=\operatorname{conjugate}(\rho)))) \land\\(\operatorname{conjugate}(\rho)=\rho \iff \operatorname{Im}(\operatorname{stateMatrix}(\rho))=0) \land\\(\forall k\geq2,\operatorname{SameRealStatistics}(\operatorname{copies}(\rho,k),\operatorname{copies}(\sigma,k)) \implies \operatorname{rank}(\operatorname{stateMatrix}(\sigma))=\operatorname{rank}(\operatorname{stateMatrix}(\rho)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/RealCopyConjugation.real_copy_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem states the two-copy equivalence, the equivalence for all positive copy counts, and the equivalence for every fixed count at least two. The two possible states are the original state and its conjugate. They coincide exactly when every imaginary entry is zero. Otherwise the fiber has exactly two distinct states. Every state in the fiber has the same matrix rank. These statements include mixed and singular states and do not assume a geometric chart.

**Definition 1.10 (Actual normalized one-copy coordinate).**

Lean statement: `D5/S3/Quantum/Fibers/RealCopyConjugation.fiveModeRealCoordinate`

*Formalization.* `D5/S3/Quantum/Fibers/RealCopyConjugation.fiveModeRealCoordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a Fin 5 density state this is its entrywise real Hermitian matrix in the specified basis. Equality of every real effect probability is proved equivalent to equality of these coordinates.

**Definition 1.11 (Actual physical statistical image).**

Lean statement: `D5/S3/Quantum/Fibers/RealCopyConjugation.fiveModePhysicalImage`

*Formalization.* `D5/S3/Quantum/Fibers/RealCopyConjugation.fiveModePhysicalImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The image ranges over native positive trace-one density matrices, including mixed, rank-deficient, and real states. It is not an assumed chart.

**Theorem 1.12 (Normalized visible dimension fourteen).**

$$\operatorname{finrank}(\operatorname{Real}(),\operatorname{direction}(\operatorname{affineSpan}(\operatorname{Real}(),\operatorname{fiveModePhysicalImage}())))=14 \land\\(\forall \rho,\sigma\in\operatorname{FiveModeState}(),\operatorname{SameRealStatistics}(\rho,\sigma) \iff \operatorname{fiveModeRealCoordinate}(\rho)=\operatorname{fiveModeRealCoordinate}(\sigma))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/RealCopyConjugation.five_mode_physical_image_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The affine direction of the actual normalized one-copy image has finrank 14. The proof uses the trace-one symmetric carrier and actual positive/negative density perturbations, so the number is intrinsic to this image and not a finite-state count. The same theorem identifies equality on the entire real effect interval with equality of these actual coordinates.

**Definition 1.13 (Literal conjugation orbit relation).**

Lean statement: `D5/S3/Quantum/Fibers/RealCopyConjugation.fiveModeOrbitRel`

*Formalization.* `D5/S3/Quantum/Fibers/RealCopyConjugation.fiveModeOrbitRel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quotient identifies exactly a state with itself or with its entrywise complex conjugate. This is a nonlinear finite orbit identification on actual density states, not a linear kernel quotient.

**Definition 1.14 (Actual orbit quotient carrier).**

Lean statement: `D5/S3/Quantum/Fibers/RealCopyConjugation.fiveModeOrbitQuotient`

*Formalization.* `D5/S3/Quantum/Fibers/RealCopyConjugation.fiveModeOrbitQuotient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quotient is constructed from the density-state setoid and has a surjective representative projection. Every rank stratum and the real fixed stratum remain in its domain.

Two-copy real entries have the form of a product of two real entries minus a product of two imaginary entries. The actual partial trace recovers the one-copy real matrix because the second density matrix has trace one. Equality then fixes every product of imaginary entries. A nonzero imaginary entry fixes one common sign for all entries; if none exists, both matrices are real. Repeated actual partial traces reduce any larger copy count to two copies. Conjugation commutes with the Kronecker products and preserves all real-effect probabilities.

The statement requires independent preparation and the full real joint effect interval. A restricted single-system gate menu does not establish either requirement. In five modes the actual normalized one-copy image has affine dimension fourteen, and the conjugation identification acts on actual normalized density matrices. Rank-boundary states and the real fixed stratum remain in the quotient domain.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/RealCopyConjugation.CopyIndex`
- Truth anchor: `D5/S3/Quantum/Fibers/RealCopyConjugation.RealEffect`
- Truth anchor: `D5/S3/Quantum/Fibers/RealCopyConjugation.SameRealStatistics`
- Truth anchor: `D5/S3/Quantum/Fibers/RealCopyConjugation.conjugate`
- Truth anchor: `D5/S3/Quantum/Fibers/RealCopyConjugation.copies`
- Truth anchor: `D5/S3/Quantum/Fibers/RealCopyConjugation.fiveModeOrbitQuotient`
- Truth anchor: `D5/S3/Quantum/Fibers/RealCopyConjugation.fiveModeOrbitRel`
- Truth anchor: `D5/S3/Quantum/Fibers/RealCopyConjugation.fiveModePhysicalImage`
- Truth anchor: `D5/S3/Quantum/Fibers/RealCopyConjugation.fiveModeRealCoordinate`
- Truth anchor: `D5/S3/Quantum/Fibers/RealCopyConjugation.five_mode_physical_image_dimension`
- Truth anchor: `D5/S3/Quantum/Fibers/RealCopyConjugation.pairEffect`
- Truth anchor: `D5/S3/Quantum/Fibers/RealCopyConjugation.probability`
- Truth anchor: `D5/S3/Quantum/Fibers/RealCopyConjugation.real_copy_classification`
- Truth anchor: `D5/S3/Quantum/Fibers/RealCopyConjugation.stateMatrix`
- Dependency: [D5/S3/Quantum/Fibers/FiveModeRealResponse](FiveModeRealResponse.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Measurement/BasisMeasurementProjection](../Measurement/BasisMeasurementProjection.md)
- Dependency: [D5/S3/Quantum/Measurements/VisibleStateSpaceDimension](../Measurements/VisibleStateSpaceDimension.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation](../QuantumChannels/PositiveFilterTransposeRefutation.md)
