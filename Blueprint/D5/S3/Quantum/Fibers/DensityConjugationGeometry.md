# Geometry of the Actual Density Conjugation Quotient

## Abstract

The literal conjugation quotient of all nonreal normalized five-mode density matrices has real Hausdorff dimension twenty-four in its finite orbit metric.

**Definition 1.1 (Centered Hermitian coordinates).**

Lean statement: `D5/S3/Quantum/Fibers/DensityConjugationGeometry.Coordinates`

*Formalization.* `D5/S3/Quantum/Fibers/DensityConjugationGeometry.Coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real coordinate space consists of trace-zero Hermitian five-by-five complex matrices. It carries the entrywise supremum norm inherited from matrices, namely the maximum complex absolute value of an entry.

**Definition 1.2 (Coordinates of a physical density matrix).**

Lean statement: `D5/S3/Quantum/Fibers/DensityConjugationGeometry.coordinate`

*Formalization.* `D5/S3/Quantum/Fibers/DensityConjugationGeometry.coordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract one fifth of the identity from the native positive trace-one density matrix. Reconstruction adds that same matrix. The coordinate map is injective, and every physical coordinate reconstructs a positive trace-one state.

**Definition 1.3 (The actual positivity domain).**

Lean statement: `D5/S3/Quantum/Fibers/DensityConjugationGeometry.physical`

*Formalization.* `D5/S3/Quantum/Fibers/DensityConjugationGeometry.physical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A centered coordinate is physical exactly when adding one fifth of the identity gives a positive semidefinite matrix. Trace one follows from the trace-zero coordinate condition. No determinant, purity, or rank condition restricts this set.

**Definition 1.4 (Conjugation as an isometric involution).**

Lean statement: `D5/S3/Quantum/Fibers/DensityConjugationGeometry.transpose`

*Formalization.* `D5/S3/Quantum/Fibers/DensityConjugationGeometry.transpose` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transposition preserves the centered Hermitian space and its norm. On a Hermitian matrix it is entrywise complex conjugation. Subtraction of the real center commutes with conjugation.

**Definition 1.5 (An explicit realization of the literal quotient).**

Lean statement: `D5/S3/Quantum/Fibers/DensityConjugationGeometry.orbitRealization`

*Formalization.* `D5/S3/Quantum/Fibers/DensityConjugationGeometry.orbitRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input is the literal quotient of native density states by equality or conjugation. Centered coordinates map it injectively into the orbit space of transposition. The metric on the density quotient is induced by this map, so the map is an isometry onto its image. The distance is the smaller of the two matrix distances obtained by conjugating either representative. This is a nonlinear finite orbit quotient.

**Definition 1.6 (The entire nonreal quotient subset).**

Lean statement: `D5/S3/Quantum/Fibers/DensityConjugationGeometry.fiveModeNonrealQuotient`

*Formalization.* `D5/S3/Quantum/Fibers/DensityConjugationGeometry.fiveModeNonrealQuotient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the image of every native density state that differs from its conjugate. All nonreal singular states are included. Real density states remain in the ambient quotient as its fixed stratum.

**Theorem 1.7 (Intrinsic real Hausdorff dimension twenty-four).**

$$\operatorname{dimH}\left(\operatorname{fiveModeNonrealQuotient}\left(\right)\right)=24$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/DensityConjugationGeometry.five_mode_nonreal_quotient_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual positive and negative density perturbations span every trace-zero Hermitian direction. Convexity then proves that the physical coordinate domain has nonempty interior. The fixed subspace is proper, as witnessed by the existing physical conjugate pair. Removing that subspace leaves a set with nonempty interior and Hausdorff dimension twenty-four. These steps construct the dimensional correspondence.

The finite isometric involution theorem preserves the Hausdorff dimension of this entire set. The explicit quotient realization transfers the result to the literal density quotient. This does not assert a smooth manifold chart at singular density states.

Complete real statistics on every fixed number of independent copies at least two have precisely these orbit fibers by real_copy_classification. A nonreal orbit has the two distinct states rho and its conjugate; conjugation preserves matrix rank. The real locus is fixed. The normalized one-copy statistical image has affine dimension fourteen by five_mode_physical_image_dimension. The supplied states pairState one and pairState minus one are distinct positive trace-one conjugate states and furnish a concrete candidate pair.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/DensityConjugationGeometry.Coordinates`
- Truth anchor: `D5/S3/Quantum/Fibers/DensityConjugationGeometry.coordinate`
- Truth anchor: `D5/S3/Quantum/Fibers/DensityConjugationGeometry.fiveModeNonrealQuotient`
- Truth anchor: `D5/S3/Quantum/Fibers/DensityConjugationGeometry.five_mode_nonreal_quotient_dimension`
- Truth anchor: `D5/S3/Quantum/Fibers/DensityConjugationGeometry.orbitRealization`
- Truth anchor: `D5/S3/Quantum/Fibers/DensityConjugationGeometry.physical`
- Truth anchor: `D5/S3/Quantum/Fibers/DensityConjugationGeometry.transpose`
- Dependency: [D5/S3/Geometry/InvolutionOrbitDimension](../../Geometry/InvolutionOrbitDimension.md)
- Dependency: [D5/S3/Quantum/Fibers/RealCopyConjugation](RealCopyConjugation.md)
