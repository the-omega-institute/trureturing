# OriginalFourMChargeCoset

## Abstract

Original lattice twisted-sector coefficient reduction, preserving the original carriers and operators.

**Theorem 1.1 (Statewise oscillator factorization).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.corrected_tmul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.corrected_tmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All original source charges, source polynomials, integer doubled exponents, oscillator inputs and selected ground vectors occur. Normal-order recursion retains e+2m+2r+3 and both ordering branches; Corr is the original finite correction with e+2s. Mode sums are finite after application to an input, proved by projecting a genuine actual tensor coefficient along an inverse charged ground action. No endomorphism-valued infinite sum is asserted.

**Theorem 1.2 (Original ground Fourier exchange).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.ground_exchange_first`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.ground_exchange_first` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected ground pairing and the actual charge representation give the exact quadratic and bilinear Fourier signs. Ground completeness consumes OperatorAlgebra.actual_operator_algebra and its reconstruction of rank-one endomorphisms. No ground-basis or reconstruction hypothesis is added.

**Theorem 1.3 (Signed full-energy-fiber coset factorization).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.fourM_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.fourM_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original global inverse I is paired in the first detector slot. The sum ranges over every signed EnergyFiber element, with its original dual inverse-Gram polynomial and occupation factorials. Both chargeScalar factors and exactly one theta half-average remain. Actual homogeneous u,v are polynomial tensors, the third tensor and the detector are unrestricted, and both mode indices are integers.

**Theorem 1.4 (The original scalar detector reduction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.original_jacobi_tensor_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.original_jacobi_tensor_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer m,n,r, use the three sharp finite j cutoffs and common ell output-weight cutoff. Recover all actual detectors by tensor induction. The below-two branch follows the original exact zero and cutoff facts. This statement concerns tensor inputs; the all-input extension is proved separately in OriginalFourMReduction.

**Theorem 1.5 (Independent ground tensors eliminate the four ground variables).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.coset_ground_elimination`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.coset_ground_elimination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two Fourier exchanges and independence in the accepted actual operator basis identify the common-channel coefficients. The original ground dimension is 2^12; the Fourier coefficient is its inverse 2^-12. identityK is the explicit channelA/B/D identity built from cosetKernel. It is not defined as Jacobi and is not proved here.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.corrected_tmul`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.coset_ground_elimination`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.fourM_factorization`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.ground_exchange_first`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.original_jacobi_tensor_kernel`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/ActualPairingSymmetry](ActualPairingSymmetry.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OperatorAlgebra](OperatorAlgebra.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients](OriginalFourMCoefficients.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalRightSkew](OriginalRightSkew.md)
