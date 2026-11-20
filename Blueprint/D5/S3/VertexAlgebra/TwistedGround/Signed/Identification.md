# Identification of the original Gaussian kernels in six signed sectors

## Abstract

Identification of the original Gaussian kernels in six signed sectors

**Definition 1.1 (Candidate selected by the original kernel flag).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/Identification.signedCandidate`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Signed/Identification.signedCandidate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For Boolean square, e and f and complex u, v and r, signedCandidate(square,e,f,u,v,r) selects candidateT(e,f,u,v,r) if square is true and candidateJ(e,f,u,v,r) if square is false. The labels e and f are the same Boolean labels used in kernelMode.

**Theorem 1.2 (Literal J and T equal their signed candidates).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Signed/Identification.six_sector_identification`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Signed/Identification.six_sector_identification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Boolean square, e and f with e = false or f = false, complex u and v, and real 0 < r < 1 with ‖u‖ + √r < 1 and ‖v‖ + √r < 1, kernelMode(square,e,f,u,v,(√r : ℂ)) = signedCandidate(square,e,f,u,v,(r : ℂ)). Here kernelMode is the full original ℕ × ℕ mode sum of externalJ or externalT coefficients weighted by uᵖvᑫ. The three label pairs (−−), (−+), and (+−) apply to both kernel flags. The axes and diagonal are included.

At fixed r, subtract the candidate from the literal kernel on the bidisk of radius 1 − √r. The original Hilbert mode theorem and candidate regularity give joint complex differentiability, so restriction to either coordinate slice justifies subtraction of derivatives. `D5/S3/VertexAlgebra/TwistedGround/PositiveJ/Identification.kernelMode_joint_differentiable`, `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidates_original_joint_differentiable`

The literal displacement equations and the corresponding J and T candidate equations have the same original modeA and modeH source with the same period ratio. The J equations also have the identical modeB(e)modeB(f) term. Subtracting gives the homogeneous equation with the sum for J and the difference for T. `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations.displacement_differential`, `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.candidateJ_original_displacement`, `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateT_original_displacement`

Apply signed_spatial_zero directly to the difference on that bidisk using the negative-label hypothesis. Its slice argument uses the analytic identity lemma eqOn_zero_of_preconnected_of_eventuallyEq_zero to extend local vanishing over the whole slice disk. `D5/S3/VertexAlgebra/TwistedGround/Signed/SpatialUniqueness.signed_spatial_zero`

This equality supplies the positive-real radial values for the later complex radial identification in the same six sectors. That transport applies eqOn_of_preconnected_of_mem_closure to the original kernel and the candidate composed with z ↦ z², using the real equalities accumulating at z = 0.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations.displacement_differential`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/PositiveJ/Identification.kernelMode_joint_differentiable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidateT_original_displacement`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource.candidates_original_joint_differentiable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/Identification.signedCandidate`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/Identification.six_sector_identification`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.candidateJ_original_displacement`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Signed/SpatialUniqueness.signed_spatial_zero`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/PositiveJ/Identification](../PositiveJ/Identification.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial](JSpatial.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Signed/SpatialUniqueness](SpatialUniqueness.md)
