# Supported middle reconstruction

## Abstract

Supported middle reconstruction

**Theorem 1.1 (qSlice_lower).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.qSlice_lower`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.qSlice_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fixed finite mode fiber supplies a uniform lower first-coordinate bound for its polynomial slice. The inverse shifts only the first and spectator coordinates, so this fiber is independent of the inverse length.

**Theorem 1.2 (positiveClear_qSlice).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.positiveClear_qSlice`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.positiveClear_qSlice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive clearing commutes with the two finite polynomial sums defining qSlice. The equality uses finite sum interchange and scalar commutation.

**Theorem 1.3 (middle_bounds).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.middle_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.middle_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative numerator coordinates imply j+l <= b+k, q <= s+2k+j and q+l <= s+b+3k, together with the three signed cone inequalities and the exact first-two-coordinate balance. No individual raw target exponent is required to be nonnegative.

**Theorem 1.4 (mem_middleFiber_iff).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.mem_middleFiber_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.mem_middleFiber_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The containing finite box filtered by all three nonnegative numerator coordinates contains exactly every admissible triple. The box bounds follow from the signed balances, including all negative target branches.

**Theorem 1.5 (middleSum_zero).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.middleSum_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.middleSum_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact finite sum vanishes when b+k, s+b+3k, or the total shifted exponent s+b+z+3k+a0+a1+a2 is negative.

**Theorem 1.6 (middleCutoffSum_eq).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.middleCutoffSum_eq`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.middleCutoffSum_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every auxiliary T at least k, the successive finite inverse sum equals the same exact middleFiber sum. Padding the j and q ranges contributes only zero native numerator coefficients. The negative b+T branch is included.

**Theorem 1.7 (qSlice_partialClear).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.qSlice_partialClear`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.qSlice_partialClear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full finite slice equals difference clearing of the partial positive clearing, with both original monomial shifts s^k and y^k retained.

**Theorem 1.8 (original_middle_reconstruction).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.original_middle_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.original_middle_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a commutative complex algebra, a raw family with a uniform lower second-coordinate bound and a derived short positive inverse is recovered by the exact finite middleFiber sum whenever its cleared numerator vanishes outside the native nonnegative octant. The short inverse is a premise of this general supplier; the actual canonical consumer proves it from descendant truncation. No finite-support assumption is imposed on the numerator. Supported difference and positive inversions are reused from SupportedChannelSeries, retaining Carnahan attribution. The chamber is b << s << z; no substitution is applied to an unrestricted raw distribution.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.mem_middleFiber_iff`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.middleCutoffSum_eq`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.middleSum_zero`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.middle_bounds`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.original_middle_reconstruction`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.positiveClear_qSlice`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.qSlice_lower`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldOriginalMiddleInverse.qSlice_partialClear`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/SupportedCollisionSlice](SupportedCollisionSlice.md)
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber](ThreeFieldFinalLaurentFiber.md)
