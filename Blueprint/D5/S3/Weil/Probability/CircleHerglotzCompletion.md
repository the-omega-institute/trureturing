# CircleHerglotzCompletion

## Abstract

Circle probability measures, the existing negative-power Fourier moments, and the existing Toeplitz matrices.

**Theorem 1.1 (Weak continuity of each original moment).**

Lean statement: `D5/S3/Weil/Probability/CircleHerglotzCompletion.circleMoment_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CircleHerglotzCompletion.circleMoment_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same negative-power circle moment is continuous on the actual weak probability-measure space.

**Theorem 1.2 (All original moments determine the measure).**

Lean statement: `D5/S3/Weil/Probability/CircleHerglotzCompletion.circle_moment_ext`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CircleHerglotzCompletion.circle_moment_ext` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transport the existing AddCircle Fourier uniqueness theorem through the standard circle homeomorphism, retaining the sign convention.

**Theorem 1.3 (Hermitian symmetry is derived).**

Lean statement: `D5/S3/Weil/Probability/CircleHerglotzCompletion.hermitian_of_all_toeplitz`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CircleHerglotzCompletion.hermitian_of_all_toeplitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Matrix entries at each positive and negative index force conjugation symmetry; no symmetry premise is added.

**Theorem 1.4 (One common measure for every finite order).**

Lean statement: `D5/S3/Weil/Probability/CircleHerglotzCompletion.circle_herglotz_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CircleHerglotzCompletion.circle_herglotz_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing finite atomic representations give nested nonempty closed subsets of a compact probability-measure space. Their intersection supplies all moments at once.

**Theorem 1.5 (Normalized Toeplitz positivity characterizes a unique measure).**

Lean statement: `D5/S3/Weil/Probability/CircleHerglotzCompletion.circle_herglotz_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CircleHerglotzCompletion.circle_herglotz_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalization is explicit. The existence conclusion includes uniqueness of the actual Borel probability measure.

**Theorem 1.6 (All moments characterize weak continuity).**

Lean statement: `D5/S3/Weil/Probability/CircleHerglotzCompletion.continuous_iff_circleMoments`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CircleHerglotzCompletion.continuous_iff_circleMoments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compactness and existing measure uniqueness make the complete moment profile a topological embedding. Finite-mode reconstruction is not asserted.

**Theorem 1.7 (All moments characterize weak convergence).**

Lean statement: `D5/S3/Weil/Probability/CircleHerglotzCompletion.tendsto_iff_circleMoments`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CircleHerglotzCompletion.tendsto_iff_circleMoments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original complete moment profile identifies weak convergence along arbitrary filters, reusing the same compact embedding.

**Theorem 1.8 (Every finite-order witness sequence has the same weak limit).**

Lean statement: `D5/S3/Weil/Probability/CircleHerglotzCompletion.finite_moment_witnesses_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CircleHerglotzCompletion.finite_moment_witnesses_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any probability witnesses matching all modes up to their respective orders converge as a whole sequence. No compatibility of consecutive choices is assumed; no quantitative rate is asserted.

## References

- Truth anchor: `D5/S3/Weil/Probability/CircleHerglotzCompletion.circleMoment_continuous`
- Truth anchor: `D5/S3/Weil/Probability/CircleHerglotzCompletion.circle_herglotz_exists`
- Truth anchor: `D5/S3/Weil/Probability/CircleHerglotzCompletion.circle_herglotz_iff`
- Truth anchor: `D5/S3/Weil/Probability/CircleHerglotzCompletion.circle_moment_ext`
- Truth anchor: `D5/S3/Weil/Probability/CircleHerglotzCompletion.continuous_iff_circleMoments`
- Truth anchor: `D5/S3/Weil/Probability/CircleHerglotzCompletion.finite_moment_witnesses_tendsto`
- Truth anchor: `D5/S3/Weil/Probability/CircleHerglotzCompletion.hermitian_of_all_toeplitz`
- Truth anchor: `D5/S3/Weil/Probability/CircleHerglotzCompletion.tendsto_iff_circleMoments`
- Dependency: [D5/S3/Observer/MeasureSeparation/FourierModeDetermination](../../Observer/MeasureSeparation/FourierModeDetermination.md)
- Dependency: [D5/S3/Weil/CayleyLaguerre/TruncatedCircleMomentBridge](../CayleyLaguerre/TruncatedCircleMomentBridge.md)
- Dependency: [D5/S3/Weil/TestFunctions/LiCurvatureCriterion](../TestFunctions/LiCurvatureCriterion.md)
