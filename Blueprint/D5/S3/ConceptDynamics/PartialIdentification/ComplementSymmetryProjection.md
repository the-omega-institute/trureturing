# Complement Symmetry Projection

## Abstract

Equal averaging of a real parameter with its complement projects every value to one half while erasing the antisymmetric centered defect.

The affine involution sends theta to one minus theta. Its unique fixed point is one half, and the centered defect theta minus one half changes sign under the involution.

Equal averaging applies the invariant projection and therefore returns one half for every parameter, including off-center parameters. The projected value cannot identify whether the original parameter was fixed.

For arbitrary stratum weight, the complementary query has slope two times the weight minus one. Parameter cancellation for every theta occurs exactly at equal weight.

**Theorem 1.1 (Complementary symmetrization always equals one half).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/ComplementSymmetryProjection.symmetricAverage_eq_half`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/ComplementSymmetryProjection.symmetricAverage_eq_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity follows by exact affine cancellation.

**Theorem 1.2 (The symmetric projection cannot identify the original center).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/ComplementSymmetryProjection.symmetric_average_does_not_identify_center`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/ComplementSymmetryProjection.symmetric_average_does_not_identify_center` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero is an explicit off-center parameter whose symmetrized query is still one half.

**Theorem 1.3 (Equal weight is exactly the parameter-cancelling regime).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/ComplementSymmetryProjection.weightedComplementaryQuery_constant_half_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/ComplementSymmetryProjection.weightedComplementaryQuery_constant_half_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating at zero proves necessity, while direct polynomial normalization proves sufficiency.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/ComplementSymmetryProjection.symmetricAverage_eq_half`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/ComplementSymmetryProjection.symmetric_average_does_not_identify_center`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/ComplementSymmetryProjection.weightedComplementaryQuery_constant_half_iff`
