# Canonical two-cut occupation sewing

## Abstract

Literal two-cut occupation control for canonical lattice coefficients.

The overlap envelope retains both unrestricted occupations and the literal factorialEnvelope. MixedControl records the all-mode coefficient estimate with the explicit energy polynomial and the finite positive overlap family. The analytic comparison theorem then consumes a summable majorant to obtain the exact signed-mode pair sum, including zero radial parameters.

**Definition 1.1 (Uniform mixed descendant control).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CanonicalTwoCutOccupation.MixedControl`

*Formalization.* `D5/S3/VertexAlgebra/Sewing/CanonicalTwoCutOccupation.MixedControl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary signed modes and both occupations, the literal wordCoeff is bounded by the recursively defined word constant, the total-energy polynomial and the finite overlap envelope built from binomial(e,u), T^(degree(e-u)) and factorialEnvelope A(d-u). The predicate keeps the charge coefficient buffers A and T explicit. The recurrence proof and the summability of this majorant remain separate obligations of the sewing owner.

**Theorem 1.2 (Two-index absolute summability comparison).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CanonicalTwoCutOccupation.mixed_pair_summable_of_control`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sewing/CanonicalTwoCutOccupation.mixed_pair_summable_of_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assuming the exact mixed coefficient control and a summable literal overlap majorant, comparison yields the original pair-index kernel with rowWeight on the first occupation, columnWeight on the second occupation, arbitrary signed offset s+level(e)-level(d), and both open-disk parameters. No inverse Gram, positivity or nonzero-q premise is introduced by the comparison.

The source definitions are the original private canonical maps, wordCoeff, rowWeight, columnWeight and factorialEnvelope accessed through Batteries.Tactic.OpenPrivate. The finite overlap expression is a proof-local majorant, not a replacement field. The unproved coefficient induction and majorant summability are intentionally not claimed as completed by this unit.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CanonicalTwoCutOccupation.MixedControl`
- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CanonicalTwoCutOccupation.mixed_pair_summable_of_control`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner](../Sectors/LatticeSectorIntertwiner.md)
- Dependency: [D5/S3/VertexAlgebra/Sewing/CanonicalOccupation](CanonicalOccupation.md)
