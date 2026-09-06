# Finite independent source grouping

## Abstract

Independent elementary disturbance laws induce one partition-independent full source law. Regrouping and local query elimination preserve that law exactly.

**Definition 1.1 (Full independent source law).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSourceLaw`

*Formalization.* `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSourceLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product of elementary rational masses is nonnegative and normalized by the pinned finite product-of-sums theorem. Noise carriers may depend on the source index.

**Theorem 1.2 (Regroup every full-source mass).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSource_mass_split`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSource_mass_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any supported block and its complement reproduce the original mass. The partition is selected after the elementary source law has been defined.

**Theorem 1.3 (Preserve every finite readout law).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSource_pushforward_regroup`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSource_pushforward_regroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reindexing the full finite sum along the standard source partition equivalence leaves every response mass unchanged.

**Theorem 1.4 (Derive actual block independence).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSource_split_law`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSource_split_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The distribution of the two coordinate blocks equals the product of their induced laws. Empty supported and complementary blocks are included.

**Theorem 1.5 (Eliminate unused sources exactly).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSource_pushforward_restrict`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSource_pushforward_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a readout that descends through source restriction, the complementary normalized law integrates to one. The remaining pushforward uses only the retained elementary laws.

**Theorem 1.6 (Recover the actual restriction marginal).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSource_restriction_marginal`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSource_restriction_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinate restriction pushes the full source law to the elementary product law on precisely the retained coordinates.

**Theorem 1.7 (Insensitivity to unused disturbance laws).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSource_readout_law_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSource_readout_law_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed supported readout, two elementary law families that agree on the support have identical output distributions. Structural equations and readouts remain fixed.

**Theorem 1.8 (Retain constraints while eliminating nuisance parameters).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.joint_event_constraint_projection_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.joint_event_constraint_projection_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The parameter region with observed joint-event probability c and target marginal x projects exactly to c <= x <= 1. When c is positive, dropping the joint-event constraint would incorrectly allow x = 0.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSourceLaw`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSource_mass_split`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSource_pushforward_regroup`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSource_pushforward_restrict`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSource_readout_law_invariant`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSource_restriction_marginal`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.independentSource_split_law`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.joint_event_constraint_projection_iff`
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/MarkovianResponseLawFactorization](MarkovianResponseLawFactorization.md)
