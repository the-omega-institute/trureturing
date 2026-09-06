# Finite moment support reduction for causal response laws

## Abstract

Finite rational causal laws can be compressed relative to the linear information actually retained. The global joint feature profile exposes indistinguishable states and affine redundancy, while Caratheodory supplies a positive law-specific latent witness controlled by profile rank rather than the full response-table cardinality.

**Definition 1.1 (Retained moment vector).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.lawMomentVector`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.lawMomentVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Collect a finite family of rational atom features into their expectation vector under one normalized response law.

**Definition 1.2 (Affine rank of joint atom profiles).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.profileAffineRank`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.profileAffineRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Measure the affine dimension of the range of the retained feature map. Duplicate profiles and affine dependencies do not increase this rank.

**Theorem 1.3 (Moments lie in the atom-profile convex hull).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.lawMomentVector_mem_convexHull`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.lawMomentVector_mem_convexHull` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalization and nonnegativity express the retained moment vector as a convex combination of original atom profiles.

**Definition 1.4 (Positive sparse moment witness).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.MomentCompression`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.MomentCompression` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A compression stores original feature profiles, positive normalized weights, exact moment equality, affine independence, and a finite cardinality bound.

**Theorem 1.5 (Every finite law has a small exact moment witness).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.exists_momentCompression`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.exists_momentCompression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib Caratheodory reduction selects an affinely independent positive atomic representation of the exact moment vector.

**Definition 1.6 (Join LP rows and one query).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.linearRowQueryFeature`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.linearRowQueryFeature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constraint rows occupy some coordinates of an Option index and the none coordinate stores the objective.

**Definition 1.7 (Constraint-aware LP profile rank).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.linearProblemProfileRank`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.linearProblemProfileRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the affine rank of the joint vector consisting of every LP row coefficient and the objective coefficient on each original atom.

**Theorem 1.8 (Profile rank is bounded by the raw row count).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.linearProblemProfileRank_le`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.linearProblemProfileRank_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joint LP profile rank is at most the number of constraint rows plus the one objective coordinate.

**Theorem 1.9 (Every feasible query point has a small attaining latent model).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.finite_linear_problem_small_latent_witness`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.finite_linear_problem_small_latent_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every feasible finite linear causal law admits an attaining positive latent realization with at most the row count plus two states.

**Definition 1.10 (All response-cell marginals plus one query).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.responseTableCellQueryFeature`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.responseTableCellQueryFeature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For k Boolean response-pair strata, retain all four one-stratum response-cell indicators and one scalar query.

**Theorem 1.11 (Linear-size witness inside the four-to-the-k table space).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.exists_responseTableCellQueryCompression`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.exists_responseTableCellQueryCompression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Although the unrestricted response-table carrier has four to the k atoms, all one-stratum four-cell marginals and one query have a positive witness using at most four k plus two atoms.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.MomentCompression`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.exists_momentCompression`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.exists_responseTableCellQueryCompression`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.finite_linear_problem_small_latent_witness`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.lawMomentVector`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.lawMomentVector_mem_convexHull`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.linearProblemProfileRank`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.linearProblemProfileRank_le`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.linearRowQueryFeature`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.profileAffineRank`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.responseTableCellQueryFeature`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding](QuaternaryResponseTableCoding.md)
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/MarkovianResponseLawFactorization](../PartialIdentification/MarkovianResponseLawFactorization.md)
