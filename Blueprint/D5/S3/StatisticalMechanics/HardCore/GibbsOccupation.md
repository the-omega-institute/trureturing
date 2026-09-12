# GibbsOccupation

## Abstract

Actual occupation, normalized Gibbs probabilities and analytic response.

**Definition 1.1 (gibbsMass).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbsMass`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbsMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual normalized Gibbs mass. Configurations outside the finite independent family have zero mass. Its probability properties are proved for lambda >= 0.

**Theorem 1.2 (gibbs mass nonneg).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbs_mass_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbs_mass_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All actual masses are nonnegative, including the zero-activity endpoint.

**Theorem 1.3 (mass moment eq).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.mass_moment_eq`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.mass_moment_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact normalized raw moments, before imposing positivity or a probability interpretation. The normalization denominator is the actual partition.

**Theorem 1.4 (gibbs mass sum).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbs_mass_sum`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbs_mass_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete family of actual configurations has total probability one.

**Definition 1.5 (gibbsPMF).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbsPMF`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbsPMF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Gibbs law is a standard Mathlib PMF on actual finite vertex sets. The ambient graph need not be finite. No external probability oracle is used.

**Theorem 1.6 (gibbs pmf toReal).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbs_pmf_toReal`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbs_pmf_toReal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real-valued point masses of the actual PMF equal the normalized weights.

**Definition 1.7 (meanOccupation).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.meanOccupation`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.meanOccupation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mean particle number, subsequently identified with the actual PMF sum.

**Theorem 1.8 (gibbs expected card).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbs_expected_card`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbs_expected_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite expectation of configuration cardinality under the actual PMF is exactly the first normalized occupation moment.

**Theorem 1.9 (gibbs vertex occupied).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbs_vertex_occupied`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbs_vertex_occupied` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual probability that a marked vertex is occupied equals one minus the actual vacancy ratio. A vertex outside V has occupancy zero automatically.

**Theorem 1.10 (mean eq sum vacancies).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.mean_eq_sum_vacancies`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.mean_eq_sum_vacancies` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expected occupation is the sum of actual one-vertex occupancies. No independence among these Bernoulli indicators is assumed.

**Theorem 1.11 (mean occupation bounds).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.mean_occupation_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.mean_occupation_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mean lies between zero and the actual number of available vertices.

**Definition 1.12 (occupationVariance).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.occupationVariance`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.occupationVariance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Centered second moment under the same actual Gibbs weights.

**Theorem 1.13 (gibbs variance).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbs_variance`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbs_variance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The centered second moment equals the conventional finite PMF variance.

**Theorem 1.14 (variance eq moments).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.variance_eq_moments`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.variance_eq_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expansion of the actual centered variance into its first two raw moments.

**Theorem 1.15 (occupation variance nonneg).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.occupation_variance_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.occupation_variance_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegativity is proved from squared centered deviations and actual nonnegative masses, not postulated from the derivative formula.

**Theorem 1.16 (mean occupation fluctuation response).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.mean_occupation_fluctuation_response`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.mean_occupation_fluctuation_response` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact fluctuation-response identity. The factor lambda preserves the zero-activity endpoint and expresses differentiation in log activity.

**Theorem 1.17 (mean occupation deriv nonneg).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.mean_occupation_deriv_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.mean_occupation_deriv_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive activity the expected particle number has nonnegative ordinary derivative, as a consequence of the proved fluctuation identity.

**Theorem 1.18 (zero activity moments).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.zero_activity_moments`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.zero_activity_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero-activity mean and variance are both zero, with the empty configuration still carrying unit mass. No limiting argument is needed.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbsMass`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbsPMF`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbs_expected_card`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbs_mass_nonneg`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbs_mass_sum`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbs_pmf_toReal`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbs_variance`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.gibbs_vertex_occupied`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.mass_moment_eq`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.meanOccupation`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.mean_eq_sum_vacancies`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.mean_occupation_bounds`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.mean_occupation_deriv_nonneg`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.mean_occupation_fluctuation_response`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.occupationVariance`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.occupation_variance_nonneg`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.variance_eq_moments`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/GibbsOccupation.zero_activity_moments`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/OccupationMoments](OccupationMoments.md)
