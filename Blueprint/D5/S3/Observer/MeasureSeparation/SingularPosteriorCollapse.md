# Posterior Collapse under Singular Laws

## Abstract

Singular transcript laws make binary posteriors collapse under generated information.

**Definition 1.1 (Binary prior mixture).**

$$\operatorname{binaryPriorMixture}\left(a, Px, Py\right) = \operatorname{ofReal}\left(a\right) \cdot Px + \operatorname{ofReal}\left(1 - a\right) \cdot Py$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.binaryPriorMixture` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The prior weights the two transcript laws, including totalized endpoints.

**Definition 1.2 (Likelihood posterior).**

$$\operatorname{likelihoodPosterior}\left(a, L\right) = \frac{a \cdot L}{a \cdot L + 1 - a}$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.likelihoodPosterior` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the exact binary likelihood normalization displayed in section 225.

**Definition 1.3 (Likelihood posterior process).**

$$\operatorname{likelihoodPosteriorProcess}\left(a, L, m, omega\right) = \operatorname{likelihoodPosterior}\left(a, \operatorname{L}\left(m, omega\right)\right)$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.likelihoodPosteriorProcess` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The likelihood posterior is evaluated at every natural observation time.

**Definition 1.4 (Conditional posterior process).**

$$\operatorname{binaryPosteriorProcess}\left(M, F, A, m, omega\right) = \operatorname{conditionalExpectation}\left(M, \operatorname{indicator}\left(A\right), \operatorname{F}\left(m\right), omega\right)$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.binaryPosteriorProcess` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The posterior is the conditional expectation of a separating-event indicator.

**Theorem 1.5 (Singular laws have collapsing posterior).**

$$\left(\operatorname{InteriorPrior}\left(a\right) \land \left(\operatorname{Generates}\left(F\right) \land \operatorname{MutuallySingular}\left(Px, Py\right)\right)\right) \Rightarrow \operatorname{ExistsPerfectSeparatorWithPosteriorLimits}\left(Px, Py, a, F, 1, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.mutually_singular_laws_have_collapsing_posterior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A perfect separator and conditional-expectation convergence give limits one and zero under the two laws.

**Theorem 1.6 (A zero prior prevents first-state completion).**

$$\neg \operatorname{Tendsto}\left(\operatorname{constantLikelihoodPosterior}\left(0\right), 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.zero_prior_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With constant unit likelihood, the posterior remains zero.

**Theorem 1.7 (A unit prior prevents second-state completion).**

$$\neg \operatorname{Tendsto}\left(\operatorname{constantLikelihoodPosterior}\left(1\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.one_prior_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With constant unit likelihood, the posterior remains one.

**Theorem 1.8 (Equal laws have no perfect separator).**

$$\neg \operatorname{ExistsPerfectSeparator}\left(\operatorname{dirac}\left(unit\right), \operatorname{dirac}\left(unit\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.equal_law_is_not_perfectly_separable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One Dirac law cannot assign both full and zero mass to the same event.

**Theorem 1.9 (The empty transcript type has no probability law).**

$$\neg \operatorname{ExistsProbabilityMeasure}\left(\emptyset\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.empty_transcript_has_no_probability_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Probability normalization forces the sample type to be nonempty.

**Theorem 1.10 (Singleton probability laws coincide).**

$$\operatorname{AllProbabilityMeasuresEqual}\left(Unit\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.unit_probability_laws_are_equal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every measurable singleton event is either empty or universal.

**Theorem 1.11 (The bottom Boolean filtration is not generating).**

$$\operatorname{join}\left(\operatorname{constantBottomFiltration}\left(Bool\right)\right) \ne \operatorname{fullMeasurableSpace}\left(Bool\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.trivial_filtration_does_not_generate_bool` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A constant bottom filtration never reveals the nontrivial Boolean event.

**Theorem 1.12 (Generation is necessary for posterior collapse).**

$$\operatorname{MutuallySingular}\left(\operatorname{dirac}\left(true\right), \operatorname{dirac}\left(false\right)\right) \land \neg \operatorname{TendstoUnder}\left(\operatorname{dirac}\left(true\right), \operatorname{bottomFiltrationPosterior}\left(\frac{1}{2}\right), 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.filtration_generation_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Singular Boolean Dirac laws with half prior retain posterior one half under the bottom filtration.

## References

- Truth anchor: `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.binaryPosteriorProcess`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.binaryPriorMixture`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.empty_transcript_has_no_probability_law`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.equal_law_is_not_perfectly_separable`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.filtration_generation_is_necessary`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.likelihoodPosterior`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.likelihoodPosteriorProcess`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.mutually_singular_laws_have_collapsing_posterior`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.one_prior_is_necessary`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.trivial_filtration_does_not_generate_bool`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.unit_probability_laws_are_equal`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse.zero_prior_is_necessary`
- Dependency: [D5/S3/Observer/MeasureSeparation/SingularProbabilityPerfectSeparator](SingularProbabilityPerfectSeparator.md)
