# Identifiability, Estimability, and Computation

## Abstract

Exact-law semantics, finite-sample guarantees, algorithms, and resource bounds are registered separately and separated by concrete witnesses.

**Definition 1.1 (Identifiability is evidence-kernel containment).**

Lean statement: `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.Identifiable`

*Formalization.* `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.Identifiable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Definition 281.1 is represented literally by containment of the canonical Setoid.ker of the evidence interface in the target kernel. It is an infinite-precision law-level predicate.

**Definition 1.2 (Estimability uses a positive finite sample).**

Lean statement: `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.Estimable`

*Formalization.* `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.Estimable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Definition 281.2 is deliberately narrowed to one faithful disjunct: there is a positive finite sample size and an estimator that is almost surely exact for every model. Under zero-one loss this is a zero-risk guarantee, stronger than merely finite risk.

**Definition 1.3 (Computability combines correctness and a resource bound).**

Lean statement: `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.Computable`

*Formalization.* `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.Computable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Definition 281.3 is narrowed to exact evaluation by a registered algorithm together with a uniform bound in a supplied natural-valued cost model. It does not claim a Mathlib complexity class.

**Theorem 1.4 (Identifiability does not imply finite-sample accuracy).**

$$\operatorname{Identifiable}\left(stateLaw, id\right) \land\\\neg \operatorname{Estimable}\left(finiteTranscript, id\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.identifiable_not_finite_sample_accurate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported Bernoulli product-law witness separates the two Boolean states by a complete-transcript event of probabilities zero and one. Every finite prefix retains an overlapping positive-mass all-false cylinder, so no finite decoder is almost surely exact.

**Theorem 1.5 (Finite-sample accuracy does not imply tractability).**

$$\operatorname{Estimable}\left(deterministicBoolLaw, id\right) \land\\\neg \operatorname{Computable}\left(id, id, 1\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.finite_sample_accurate_not_computable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A noiseless Boolean observation is exactly estimable at sample size one. The same correct identity evaluator is charged cost two by the explicit model, exceeding the positive acceptable budget one.

**Theorem 1.6 (A subclass algorithm does not prove global identifiability).**

$$\operatorname{IdentificationFormula}\left(parametricSubclass, parametricAlgorithm\right) \land\\\operatorname{Computable}\left(parametricAlgorithm, 1\right) \land\\\neg \operatorname{Identifiable}\left(nonparametricEvidence, nonparametricTarget\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.parametric_algorithm_not_nonparametric_identifiable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two-point subclass consisting of some false and some true is decoded exactly within budget. On the full Option Bool class, none and some false have equal evidence but different targets.

**Theorem 1.7 (The semantic layer does not certify a registered formula).**

$$\operatorname{Identifiable}\left(id, id\right) \land\\\neg \operatorname{IdentificationFormula}\left(id, id, not\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.semantic_kernel_does_not_certify_candidate_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identity evidence identifies the identity target, but this semantic fact does not certify the independently registered Boolean negation formula. This records the first adjacent layer boundary.

**Theorem 1.8 (An identification formula does not replace sampling).**

$$\operatorname{IdentificationFormula}\left(stateLaw, id, lawClassifier\right) \land\\\neg \operatorname{Estimable}\left(finiteTranscript, id\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.identification_formula_does_not_replace_sampling_theorem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating the probability-one distinguishing event gives an exact formula on complete laws. The same product-law model still has no almost-surely exact finite-prefix estimator.

**Theorem 1.9 (A sampling theorem does not certify a candidate algorithm).**

$$\operatorname{FiniteSampleAccurateAt}\left(deterministicBoolLaw, 1, id\right) \land\\\neg \operatorname{AlgorithmImplements}\left(id, not\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.sampling_theorem_does_not_certify_candidate_algorithm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The one-sample identity estimator is almost surely exact in the noiseless Boolean model. That theorem does not make the separately registered Boolean-negation algorithm implement identity.

**Theorem 1.10 (An algorithm does not replace a complexity bound).**

$$\operatorname{AlgorithmImplements}\left(id, id\right) \land\\\neg \operatorname{ComplexityBound}\left(2, id, 1\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.algorithm_does_not_replace_complexity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identity implements the identity specification pointwise. A separate cost calculation still exceeds budget one, so correctness alone does not register the fifth layer.

The Lean degeneracy audit also checks equal kernels, constant maps, an empty carrier, a singleton model, a finite Boolean model, and sample size zero. No prime-specific fact is load-bearing.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.Computable`
- Truth anchor: `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.Estimable`
- Truth anchor: `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.Identifiable`
- Truth anchor: `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.algorithm_does_not_replace_complexity_bound`
- Truth anchor: `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.finite_sample_accurate_not_computable`
- Truth anchor: `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.identifiable_not_finite_sample_accurate`
- Truth anchor: `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.identification_formula_does_not_replace_sampling_theorem`
- Truth anchor: `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.parametric_algorithm_not_nonparametric_identifiable`
- Truth anchor: `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.sampling_theorem_does_not_certify_candidate_algorithm`
- Truth anchor: `D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation.semantic_kernel_does_not_certify_candidate_formula`
- Dependency: [D5/S3/ConceptDynamics/Experiment/InfiniteIdentificationFiniteInexactness](../Experiment/InfiniteIdentificationFiniteInexactness.md)
