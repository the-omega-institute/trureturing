# Output and State Randomness Separation

## Abstract

Finite Boolean kernels separate randomness in state, interface, and prior.

**Theorem 1.1 (Every Dirac law is degenerate).**

$$\forall A, a: A, \neg\operatorname{NondegenerateLaw}\left(\operatorname{pure}\left(a\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.dirac_law_is_degenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A point mass has singleton support, so it cannot support two distinct values. This fact audits both fixed priors and deterministic rows.

**Theorem 1.2 (A fixed state can have random output).**

$$\exists x: Bool, \mu: \operatorname{PMF}\left(Bool\right), K: Bool \to \operatorname{PMF}\left(Bool\right),\\{}\mu = \operatorname{pure}\left(x\right) \land \operatorname{NondegenerateLaw}\left(K(x)\right) \land \operatorname{NondegenerateLaw}\left(\operatorname{inducedOutputLaw}\left(\mu, K\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.fixed_state_random_output` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state law is the point mass at false, while every row of the interface kernel is the fair Boolean law. The induced output therefore remains nondegenerate.

**Theorem 1.3 (A random state can have deterministic output).**

$$\exists \mu: \operatorname{PMF}\left(Bool\right), K: Bool \to \operatorname{PMF}\left(Bool\right), y: Bool,\\{}\operatorname{NondegenerateLaw}\left(\mu\right) \land {\forall x, K(x) = \operatorname{pure}\left(y\right)} \land \operatorname{inducedOutputLaw}\left(\mu, K\right) = \operatorname{pure}\left(y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.random_state_deterministic_output` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fair Boolean state law is sent by a constant Dirac kernel to false. Thus the state law is nondegenerate while the output law is a point mass.

**Theorem 1.4 (Output and state randomness imply neither direction).**

$$\neg{\forall \mu: \operatorname{PMF}\left(Bool\right), K: Bool \to \operatorname{PMF}\left(Bool\right), \operatorname{NondegenerateLaw}\left(\operatorname{inducedOutputLaw}\left(\mu, K\right)\right) \Rightarrow \operatorname{NondegenerateLaw}\left(\mu\right)} \land\\{}\neg{\forall \mu: \operatorname{PMF}\left(Bool\right), K: Bool \to \operatorname{PMF}\left(Bool\right), \operatorname{NondegenerateLaw}\left(\mu\right) \Rightarrow \operatorname{NondegenerateLaw}\left(\operatorname{inducedOutputLaw}\left(\mu, K\right)\right)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.output_state_randomness_nonimplication` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The preceding two Boolean witnesses refute both universal implications: random output need not come from a random state law, and a random state law need not survive in the output.

**Theorem 1.5 (Three models isolate the three uncertainty sources).**

$${\operatorname{StateUncertainty}\left(M_{state}\right) \land \neg\operatorname{MeasurementNoise}\left(M_{state}\right) \land \neg\operatorname{PriorUncertainty}\left(M_{state}\right)} \land\\{}{\neg\operatorname{StateUncertainty}\left(M_{measurement}\right) \land \operatorname{MeasurementNoise}\left(M_{measurement}\right) \land \neg\operatorname{PriorUncertainty}\left(M_{measurement}\right)} \land\\{}{\neg\operatorname{StateUncertainty}\left(M_{prior}\right) \land \neg\operatorname{MeasurementNoise}\left(M_{prior}\right) \land \operatorname{PriorUncertainty}\left(M_{prior}\right)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.single_source_models_isolate_uncertainties` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One model has only a random state transition, one has only measurement noise, and one has only a nondegenerate initial prior. All other rows in each model are explicit Dirac laws.

**Theorem 1.6 (The three isolated sources have one observable law).**

$$\operatorname{observableLaw}\left(M_{state}\right) = \operatorname{uniform}\left(Bool\right) \land\\{}\operatorname{observableLaw}\left(M_{measurement}\right) = \operatorname{uniform}\left(Bool\right) \land\\{}\operatorname{observableLaw}\left(M_{prior}\right) = \operatorname{uniform}\left(Bool\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.single_source_models_observationally_equal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each single-source model induces the fair Boolean observation law. The same observable distribution therefore admits three distinct source placements in this finite construction.

**Theorem 1.7 (The three uncertainty sources are pairwise nonimplicative).**

$$\neg{\forall M, StateUncertainty(M) \Rightarrow MeasurementNoise(M)} \land \neg{\forall M, MeasurementNoise(M) \Rightarrow StateUncertainty(M)} \land\\{}\neg{\forall M, StateUncertainty(M) \Rightarrow PriorUncertainty(M)} \land \neg{\forall M, PriorUncertainty(M) \Rightarrow StateUncertainty(M)} \land\\{}\neg{\forall M, MeasurementNoise(M) \Rightarrow PriorUncertainty(M)} \land \neg{\forall M, PriorUncertainty(M) \Rightarrow MeasurementNoise(M)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.uncertainty_sources_pairwise_do_not_imply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three single-source witnesses refute all six directed implications between state-transition uncertainty, measurement noise, and prior uncertainty.

**Theorem 1.8 (The empty carrier has no probability law).**

$$\neg\operatorname{Nonempty}\left(\operatorname{PMF}\left(Empty\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.empty_type_has_no_probability_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A PMF on Empty would have total mass both zero and one. Hence an empty state carrier cannot supply the prior required by these models.

**Theorem 1.9 (A singleton state is fixed but its output can be random).**

$${\forall \mu: \operatorname{PMF}\left(PUnit\right), \neg\operatorname{NondegenerateLaw}\left(\mu\right)} \land\\{}\exists K: PUnit \to \operatorname{PMF}\left(Bool\right), \operatorname{NondegenerateLaw}\left(K(unit)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.singleton_state_can_still_have_random_output` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every PMF on PUnit is degenerate because no two states differ, yet a kernel row on that sole state can be the fair Boolean law.

**Theorem 1.10 (A deterministic kernel row cannot be random).**

$$\forall X, Y, x: X, f: X \to Y,\\{}\neg\operatorname{NondegenerateLaw}\left(\operatorname{pure}\left(f(x)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.deterministic_kernel_cannot_witness_random_output` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating a deterministic kernel at any fixed state gives a Dirac law. Consequently the fixed-state random-output witness requires a genuinely stochastic interface row.

**Theorem 1.11 (Zero uncertainty gives a deterministic observation).**

$$\forall i: Bool, f: Bool \to Bool, g: Bool \to Bool,\\{}\operatorname{observableLaw}\left(\operatorname{deterministicModel}\left(i, f, g\right)\right) = \operatorname{pure}\left(g(f(i))\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.zero_uncertainty_observation_is_deterministic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With a Dirac prior and Dirac state and measurement kernels, binding the three stages yields the point mass at the composed deterministic output.

**Theorem 1.12 (FPOD principle 202.1).**

$$\neg{\forall \mu: \operatorname{PMF}\left(Bool\right), K: Bool \to \operatorname{PMF}\left(Bool\right), \operatorname{NondegenerateLaw}\left(\operatorname{inducedOutputLaw}\left(\mu, K\right)\right) \Rightarrow \operatorname{NondegenerateLaw}\left(\mu\right)} \land\\{}\neg{\forall \mu: \operatorname{PMF}\left(Bool\right), K: Bool \to \operatorname{PMF}\left(Bool\right), \operatorname{NondegenerateLaw}\left(\mu\right) \Rightarrow \operatorname{NondegenerateLaw}\left(\operatorname{inducedOutputLaw}\left(\mu, K\right)\right)} \land\\{}{\operatorname{StateUncertainty}\left(M_{state}\right) \land \neg\operatorname{MeasurementNoise}\left(M_{state}\right) \land \neg\operatorname{PriorUncertainty}\left(M_{state}\right)} \land\\{}{\neg\operatorname{StateUncertainty}\left(M_{measurement}\right) \land \operatorname{MeasurementNoise}\left(M_{measurement}\right) \land \neg\operatorname{PriorUncertainty}\left(M_{measurement}\right)} \land\\{}{\neg\operatorname{StateUncertainty}\left(M_{prior}\right) \land \neg\operatorname{MeasurementNoise}\left(M_{prior}\right) \land \operatorname{PriorUncertainty}\left(M_{prior}\right)} \land\\{}\neg{\forall M, StateUncertainty(M) \Rightarrow MeasurementNoise(M)} \land \neg{\forall M, MeasurementNoise(M) \Rightarrow StateUncertainty(M)} \land\\{}\neg{\forall M, StateUncertainty(M) \Rightarrow PriorUncertainty(M)} \land \neg{\forall M, PriorUncertainty(M) \Rightarrow StateUncertainty(M)} \land\\{}\neg{\forall M, MeasurementNoise(M) \Rightarrow PriorUncertainty(M)} \land \neg{\forall M, PriorUncertainty(M) \Rightarrow MeasurementNoise(M)} \land\\{}\operatorname{observableLaw}\left(M_{state}\right) = \operatorname{uniform}\left(Bool\right) \land\\{}\operatorname{observableLaw}\left(M_{measurement}\right) = \operatorname{uniform}\left(Bool\right) \land\\{}\operatorname{observableLaw}\left(M_{prior}\right) = \operatorname{uniform}\left(Bool\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.fpod_principle_202_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bidirectional output-state separation, all six source nonimplications, the exact one-source audits, and their common observable law hold together in the explicit Boolean models.

## References

- Truth anchor: `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.deterministic_kernel_cannot_witness_random_output`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.dirac_law_is_degenerate`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.empty_type_has_no_probability_law`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.fixed_state_random_output`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.fpod_principle_202_1`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.output_state_randomness_nonimplication`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.random_state_deterministic_output`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.single_source_models_isolate_uncertainties`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.single_source_models_observationally_equal`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.singleton_state_can_still_have_random_output`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.uncertainty_sources_pairwise_do_not_imply`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation.zero_uncertainty_observation_is_deterministic`
