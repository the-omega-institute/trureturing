# Coarsest Observation Quotient

## Abstract

The quotient by an observation kernel is the coarsest exact interface, and every accurate surjective readout factors uniquely through it.

**Theorem 1.1 (The canonical observation quotient recovers the observation uniquely).**

$$\begin{gathered}\forall X, O: \operatorname{Type}, observation: X \to O,\\{}\exists! decoder: \operatorname{Quotient}(\operatorname{ker}(observation)) \to O, observation = decoder\left(observationProjection\left(observation\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/CoarsestObservationQuotient.observation_quotient_recovers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient identifies exactly those states with the same observation. The observation therefore descends to a unique decoder on the quotient, and composing that decoder with the canonical projection recovers the original observation.

**Theorem 1.2 (Every accurate surjective readout factors uniquely through the quotient).**

$$\begin{gathered}\forall X, O, Q: \operatorname{Type},\\{}observation: X \to O, readout: X \to Q,\\{}\operatorname{Surjective}(readout), decoder: Q \to O,\\{}observation = decoder\left(readout\right) \Rightarrow\\{}\exists! factor: Q \to \operatorname{Quotient}(\operatorname{ker}(observation)), observationProjection\left(observation\right) = factor\left(readout\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/CoarsestObservationQuotient.accurate_surjective_readout_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a surjective readout can decode the observation, its fibers are contained in observation fibers. A representative from each readout value then defines a map to the canonical quotient, and surjectivity makes that map both total and unique.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Observation/CoarsestObservationQuotient.accurate_surjective_readout_factors`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/CoarsestObservationQuotient.observation_quotient_recovers`
