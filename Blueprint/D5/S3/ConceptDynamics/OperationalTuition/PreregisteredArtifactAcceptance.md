# Preregistered Artifact Acceptance

## Abstract

A missing routing envelope permits independent artifact acceptance exactly when a fixed criterion was recorded before production, and that witness survives seat death.

**Theorem 1.1 (Missing-envelope acceptance is preregistered and inheritable).**

$$\begin{aligned}\forall C, B: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(C\right)], [\operatorname{DecidableEq}\left(B\right)],\\v: C \Rightarrow \operatorname{ToyState}\left(B\right) \Rightarrow Bool,\\d: \operatorname{DeliveryRecord}\left(C, B\right),\\(\operatorname{missingEnvelopeAcceptance}\left(v, d\right) = true \iff (\operatorname{EnvelopeMissing}\left(d\right) \land \operatorname{Nonempty}\left(\operatorname{PreregisteredAcceptanceWitness}\left(v, d\right)\right))) \land\\{}(\operatorname{Nonempty}\left(\operatorname{PreregisteredAcceptanceWitness}\left(v, d\right)\right) \Rightarrow \operatorname{missingEnvelopeAcceptance}\left(v, \operatorname{inheritAfterSeatDeath}\left(d\right)\right) = true).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/OperationalTuition/PreregisteredArtifactAcceptance.missing_envelope_acceptance_iff_preregistered_and_inheritable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite delivery keeps the optional routing envelope separate from a frozen toy artifact trajectory. The distinguished artifact checkpoint follows the complete finite prefix used by the independent verifier.

The executable judgment scans only that prefix. Its forward direction extracts a concrete registered criterion whose fixed Boolean verifier accepts the computed final artifact state; the reverse direction runs that witness.

Seat death clears the envelope and liveness flag but preserves the artifact and pre-artifact prefix. Consequently the same finite witness establishes postmortem acceptance without trusting a self-reported status.

## References

- Truth anchor: `D5/S3/ConceptDynamics/OperationalTuition/PreregisteredArtifactAcceptance.missing_envelope_acceptance_iff_preregistered_and_inheritable`
- Dependency: [D5/S3/ConceptDynamics/OperationalTuition/ArtifactSufficiencyAndKillLoss](ArtifactSufficiencyAndKillLoss.md)
