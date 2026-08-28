# Bare Value Observation Is Nonfaithful

## Abstract

The value-only observation identifies distinct structural completion certificates.

**Theorem 1.1 (The bare value observation is not injective).**

$$\neg \operatorname{Injective}\left(val: ConstCert \to \mathbb{C}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/BareValueObservationNoninjective.bare_value_observation_not_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A ConstCert retains its completion-problem role, complex value, and proof of the corresponding completion equation. The value observation deliberately returns only the complex number.

The Gaussian Fourier certificate uses the repository theorem that the positive self-dual Gaussian has scale pi. The rotation certificate uses the pinned identity exp(pi i) = -1. Their roles are distinct, while both value observations are pi, so the projection is not injective.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/BareValueObservationNoninjective.bare_value_observation_not_injective`
- Dependency: [D5/S3/Fourier/CompletionConstants/GaussianSelfDualPi](../../Fourier/CompletionConstants/GaussianSelfDualPi.md)
