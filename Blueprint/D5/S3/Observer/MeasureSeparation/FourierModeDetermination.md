# Fourier-Mode Determination

## Abstract

Finite Fourier data leave regulator measures nonunique; the complete profile is exact.

**Theorem 1.1 (Every finite Fourier table has distinct realizations).**

$$\begin{aligned}\forall S: \operatorname{Finset}\left(\mathbb{Z}\right),\\{}\exists mu: \operatorname{Measure}\left(\operatorname{AddCircle}\left(2 \cdot \pi\right)\right), \exists nu: \operatorname{Measure}\left(\operatorname{AddCircle}\left(2 \cdot \pi\right)\right),\\{}\operatorname{IsProbabilityMeasure}\left(mu\right) \land \operatorname{IsProbabilityMeasure}\left(nu\right) \land mu \neq nu \land\\{}\forall n \in S, \operatorname{fourierMoment}\left(mu, n\right) = \operatorname{fourierMoment}\left(nu, n\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/FourierModeDetermination.finite_fourier_modes_do_not_determine_measure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite mode set, choose a positive integer k beyond every listed absolute frequency. The construction compares normalized circle Haar measure with its density 1 + Re(fourier k)/2 perturbation.

Fourier orthogonality makes the two probability measures agree on every listed mode. Their moments at the unused mode -k differ by one quarter, which proves that the measures themselves are distinct.

The explicit nonnegative density and the unused-mode discrepancy are the constructive escape witness for finite non-clonability.

**Theorem 1.2 (The complete Fourier profile determines the measure).**

$$\begin{aligned}\forall mu: \operatorname{Measure}\left(\operatorname{AddCircle}\left(2 \cdot \pi\right)\right), nu: \operatorname{Measure}\left(\operatorname{AddCircle}\left(2 \cdot \pi\right)\right),\\{}[\operatorname{IsFiniteMeasure}\left(mu\right)], [\operatorname{IsFiniteMeasure}\left(nu\right)],\\{}(\forall n: \mathbb{Z}, \operatorname{fourierMoment}\left(mu, n\right) = \operatorname{fourierMoment}\left(nu, n\right)) \Rightarrow mu = nu.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/FourierModeDetermination.all_fourier_modes_determine_measure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Fourier characters generate a star subalgebra that separates points of the additive circle.

Equality on every character extends by linearity to that algebra. The pinned Mathlib finite-measure extensionality theorem then identifies the two finite regulator measures.

## References

- Truth anchor: `D5/S3/Observer/MeasureSeparation/FourierModeDetermination.all_fourier_modes_determine_measure`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/FourierModeDetermination.finite_fourier_modes_do_not_determine_measure`
