# Bondi flux and the infrared memory spectrum

## Abstract

The sphere-averaged Bondi flux gives an exact mass balance. The angular memory spectrum has four translation modes, and a nonzero zero-frequency value forces a logarithmic infrared divergence.

The setting uses the round celestial sphere and a complex news profile. Satishchandran and Sorce give the characteristic graviton reference, and Chandrasekaran studies radiative gravitational data on intersecting null cones. The normalized Bondi mass equation is imposed on the profile. The angular part of the Christodoulou memory model is specified by its harmonic eigenvalues.

**Definition 1.1 (Sphere-averaged news flux).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondiFlux`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondiFlux` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Integrate the squared complex norm of the news on the round sphere and divide by its area 4π.

**Theorem 1.2 (Nonnegative news flux).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondiFlux_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondiFlux_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The squared norm is pointwise nonnegative and the area normalization is positive.

**Theorem 1.3 (Zero flux for continuous news).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondiFlux_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondiFlux_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For continuous news the flux vanishes exactly when the profile vanishes everywhere. A nonzero value would remain bounded away from zero on an open set of positive round measure.

**Theorem 1.4 (Bondi mass monotonicity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondi_mass_loss_nonpos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondi_mass_loss_nonpos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

A mass with derivative equal to minus the news flux at each time is antitone.

**Theorem 1.5 (Integrated mass balance).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondi_energy_balance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondi_energy_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For a continuously differentiable mass obeying the mass equation, the mass at a minus the mass at b equals the oriented integral of the news flux from a to b.

**Theorem 1.6 (Nonnegative radiated energy).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondi_energy_radiated_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondi_energy_radiated_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For a ≤ b the integral of the news flux from a to b is nonnegative.

**Theorem 1.7 (Strict mass decrease).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondi_strict_mass_loss_of_nonzero_news`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondi_strict_mass_loss_of_nonzero_news` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Suppose the mass equation holds and the news is jointly continuous. If it is nonzero as an angular profile at an interior time between a and b, then the mass at b is strictly less than at a. The flux stays positive on an interval around that time.

**Definition 1.8 (Memory elliptic eigenvalue).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.memoryEllipticEigenvalue`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.memoryEllipticEigenvalue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

In degree ℓ the eigenvalue of the spherical harmonic model for D²(D² + 2) is ℓ(ℓ + 1)(ℓ − 1)(ℓ + 2).

**Theorem 1.9 (Translation kernel).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.memoryElliptic_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.memoryElliptic_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The eigenvalue vanishes exactly in degrees zero and one.

**Theorem 1.10 (Positive supertranslation modes).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.memoryElliptic_pos_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.memoryElliptic_pos_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The eigenvalue is positive exactly in degrees at least two.

**Theorem 1.11 (Translation multiplicity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.poincare_translation_dim_eq_four`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.poincare_translation_dim_eq_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The four-dimensional harmonic multiplicity is 2ℓ + 1. The two kernel degrees therefore have total multiplicity 1 + 3 = 4.

**Theorem 1.12 (Square-summable inverse eigenvalues).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.memoryGreenSq_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.memoryGreenSq_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Starting at degree two, the multiplicity divided by the squared eigenvalue is summable. The eigenvalue is at least ℓ⁴/2 and the multiplicity is at most 3ℓ, giving the summable bound 12/ℓ⁷. This is the Hilbert–Schmidt sum for the diagonal inverse.

**Definition 1.13 (Frequency-space density).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.irDensity`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.irDensity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

At positive frequency ω use the squared complex norm of the profile divided by ω.

**Theorem 1.14 (Infrared divergence at nonzero memory).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.nonzero_memory_ir_diverges`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.nonzero_memory_ir_diverges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For a continuous profile with nonzero value at zero and any positive upper cutoff Λ, there are a positive constant a and 0 < δ ≤ Λ such that the integral from ε to Λ is at least a log(δ/ε) when 0 < ε < δ. Continuity gives a positive lower bound on the squared norm near zero. The cutoff integrals tend to positive infinity as ε decreases to zero, and the density is nonintegrable on (0, Λ).

**Theorem 1.15 (Hölder vanishing makes the density integrable).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.zero_memory_ir_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.zero_memory_ir_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For a profile continuous on [0, Λ] with Λ > 0, a bound by Cωᵅ in norm on (0, Λ), with α > 0, gives an integrable majorant C²ω^(2α − 1).

**Theorem 1.16 (Exact dyadic weight).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.dyadic_memory_bin_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.dyadic_memory_bin_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The integral of the reciprocal frequency from 2^(−k−1) to 2^(−k) is log 2 for each natural-number k.

**Definition 1.17 (Dyadic memory profile).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.dyadicMemoryProfile`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.dyadicMemoryProfile` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Assign the same coefficient m√(log 2) to every dyadic frequency bin for a real parameter m.

**Theorem 1.18 (Nonzero memory has infinite squared norm).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.dyadic_memory_not_summable_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.dyadic_memory_not_summable_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

A nonzero parameter gives the same positive squared norm on every bin and hence a divergent sum.

**Theorem 1.19 (Exact equivalence for two dyadic profiles).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.dyadic_memory_diff_summable_sq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.dyadic_memory_diff_summable_sq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The squared norms of the pointwise difference are summable exactly when the two real parameters agree.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondiFlux`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondiFlux_eq_zero_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondiFlux_nonneg`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondi_energy_balance`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondi_energy_radiated_nonneg`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondi_mass_loss_nonpos`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.bondi_strict_mass_loss_of_nonzero_news`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.dyadicMemoryProfile`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.dyadic_memory_bin_weight`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.dyadic_memory_diff_summable_sq_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.dyadic_memory_not_summable_sq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.irDensity`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.memoryEllipticEigenvalue`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.memoryElliptic_pos_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.memoryElliptic_zero_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.memoryGreenSq_summable`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.nonzero_memory_ir_diverges`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.poincare_translation_dim_eq_four`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D.zero_memory_ir_integrable`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold](NullDiamondDimensionThreshold.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D](NullDiamondSphere4D.md)
