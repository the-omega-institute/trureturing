# The regulated bulk two-point function

## Abstract

Regulated bulk mass-shell integrals and scaling in four spacetime dimensions.

The characteristic covariance problem of Satishchandran and Sorce uses the difference of massive and massless scalar two-point functions. The bulk momentum integral gives this difference throughout the right half-plane of complex time.

**Definition 1.1 (Momentum energy).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.energy`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.energy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For real M and momentum k in three-dimensional Euclidean space, the energy is the nonnegative square root of ‖k‖² + M².

**Definition 1.2 (Mass-shell density).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.shellWeight`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.shellWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The density relative to Lebesgue momentum measure is the reciprocal of 2(2π)³ times the energy. The massless density takes value zero at zero momentum.

**Definition 1.3 (Regulated bulk integral).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.bulkU`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.bulkU` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For real mass M, complex time τ and spatial separation r, integrate the shell density against exp(−τ times the energy plus i times the Euclidean inner product of k and r).

**Theorem 1.4 (Momentum integrability).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.bulkU_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.bulkU_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every real mass and every spatial separation, the momentum integrand is integrable when the real part of τ is positive. The energy is at least ‖k‖. Away from k = 0 this bounds the integrand by a constant times exp(−Re(τ)‖k‖)/‖k‖. The radial volume factor is ‖k‖².

**Theorem 1.5 (Holomorphy in time).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.bulkU_differentiableOn`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.bulkU_differentiableOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For fixed real mass and spatial separation, the integral is complex differentiable on the right half-plane. Differentiation inserts a factor of minus the energy, so a positive local lower bound on the real part of τ gives an integrable exponential bound.

**Theorem 1.6 (Massless bulk formula).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.bulkU_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.bulkU_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every spatial separation r and complex time τ with positive real part, put q = ‖r‖² + τ². The massless bulk integral equals the reciprocal of 4π² times q.

**Theorem 1.7 (Massive minus massless).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.bulkU_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.bulkU_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For M > 0 and complex time τ with positive real part, the difference of the mass M and massless bulk integrals is the bulk correction evaluated at M and q = ‖r‖² + τ². At positive real time, Gaussian subordination and the momentum Fourier integral give H(M²q/4)/(4π²q). The Schwinger series identifies its difference from the massless value with the stated correction. Holomorphic continuation extends the formula throughout the right half-plane, where q lies in the slit plane.

**Theorem 1.8 (Joint scaling of time and separation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.bulkU_scale`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.bulkU_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For nonnegative mass m, positive L and complex time τ with positive real part, the mass m integral at (Lτ, Lr) equals L⁻² times the mass mL integral at (τ, r). Under k ↦ k/L, three-dimensional volume supplies L⁻³ and the shell density supplies L.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.bulkU`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.bulkU_difference`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.bulkU_differentiableOn`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.bulkU_integrable`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.bulkU_scale`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.bulkU_zero`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.energy`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.shellWeight`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSchwinger4D](NullDiamondSchwinger4D.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D](NullDiamondSphere4D.md)
