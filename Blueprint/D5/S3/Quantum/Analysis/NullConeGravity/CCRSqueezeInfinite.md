# Square-summable squeezes in Fock space

## Abstract

The norm limit of finite squeeze products and the resulting diagonal Gaussian vector state.

This construction represents the diagonal Gaussian covariance by a unit vector in the reference Fock space, as needed in the Gaussian excitability problem of Satishchandran and Sorce. The finite subsets of any basis index type form the directed set for the norm limit.

**Definition 1.1 (Finite squeeze product).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Use a one-mode squeezed vector at each selected mode and the vacuum at each unselected mode.

**Theorem 1.2 (Finite squeeze amplitudes).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

If an occupation is supported on the selected modes, its amplitude is the product of their one-mode amplitudes. Otherwise its amplitude is zero.

**Theorem 1.3 (Norm of a finite squeeze product).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The occupation sum factors into the one-mode squared norms, all equal to one.

**Theorem 1.4 (Overlap for nested finite sets).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For F contained in G, the overlap is the product of 1/√cosh(r) over G outside F. Modes in F contribute their squared norms.

**Theorem 1.5 (Squared distance for nested finite sets).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze_sub_norm_sq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze_sub_norm_sq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The squared distance is at most one half of the sum of r² over the added modes. The bound cosh(r) ≤ exp(r²/2) controls the overlap, and 1 − t ≤ exp(−t) converts that control into the distance estimate.

**Theorem 1.6 (Cauchy net of finite squeeze products).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze_cauchy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze_cauchy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Square summability controls the tail over added modes. For two finite sets above a common cutoff, apply the nested-set estimate through their union.

**Definition 1.7 (Infinite squeeze vector).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.infiniteSqueeze`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.infiniteSqueeze` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Take the norm limit of the finite squeeze products.

**Theorem 1.8 (Norm convergence of the finite products).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Completeness gives convergence of the finite squeeze products to the infinite squeeze vector.

**Theorem 1.9 (Norm of the infinite squeeze vector).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.infiniteSqueeze_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.infiniteSqueeze_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The norm is one by continuity of the norm along the finite products.

**Theorem 1.10 (Infinite-mode Weyl expectation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.infiniteSqueeze_weyl_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.infiniteSqueeze_weyl_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Project the displacement parameter onto the same finite sets. Its Weyl expectation in each finite product factors into the one-mode expectations. The projected parameters and the finite vectors converge in norm. Strong continuity and the isometry bound give the limit on the Weyl side. On the covariance side, bounded exponential weights dominate the series by the squared Hilbert coordinates.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze_apply`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze_cauchy`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze_inner`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze_norm`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze_sub_norm_sq_le`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.finiteSqueeze_tendsto`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.infiniteSqueeze`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.infiniteSqueeze_norm`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.infiniteSqueeze_weyl_inner`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation](CCRFockOccupation.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl](CCRFockWeyl.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle](CCRSqueezeSingle.md)
