# The one-mode squeezed vacuum

## Abstract

A one-mode squeezed vacuum in the occupation representation and its Weyl expectation.

This construction supplies the one-mode vectors used in the Gaussian excitability problem of Satishchandran and Sorce. On the real line the coherent vectors become Gaussian packets with the same Gram matrix. Their span is dense because testing at imaginary labels detects the Fourier transform of the Gaussian-weighted orthogonal vector.

**Definition 1.1 (Canonical one-mode basis).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.singleModeBasis`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.singleModeBasis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The basis of the complex one-particle line is indexed by Unit and consists of one.

**Theorem 1.2 (Value of the basis vector).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.singleModeBasis_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.singleModeBasis_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The single basis vector has value one.

**Theorem 1.3 (One-particle coordinate).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.singleModeBasis_repr`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.singleModeBasis_repr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The unique basis coordinate of a complex input is the input itself.

**Definition 1.4 (One-mode squeezed vacuum).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.squeezeVacuum`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.squeezeVacuum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For each real r, pull back the normalized Gaussian of width exp(2r) under the coherent isometry. Its position wavefunction is the vacuum Gaussian dilated by exp(r), with amplitude multiplied by exp(r/2).

**Theorem 1.5 (Zero squeeze).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.squeezeVacuum_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.squeezeVacuum_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

At r = 0 the Gaussian is the image of the Fock vacuum.

**Theorem 1.6 (Unit norm).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.squeezeVacuum_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.squeezeVacuum_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The Gaussian integral of the squared wavefunction equals one for every real r.

**Theorem 1.7 (Overlap with the vacuum).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.squeezeVacuum_vacuum_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.squeezeVacuum_vacuum_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The vacuum overlap is 1/√cosh(r). The average of the two Gaussian widths is exp(r) cosh(r), and the amplitude factor cancels its exp(r) contribution.

**Theorem 1.8 (One-mode Weyl expectation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.squeezeVacuum_weyl_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.squeezeVacuum_weyl_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For z = x + iy the expectation is exp(−(exp(2r) x² + exp(−2r) y²)/2). Coherent pairings identify the displaced Gaussian, and the quadratic Gaussian integral cancels the mixed phase.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.singleModeBasis`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.singleModeBasis_apply`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.singleModeBasis_repr`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.squeezeVacuum`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.squeezeVacuum_norm`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.squeezeVacuum_vacuum_inner`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.squeezeVacuum_weyl_inner`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.squeezeVacuum_zero`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation](CCRFockOccupation.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl](CCRFockWeyl.md)
