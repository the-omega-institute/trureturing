# Bosonic occupation space and coherent vectors

## Abstract

The occupation model of bosonic Fock space, its coherent Gram formula, and totality on real subspaces.

A Hilbert basis labels the modes of the one-particle space. The occupation model uses square-summable amplitudes indexed by finite configurations of these modes. Coherent vectors supply the cyclic subspaces used in Gaussian representations of the Weyl relations.

**Definition 1.1 (Finite occupations).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.Occupation`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.Occupation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

An occupation is a finitely supported function from the mode index type to the natural numbers.

**Definition 1.2 (Bosonic Fock space).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.BosonFock`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.BosonFock` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Take the complex square-summable families indexed by finite occupations.

**Definition 1.3 (Vacuum vector).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockVacuum`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockVacuum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The amplitude at the zero occupation is one and every other amplitude is zero.

**Definition 1.4 (Coherent exponential vector).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The coherent vector of z has one factor per occupied mode, given by its Hilbert-basis coordinate raised to its occupation number and divided by the square root of that number's factorial.

**Theorem 1.5 (Unit vacuum norm).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockVacuum_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockVacuum_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The single nonzero vacuum amplitude gives norm one.

**Theorem 1.6 (Coherent occupation amplitude).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

At each occupation the amplitude is the product of the indicated factorial-normalized powers. The empty product gives amplitude one at the zero occupation.

**Theorem 1.7 (The coherent vector at zero).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

At zero one-particle input the coherent vector equals the vacuum.

**Theorem 1.8 (Coherent Gram identity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The inner product of the coherent vectors of z and w is exp(⟨z, w⟩) in the antilinear-first convention. On a finite set of modes the sum factors into single-mode exponential series. Absolute summability lets the finite-mode sums converge to the occupation-space inner product.

**Theorem 1.9 (Squared coherent norm).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_norm_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The squared norm of the coherent vector of z is exp(‖z‖²), by the diagonal Gram identity.

**Theorem 1.10 (Norm continuity of coherent vectors).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The Gram identity expresses the squared norm of a difference of coherent vectors as a continuous function of the inputs which vanishes when the inputs agree.

**Theorem 1.11 (Totality of coherent vectors).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_dense_span`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_dense_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The complex linear span of all coherent exponential vectors is dense. Restrict a vanishing coherent pairing to finitely many coordinates and use uniqueness of the scalar power-series coefficients to recover the amplitude at every finite occupation.

**Theorem 1.12 (Totality over a real subspace with dense complex span).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_dense_span_of_dense_real`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_dense_span_of_dense_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

If a real-linear subspace has dense complex span in the one-particle space, its coherent vectors already have dense complex span in Fock space. Pairing with a fixed Fock vector is holomorphic along affine complex lines by locally uniform convergence of finite occupation sums. Every vector in the complex span has the form x + iy with x and y in the real subspace. A pairing that vanishes on that subspace vanishes along the whole line x + cy by the identity theorem. Continuity and coherent totality then force the Fock vector to vanish.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.BosonFock`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.Occupation`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_apply`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_continuous`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_dense_span`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_dense_span_of_dense_real`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_inner`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_norm_sq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockExponential_zero`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockVacuum`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.fockVacuum_norm`
