# Unitary Weyl displacements in bosonic Fock space

## Abstract

Strongly continuous Weyl displacements and their behavior under basis change and occupation splitting.

The coherent Gram identity determines a displacement unitary from its action on coherent vectors. Occupation splitting presents a vector as a square-summable family in the retained modes. This presentation gives the vector families used to describe restrictions of Gaussian states in the excitability problem of Satishchandran and Sorce.

**Definition 1.1 (Weyl displacement unitary).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Translation of the coherent input by z, together with the compensating exponential factor, preserves the coherent Gram matrix. The resulting linear isometry extends from the dense coherent span and maps onto Fock space.

**Theorem 1.2 (Displacement of a coherent vector).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl_exponential`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl_exponential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The unitary W(z) sends the coherent vector of w to exp(−‖z‖²/2 − ⟨z, w⟩) times the coherent vector of z + w.

**Theorem 1.3 (Displacement at zero).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The displacement at zero is the identity isometric equivalence.

**Theorem 1.4 (Weyl multiplication law).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

With antilinear-first inner products, W(z)W(w) equals exp(−i Im⟨z, w⟩) times W(z + w) on every vector. If ⟨kf, kg⟩ = μ(f, g) + iσ(f, g)/2, the phase is exp(−iσ(f, g)/2). An imaginary part of −σ(f, g)/2 gives exp(+iσ(f, g)/2).

**Theorem 1.5 (Inverse displacement).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl_symm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The inverse of W(z) is W(−z), since the inner product of z and −z is real and their sum is zero.

**Theorem 1.6 (Gaussian vacuum expectation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl_vacuum_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl_vacuum_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The vacuum coefficient of W(z) is exp(−‖z‖²/2). The coherent Gram identity gives inner product one between the vacuum and the coherent vector of z.

**Theorem 1.7 (Strong continuity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl_strongContinuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl_strongContinuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For each Fock vector, displacement depends continuously on the one-particle input. The coherent action gives continuity on finite coherent sums, and the isometry bound extends it to all vectors.

**Definition 1.8 (Unitary change of Hilbert basis).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockBasisChange`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockBasisChange` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The common coherent Gram matrix extends the correspondence of coherent vectors in two occupation models of the same one-particle space to a unitary.

**Theorem 1.9 (Coherent vectors under basis change).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockBasisChange_exponential`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockBasisChange_exponential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The basis-change unitary sends each coherent vector in the first occupation model to the coherent vector of the same one-particle input in the second model.

**Theorem 1.10 (Basis independence of Weyl displacement).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockBasisChange_weyl`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockBasisChange_weyl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The basis-change unitary intertwines the two Weyl displacements of the same input. The coherent action gives the intertwining on a dense span.

**Definition 1.11 (Disjoint-sum occupation splitting).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockSumSplit`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockSumSplit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Each occupation on the disjoint sum splits uniquely into a left and a right occupation. Regrouping amplitudes by right occupation is a unitary onto the square-summable families of left Fock vectors.

**Theorem 1.12 (Coordinate of a split vector).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockSumSplit_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockSumSplit_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The left occupation amplitude of the component at a right occupation equals the original amplitude at the combined occupation.

**Definition 1.13 (Left one-particle component).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockOneParticleLeft`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockOneParticleLeft` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Restrict the original Hilbert coordinates to the left indices and reconstruct the resulting vector in the left Hilbert basis.

**Theorem 1.14 (Coordinate of the left component).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockOneParticleLeft_repr`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockOneParticleLeft_repr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Every coordinate in the left basis equals the corresponding left coordinate in the original basis.

**Theorem 1.15 (Coordinatewise Weyl displacement).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockSumSplit_weyl`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockSumSplit_weyl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

When the right coordinates of the displacement input vanish, the split vector's component at each right occupation is displaced by the left Weyl unitary. The left input is reconstructed in the left Hilbert basis from the original left coordinates.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockBasisChange`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockBasisChange_exponential`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockBasisChange_weyl`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockOneParticleLeft`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockOneParticleLeft_repr`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockSumSplit`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockSumSplit_apply`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockSumSplit_weyl`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl_exponential`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl_mul`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl_strongContinuous`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl_symm`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl_vacuum_inner`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl.fockWeyl_zero`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation](CCRFockOccupation.md)
