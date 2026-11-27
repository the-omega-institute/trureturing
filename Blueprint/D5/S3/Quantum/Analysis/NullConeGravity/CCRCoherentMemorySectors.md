# Coherent Fock shifts and dyadic memory sectors

## Abstract

A coherent phase shift belongs to the countable Fock folium exactly when its mode profile is square-summable. Dyadic memory gives an uncountable family of pairwise disjoint representations.

Satishchandran and Sorce discuss Gaussian-state excitability, and Chandrasekaran uses cyclic representations of null-cone observables. Ashtekar's asymptotic quantization and the gravitational memory representations of Prabhu, Satishchandran and Wald motivate the phase shifts. The representations here use the finite-mode Weyl algebra and the dyadic model of the infrared norm.

**Definition 1.1 (Coherent characteristic function).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.coherentShiftChar`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.coherentShiftChar` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

On a finite mode set F, multiply the vacuum factor exp(−∑|wᵢ|²/2) by the phase exp(2i∑ Im(conj(hᵢ)wᵢ)). Each sum uses only coordinates in F, so the shift profile h may be arbitrary.

**Theorem 1.2 (Coherent vector realization).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.coherentShiftChar_eq_weyl_vacuum_of_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.coherentShiftChar_eq_weyl_vacuum_of_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For a square-summable profile h, synthesize the vector η from its Hilbert basis coordinates. The displacement of the vacuum by η is a unit vector with the specified Weyl coefficient for every finite-mode displacement. Conjugation by the displacement gives the phase with a positive factor of 2 in the exponent.

**Theorem 1.3 (Exact finite Gaussian average).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.coherentShiftChar_gaussian_avg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.coherentShiftChar_gaussian_avg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Multiply the characteristic function by another vacuum factor and integrate with planar Lebesgue measure in each mode. The normalization is π⁻¹ per mode. When hᵢ = a + ib and wᵢ = x + iy, the exponent in that mode is −x² − y² + 2i(ay − bx). Its normalized integral is exp(−a² − b²), so the full integral is ∏ exp(−|hᵢ|²), including the empty product.

**Definition 1.4 (Countable Fock folium).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.CoherentShiftInFockFolium`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.CoherentShiftInFockFolium` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

A countable family of Fock vectors has total squared norm one and its summed vector coefficients reproduce the coherent characteristic function on every finite mode set.

**Theorem 1.5 (Exact square-summability criterion).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.coherentShift_in_fock_folium_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.coherentShift_in_fock_folium_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Finite occupation coordinates capture a positive amount of the total squared norm. On mode sets outside their combined support, the finite-mode vacuum projection retains at least that amount. Gaussian averaging equates this projection mass with exp(−∑|hᵢ|²), so taking logarithms bounds the finite squared-norm sums. For the converse, the single coherent vector realizes the folium.

**Theorem 1.6 (Nonsummable shifts lie outside the Fock folium).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.coherentShift_not_in_fock_folium_of_not_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.coherentShift_not_in_fock_folium_of_not_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

A profile whose squared coordinates are nonsummable admits no countable Fock folium representation.

**Definition 1.7 (Finite-support displacement).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.finiteModeDisplacement`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.finiteModeDisplacement` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Extend the complex tuple by zero outside the indicated finite set.

**Definition 1.8 (Hilbert-basis synthesis).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.finiteModeSynthesis`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.finiteModeSynthesis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Sum the Hilbert basis vectors weighted by the finitely supported complex coordinates.

**Definition 1.9 (Phase-shifted Fock representation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Multiply the Fock Weyl operator of a finitely supported displacement by the character exp(2i∑ Im(conj(hᵢ)wᵢ)). The phase has modulus one for every profile h.

**Definition 1.10 (Representation of the common C-star algebra).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockCStarRep`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockCStarRep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For each displacement, the shifted operators form a norm-bounded family over all profiles. These families generate a norm-closed star algebra. Evaluating at h gives the unital star algebra representation on the occupation Fock space.

**Theorem 1.11 (Weyl product relation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The shift character is multiplicative under addition of displacements. The original Weyl multiplier therefore governs the product of the shifted operators.

**Theorem 1.12 (Zero displacement).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The phase at zero is one and the zero Weyl displacement is the identity operator.

**Theorem 1.13 (Adjoint of a shifted Weyl operator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Taking the adjoint negates the displacement. The Weyl relation and the zero-displacement identity then give unitarity.

**Theorem 1.14 (Vacuum coefficient of the shifted representation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_vacuum_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_vacuum_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The normalized Fock vacuum gives the coherent characteristic function at every finite-mode displacement.

**Theorem 1.15 (Scalar commutant).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_scalar_commutant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_scalar_commutant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Divide out the nonzero scalar phases. Strong continuity then extends commutation from finite displacements to all one-particle vectors, so every commutant operator is scalar.

**Theorem 1.16 (Cyclicity of the Fock vacuum).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_cyclic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_cyclic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Finite-mode displacements of the vacuum are nonzero multiples of coherent exponential vectors. Density of the finite-mode one-particle space and totality of the exponential vectors give a dense orbit span.

**Theorem 1.17 (Strict disjointness of concrete shifts).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_disjoint_of_diff_not_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_disjoint_of_diff_not_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For profiles with a nonsummable squared difference, every bounded intertwiner between their phase-shifted Fock representations vanishes. A nonzero intertwiner would give a unitary equivalence and hence a Fock vector for the relative shift, contrary to the square-summability criterion.

**Theorem 1.18 (Strict disjointness of cyclic Weyl representations).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.coherentShift_gns_disjoint_of_diff_not_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.coherentShift_gns_disjoint_of_diff_not_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Use a common Weyl system on finitely supported displacements with symplectic form twice the imaginary part of the one-particle inner product. Cyclic realizations of the two coherent characteristics have zero bounded intertwiners when the profile difference has nonsummable squared norm. Products of generators determine the inner products between Weyl translates and identify each cyclic representation with its concrete Fock model.

**Definition 1.19 (Dyadic memory representation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.memorySectorRep`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.memorySectorRep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Evaluate the common algebra generator for the given finite displacement in the representation with natural-number modes and constant shift coordinate m√(log 2).

**Theorem 1.20 (Uncountably many disjoint memory sectors).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.uncountable_pairwise_disjoint_memory_sectors`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.uncountable_pairwise_disjoint_memory_sectors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For distinct real memory parameters, every bounded operator intertwining the representations on all finite tuples is zero. The real parameterization is injective and its range is uncountable.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.CoherentShiftInFockFolium`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.coherentShiftChar`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.coherentShiftChar_eq_weyl_vacuum_of_summable`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.coherentShiftChar_gaussian_avg`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.coherentShift_gns_disjoint_of_diff_not_summable`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.coherentShift_in_fock_folium_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.coherentShift_not_in_fock_folium_of_not_summable`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.finiteModeDisplacement`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.finiteModeSynthesis`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.memorySectorRep`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockCStarRep`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_adjoint`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_cyclic`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_disjoint_of_diff_not_summable`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_mul`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_scalar_commutant`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_vacuum_inner`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.shiftedFockRep_zero`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.uncountable_pairwise_disjoint_memory_sectors`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRFockFactorDisjointness](CCRFockFactorDisjointness.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D](NullMemoryBMS4D.md)
