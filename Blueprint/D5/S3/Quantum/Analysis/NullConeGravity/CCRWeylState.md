# Weyl systems and state transport

## Abstract

Weyl generators, Gaussian characteristic functions, and the countable vector-state folium of a GNS representation.

An alternating real bilinear form fixes the Weyl phase. The linear span of the generators is norm dense in the common C-star algebra. A positive normalized functional has a canonical cyclic vector in its GNS completion. Countable mixtures of vector states in this completion express excitability.

**Definition 1.1 (Weyl system).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.WeylSystem`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.WeylSystem` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The zero datum is sent to the algebra identity. The generators satisfy the phase-twisted addition law and the adjoint law, and have norm-dense complex linear span. The real bilinear form is alternating.

**Definition 1.2 (Gaussian state).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.IsGaussian`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.IsGaussian` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The functional is normalized at the identity and takes each Weyl generator to the exponential of minus one half of the covariance quadratic form.

**Definition 1.3 (Excitability).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.Excitability`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.Excitability` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

There exists a sequence of vectors in the reference GNS space whose squared norms sum to one and whose vector expectations sum to the target functional at every algebra element.

**Definition 1.4 (Canonical GNS vector).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.gnsVacuum`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.gnsVacuum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The vector represented by the algebra identity in the GNS completion.

**Theorem 1.5 (Unitarity of the Weyl operators).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.weyl_unitary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.weyl_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Multiplying a generator by its adjoint in either order gives the identity. Alternation makes the phase for opposite labels equal to one.

**Theorem 1.6 (Weyl norm bound).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.weyl_norm_le_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.weyl_norm_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Each generator has norm at most one by the C-star identity and the unitary product law.

**Theorem 1.7 (Weyl inversion).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.weyl_neg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.weyl_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The generator indexed by the negative datum equals the adjoint of the original generator.

**Theorem 1.8 (Unit GNS vacuum).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.gnsVacuum_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.gnsVacuum_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For a positive functional normalized at the identity the canonical GNS vector has norm one.

**Theorem 1.9 (GNS vacuum expectation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.gnsVacuum_expectation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.gnsVacuum_expectation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The expectation of the represented algebra element in the canonical GNS vector is the original positive functional evaluated at that element.

**Theorem 1.10 (Contractive state evaluation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.state_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.state_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For a normalized positive functional, the absolute value at any algebra element is bounded by the element's norm. Cauchy–Schwarz and contractivity of the GNS representation give the bound.

**Theorem 1.11 (State continuity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.state_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.state_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The normalized positive functional is continuous in the C-star norm.

**Theorem 1.12 (Determination by Weyl coefficients).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.weyl_determines`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.weyl_determines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Two continuous complex linear functionals agreeing at each generator agree on the entire algebra, by linearity and density.

**Theorem 1.13 (Uniqueness of Gaussian states).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.gaussian_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.gaussian_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Two Gaussian states on the same Weyl system with the same covariance are equal because their characteristic functions agree.

**Theorem 1.14 (Summable vector expectations).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.folium_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.folium_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

When the squared norms of the sequence sum to one, the vector expectations of each algebra element form a summable complex series.

**Theorem 1.15 (Norm bound for the folium series).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.folium_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.folium_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The absolute value of the series at each algebra element is bounded by the norm of that element.

**Definition 1.16 (Continuous folium functional).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.foliumFunctional`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.foliumFunctional` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

A sequence with total squared norm one defines the continuous complex linear functional obtained by summing its vector expectations.

**Theorem 1.17 (Excitability from Weyl coefficients).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.excitability_of_weyl_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.excitability_of_weyl_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

If the vector expectation series equals the target state at every Weyl generator, its continuous linear extension agrees with the target everywhere. The sequence therefore witnesses excitability.

**Theorem 1.18 (Unitary transfer of vector decompositions).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.excitability_of_unitary_intertwining`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.excitability_of_unitary_intertwining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

A complex linear isometric equivalence intertwining the generator actions transports a sequence of vectors in the representation space back to the reference GNS space. Norms and generator expectations are preserved, giving excitability when the coefficients match.

**Theorem 1.19 (Reflexive excitability).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.excitability_refl`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.excitability_refl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For a normalized state, the sequence concentrated at the canonical GNS vector has total squared norm one and recovers the state at every algebra element.

**Theorem 1.20 (Pullback of excitability).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.excitability_pullback`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.excitability_pullback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

A surjective unital star-algebra homomorphism identifies the pulled-back reference GNS completion isometrically with the original completion. Pulling back its vector witnesses gives excitability of the composed positive functionals.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.Excitability`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.IsGaussian`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.WeylSystem`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.excitability_of_unitary_intertwining`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.excitability_of_weyl_coefficients`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.excitability_pullback`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.excitability_refl`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.foliumFunctional`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.folium_norm_le`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.folium_summable`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.gaussian_unique`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.gnsVacuum`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.gnsVacuum_expectation`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.gnsVacuum_norm`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.state_continuous`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.state_norm_le`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.weyl_determines`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.weyl_neg`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.weyl_norm_le_one`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.weyl_unitary`
- Dependency: [D5/S3/QuantumStates/GNSExpectation](../../../QuantumStates/GNSExpectation.md)
