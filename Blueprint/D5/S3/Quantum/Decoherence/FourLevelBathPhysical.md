# Pinching by a fixed four-level Gibbs bath

## Abstract

A fixed nondegenerate Gibbs bath realizes qutrit pinching exactly when its weighted phase columns are orthonormal.

The qutrit has zero Hamiltonian. Fix four distinct bath energies E and a finite real inverse temperature β, and let p be the resulting Gibbs law. The joint Hamiltonian is I ⊗ diag(E). The input is the qutrit state tensored with diag(p), and the reduced channel traces out the bath after an exactly energy-conserving unitary. This is the finite-bath model of vom Ende, Eq. (1) in Section II.

**Theorem 1.1 (Fixed-bath phase criterion).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathPhysical.fixed_bath_pinching_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathPhysical.fixed_bath_pinching_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2022). *Which bath Hamiltonians matter for thermal operations?*. DOI: [10.1063/5.0117534](https://doi.org/10.1063/5.0117534). URL: <https://arxiv.org/abs/2207.11189v4>.

*Commentary.*

For these same E and β, one unitary pinches every qutrit density state exactly if there are unit phases z(b,i) for which W[b,i] = √p(b) z(b,i) and WᴴW = I₃. Distinct energies give one qutrit block per bath level. Fixing the basis projectors and strict positivity of p force each block to be diagonal. A coherent density with every entry 1/3 then determines the off-diagonal Gram entries. In the reduced matrix map, the multiplier of Xᵢⱼ is (WᴴW)ⱼᵢ.

**Theorem 1.2 (Pinching on all matrices).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathPhysical.phase_implements_pinching`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathPhysical.phase_implements_pinching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2022). *Which bath Hamiltonians matter for thermal operations?*. DOI: [10.1063/5.0117534](https://doi.org/10.1063/5.0117534). URL: <https://arxiv.org/abs/2207.11189v4>.

*Commentary.*

The diagonal phase construction gives coordinate pinching on every complex qutrit matrix under the weighted Gram condition.

**Theorem 1.3 (The bath marginal returns).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathPhysical.bath_return`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathPhysical.bath_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2022). *Which bath Hamiltonians matter for thermal operations?*. DOI: [10.1063/5.0117534](https://doi.org/10.1063/5.0117534). URL: <https://arxiv.org/abs/2207.11189v4>.

*Commentary.*

For any energy-conserving unitary at the fixed injective energy list, any real diagonal bath matrix and any trace-one input matrix, the outgoing bath marginal equals the initial diagonal bath matrix. The joint output can carry correlations.

**Theorem 1.4 (Zero endpoint bath heat).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathPhysical.zero_heat`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathPhysical.zero_heat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2022). *Which bath Hamiltonians matter for thermal operations?*. DOI: [10.1063/5.0117534](https://doi.org/10.1063/5.0117534). URL: <https://arxiv.org/abs/2207.11189v4>.

*Commentary.*

For each density input, the final minus initial bath mean energy is zero. The system Hamiltonian is zero at both endpoints. This energy statement concerns the specified interaction.

**Theorem 1.5 (One unitary realizes the phase witness).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathPhysical.phase_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathPhysical.phase_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2022). *Which bath Hamiltonians matter for thermal operations?*. DOI: [10.1063/5.0117534](https://doi.org/10.1063/5.0117534). URL: <https://arxiv.org/abs/2207.11189v4>.

*Commentary.*

Unit phases with identity Gram give a unitary commuting with the total Hamiltonian, pinching on the matrix algebra, and bath return and zero bath heat on density inputs.

**Theorem 1.6 (Matching a prescribed law).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathPhysical.matching_distinct_energies`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathPhysical.matching_distinct_energies` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2022). *Which bath Hamiltonians matter for thermal operations?*. DOI: [10.1063/5.0117534](https://doi.org/10.1063/5.0117534). URL: <https://arxiv.org/abs/2207.11189v4>.

*Commentary.*

If the bath energies may be chosen, at each β > 0 a positive, normalized, pairwise distinct law p is realized by the injective list E(b) = −log(p(b))/β.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathPhysical.bath_return`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathPhysical.fixed_bath_pinching_iff`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathPhysical.matching_distinct_energies`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathPhysical.phase_implements_pinching`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathPhysical.phase_realization`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathPhysical.zero_heat`
- Dependency: [D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics](ProjectedUnistochasticDynamics.md)
- Dependency: [D5/S3/Quantum/FixedAlgebra/SingletonRecordClassicality](../FixedAlgebra/SingletonRecordClassicality.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/QuantumChannels/ThermalOperationDegeneracyRefutation](../../QuantumChannels/ThermalOperationDegeneracyRefutation.md)
