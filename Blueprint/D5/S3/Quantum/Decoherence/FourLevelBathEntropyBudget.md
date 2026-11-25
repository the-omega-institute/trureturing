# Entropy budgets of the purified four-level Gibbs bath

## Abstract

Exact marginal entropies and information for an arbitrary qutrit coupled to a purified Gibbs bath.

Fix a qutrit S with zero Hamiltonian, a four-level bath B with distinct energies E, and a finite real inverse temperature β. The Gibbs weight p(b) is exp(−βE(b)) divided by the sum of those exponentials over the four bath levels. Prepare B and a four-level reference R coherently in Σᵦ √p(b) |b,b⟩, independently of the input density ρ on S. Act with the phase unitary on SB and the identity on R. Its phases have unit modulus and the p-weighted columns are orthonormal. Energy conservation is imposed on SB with Hamiltonians 0 and E.

The input ρ may be any positive semidefinite trace-one qutrit, including singular and coherent inputs. Write aᵢ = ρᵢᵢ, Δρ for coordinate pinching, H for Shannon entropy and S(·) for von Neumann entropy. Both entropies are in nats and use the zero-weight convention.

**Theorem 1.1 (Information in the actual evolved state).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.gibbs_phase_budgets`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.gibbs_phase_budgets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Acknowledgement.* T. Baumgratz, M. Cramer, M. B. Plenio (2014). *Quantifying Coherence*. URL: <https://arxiv.org/abs/1311.0275v3>.

*Acknowledgement.* David Reeb and Michael M. Wolf (2014). *An improved Landauer principle with finite-size corrections*. DOI: [10.1088/1367-2630/16/10/103011](https://doi.org/10.1088/1367-2630/16/10/103011). URL: <https://arxiv.org/abs/1306.4352v3>.

*Acknowledgement.* Frederik vom Ende (2022). *Which bath Hamiltonians matter for thermal operations?*. DOI: [10.1063/5.0117534](https://doi.org/10.1063/5.0117534). URL: <https://arxiv.org/abs/2207.11189v4>.

*Commentary.*

The same energy-conserving phase interaction gives the budget for every density ρ. The S marginal is Δρ. Both B and R have density diag(p). The SB marginal is the evolved mixed-bath product state, and SR equals SB in the corresponding coordinates. The BR marginal is the orthogonal pure-record mixture with weights a. The S and BR entropies are H(a), the B and R entropies are H(p), the SB and SR entropies are S(ρ) + H(p), and the SBR entropy is S(ρ). The S:BR mutual information equals that of the coherent copy of ρ.

$$
I(S:B) = I(S:R) = H(a) - S(\rho)
$$

$$
I(S:BR) = 2 H(a) - S(\rho),\quad I(S:R\mid B) = H(a)
$$

Baumgratz, Cramer and Plenio identify H(a) − S(ρ) with the relative entropy of coherence in the chosen basis. For the reduced SB evolution, the Reeb–Wolf balance starts from ρ ⊗ diag(p). The returning Gibbs bath has zero mean-energy change and zero relative entropy to its initial state, so the balance gives I(S:B) equal to the system entropy gain.

**Theorem 1.2 (Nonnegative Born weights).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.populations_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.populations_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each coordinate population of a positive semidefinite input density is nonnegative.

**Theorem 1.3 (Normalized Born weights).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.sum_populations`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.sum_populations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The populations sum to one by the trace of the input density.

**Theorem 1.4 (Pinching in the coordinate basis).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.pinching_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.pinching_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pinched input matrix is diagonal with the Born populations on its diagonal.

**Theorem 1.5 (Density of the original bath).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.bathState_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.bathState_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any normalized nonnegative bath law p, the B marginal of the coherent preparation has matrix diag(p).

**Theorem 1.6 (Density of the evolved preparation).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.outputState_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.outputState_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The density-state conjugation of the independent preparation by the lifted joint unitary has the actual purified-output matrix.

**Theorem 1.7 (Entries after tracing out the reference).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.systemBathMarginal_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.systemBathMarginal_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sum the joint matrix entries over the common reference index to obtain each SB entry.

**Theorem 1.8 (Entries after tracing out the bath).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.systemReferenceMarginal_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.systemReferenceMarginal_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sum the joint matrix entries over the common bath index to obtain each SR entry.

**Theorem 1.9 (The coherent copy embedded in the actual record).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.purifiedOutput_isometricCopy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.purifiedOutput_isometricCopy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Acknowledgement.* Ding, Feng; Hu, Xueyuan (2020). *Masking quantum information on hyperdisks*. DOI: [10.1103/PhysRevA.102.042404](https://doi.org/10.1103/PhysRevA.102.042404). URL: <https://arxiv.org/abs/1909.11256v3>.

*Commentary.*

Under the weighted Gram identity, V = I ⊗ recordEmbedding is an isometry. For every qutrit matrix X the actual phase output is V copyMatrix(X) V†. Each off-diagonal input entry remains in the joint state.

**Theorem 1.10 (The SB and SR densities).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.system_marginals`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.system_marginals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative normalized p and a unitary phase interaction, tracing out R gives the mixed-bath evolution and tracing out B gives the same density in the matching coordinates.

**Theorem 1.11 (The Born mixture on BR).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.record_marginal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.record_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the normalized preparation and orthonormal record columns, the BR density is the mixture of the actual pure record densities with probabilities a.

**Theorem 1.12 (The pinched input embedded on BR).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.record_marginal_embedding`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.record_marginal_embedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The BR marginal is the rectangular record isometry applied to Δρ in the original BR coordinates.

**Theorem 1.13 (One interaction for a fixed feasible law).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.gibbs_cubic_budgets`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.gibbs_cubic_budgets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Korzekwa, Kamil; Czachórski, Stanisław; Puchała, Zbigniew; Życzkowski, Karol (2019). *Distinguishing classically indistinguishable states and channels*. DOI: [10.1088/1751-8121/ab30f7](https://doi.org/10.1088/1751-8121/ab30f7). URL: <https://arxiv.org/abs/1812.09083v3>.

*Acknowledgement.* Grzegorz Rajchel; Adam Gąsiorowski; Karol Życzkowski (2018). *Robust Hadamard Matrices, Unistochastic Rays in Birkhoff Polytope and Equi-Entangled Bases in Composite Spaces*. DOI: [10.1007/s11786-018-0384-y](https://doi.org/10.1007/s11786-018-0384-y). URL: <https://arxiv.org/abs/1804.10715v2>.

*Acknowledgement.* Frederik vom Ende (2022). *Which bath Hamiltonians matter for thermal operations?*. DOI: [10.1063/5.0117534](https://doi.org/10.1063/5.0117534). URL: <https://arxiv.org/abs/2207.11189v4>.

*Commentary.*

For the fixed Gibbs law, assume p(b) ≤ 1/3 for each b and a root 0 < t ≤ 1 of the phase cubic with q(p,b)² t ≥ d(p,b)² at every b. There is one phase interaction, chosen before the input, that conserves SB energy, pinches every qutrit matrix in the mixed-bath channel, supplies a basis observation, and realizes the purified budgets for every qutrit density.

For classical readout, measure S after the interaction in the input coordinate basis, keeping its outcome X with law a. Conditional on each label of positive probability, the bath and reference carry the corresponding pure phase record. The joint decoder grants access to B and R and phase-sensitive projectors. The one-way decoder grants a four-point Fourier measurement on R, a classical message carrying its outcome k, and the matching phase-sensitive measurement on B.

**Theorem 1.14 (Information of the measured label).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.basis_label_budgets`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.basis_label_budgets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ding, Feng; Hu, Xueyuan (2020). *Masking quantum information on hyperdisks*. DOI: [10.1103/PhysRevA.102.042404](https://doi.org/10.1103/PhysRevA.102.042404). URL: <https://arxiv.org/abs/1909.11256v3>.

*Acknowledgement.* John Archibald Wheeler (1999). *Information, Physics, Quantum: The Search for Links*. DOI: [10.1201/9780429500459-19](https://doi.org/10.1201/9780429500459-19). URL: <https://cqi.inf.usi.ch/qic/wheeler.pdf>.

*Commentary.*

For any normalized nonnegative bath law with unit-modulus phases and orthonormal weighted columns, the joint record determines X for any Born prior a, including priors with zero weights. Each local label state has zero quantum mutual information.

$$
I(X:B) = I(X:R) = 0,\quad I(X:BR) = H(a)
$$

**Theorem 1.15 (Readout of the phase record).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.basis_readout_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.basis_readout_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ding, Feng; Hu, Xueyuan (2020). *Masking quantum information on hyperdisks*. DOI: [10.1103/PhysRevA.102.042404](https://doi.org/10.1103/PhysRevA.102.042404). URL: <https://arxiv.org/abs/1909.11256v3>.

*Acknowledgement.* John Archibald Wheeler (1999). *Information, Physics, Quantum: The Search for Links*. DOI: [10.1201/9780429500459-19](https://doi.org/10.1201/9780429500459-19). URL: <https://cqi.inf.usi.ch/qic/wheeler.pdf>.

*Commentary.*

For each basis label, both local densities equal diag(p), and a joint coordinate measurement has probability p(b) at (b,b) and zero off those pairs. A joint record projector identifies the label with certainty. Each Fourier outcome k has probability 1/4, and the joint law of k and the bath decoder assigns 1/4 to the matching label and zero to every other answer. Wheeler's apparatus question “Was the label j?” provides historical context.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.basis_label_budgets`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.basis_readout_comparison`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.bathState_matrix`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.gibbs_cubic_budgets`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.gibbs_phase_budgets`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.outputState_matrix`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.pinching_matrix`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.populations_nonneg`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.purifiedOutput_isometricCopy`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.record_marginal`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.record_marginal_embedding`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.sum_populations`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.systemBathMarginal_entry`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.systemReferenceMarginal_entry`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.system_marginals`
- Dependency: [D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier](FourLevelBathObserverFourier.md)
- Dependency: [D5/S3/Quantum/Decoherence/LabelResetSupport](LabelResetSupport.md)
- Dependency: [D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity](../Information/CorrelatedGibbsEnergyIdentity.md)
- Dependency: [D5/S3/Quantum/Information/StrongSubadditivity](../Information/StrongSubadditivity.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy](../Measurement/Auric/CoordinatePinchingEntropy.md)
