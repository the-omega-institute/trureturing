# Reading the purified bath record

## Abstract

The actual conditional records of a purified Gibbs bath hide a basis label in each margin and reveal it jointly.

Preparation supplies the coherent state Σᵦ √p(b) |b,b⟩ on bath B and reference R, initially independent of the qutrit. Its B marginal is the same Gibbs state used in the fixed-bath channel. The interaction is U on S and B tensored with the identity on R. Energy conservation is the commutation condition on U.

Access to R and phase-sensitive measurements are separate assumptions of the readout. Wheeler's It from Bit supplies historical context for the question “Is the label j?” Ding and Hu give the fixed-modulus masking context. Here the label runs over the three prescribed qutrit basis inputs.

**Theorem 1.1 (Both preparation marginals).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.purifiedBath_marginals`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserver.purifiedBath_marginals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a normalized nonnegative law p, the coherent preparation has marginal diag(p) on both factors.

**Theorem 1.2 (The actual output is a density).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.purifiedOutput_density`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserver.purifiedOutput_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A unitary on S and B, lifted by the identity on R, preserves positivity and unit trace for every density input with the normalized preparation.

**Theorem 1.3 (Entries of the physical output).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.purifiedOutput_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserver.purifiedOutput_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any system matrix X, its (i,j) entry multiplies the outer product of the two corresponding record vectors. The record for i has amplitudes √p(b) z(b,i) at |b,b⟩.

**Theorem 1.4 (The conditional record from the output).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.conditionalRecord_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserver.conditionalRecord_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the system partial trace after basis input i gives the rank-one record density on bath and reference.

**Theorem 1.5 (The marginal records).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.conditionalRecord_marginals`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserver.conditionalRecord_marginals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ding, Feng; Hu, Xueyuan (2020). *Masking quantum information on hyperdisks*. DOI: [10.1103/PhysRevA.102.042404](https://doi.org/10.1103/PhysRevA.102.042404). URL: <https://arxiv.org/abs/1909.11256v3>.

*Commentary.*

For nonnegative p and unit phases, either partial trace of the basis-conditioned record is diag(p), independent of the label.

**Theorem 1.6 (The joint coordinate readout).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.joint_basis_born`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserver.joint_basis_born` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ding, Feng; Hu, Xueyuan (2020). *Masking quantum information on hyperdisks*. DOI: [10.1103/PhysRevA.102.042404](https://doi.org/10.1103/PhysRevA.102.042404). URL: <https://arxiv.org/abs/1909.11256v3>.

*Commentary.*

The probability of coordinates (b,r) is p(b) when b = r and zero otherwise, for every input label.

**Theorem 1.7 (Expectations for diagonal observables).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.diagonal_observable_expectation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserver.diagonal_observable_expectation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any diagonal observable in the joint coordinate basis, the expectation is its average over (b,b) with weights p(b).

**Theorem 1.8 (Projective effects from an isometry).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.orthogonalReadout_projection`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserver.orthogonalReadout_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The column projectors and the projector onto their orthogonal complement are self-adjoint projections.

**Theorem 1.9 (The effects sum to the identity).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.orthogonalReadout_complete`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserver.orthogonalReadout_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The column outer products sum to VVᴴ and the remaining effect is I − VVᴴ.

**Theorem 1.10 (Born law of the column readout).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.orthogonalReadout_born`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserver.orthogonalReadout_born` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a column of an isometry, the matching effect has probability one and all other effects have probability zero.

**Theorem 1.11 (An exact yes-or-no question for each label).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.joint_decoder_born`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserver.joint_decoder_born` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Archibald Wheeler (1999). *Information, Physics, Quantum: The Search for Links*. DOI: [10.1201/9780429500459-19](https://doi.org/10.1201/9780429500459-19). URL: <https://cqi.inf.usi.ch/qic/wheeler.pdf>.

*Acknowledgement.* Ding, Feng; Hu, Xueyuan (2020). *Masking quantum information on hyperdisks*. DOI: [10.1103/PhysRevA.102.042404](https://doi.org/10.1103/PhysRevA.102.042404). URL: <https://arxiv.org/abs/1909.11256v3>.

*Commentary.*

Under the weighted Gram identity, use the projector onto record j as the yes effect and its complement as the no effect. The yes probability on actual record i is one exactly when i = j. The complete label measurement also has a complementary outcome with probability zero.

**Theorem 1.12 (One interaction for pinching and observation).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.fixed_bath_observable_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserver.fixed_bath_observable_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2022). *Which bath Hamiltonians matter for thermal operations?*. DOI: [10.1063/5.0117534](https://doi.org/10.1063/5.0117534). URL: <https://arxiv.org/abs/2207.11189v4>.

*Commentary.*

At any feasible fixed Gibbs law, one permitted phase unitary gives mixed-bath pinching on every qutrit matrix. With the separate coherent preparation it also supplies the actual records, their marginals and a projective decoder.

**Theorem 1.13 (A feasible Gibbs example).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.feasible_gibbs_observer`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserver.feasible_gibbs_observer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2022). *Which bath Hamiltonians matter for thermal operations?*. DOI: [10.1063/5.0117534](https://doi.org/10.1063/5.0117534). URL: <https://arxiv.org/abs/2207.11189v4>.

*Commentary.*

For every β > 0, the energies matching (29, 27, 25, 19)/100 give the same bridge.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.conditionalRecord_eq`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.conditionalRecord_marginals`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.diagonal_observable_expectation`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.feasible_gibbs_observer`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.fixed_bath_observable_bridge`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.joint_basis_born`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.joint_decoder_born`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.orthogonalReadout_born`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.orthogonalReadout_complete`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.orthogonalReadout_projection`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.purifiedBath_marginals`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.purifiedOutput_density`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserver.purifiedOutput_entry`
- Dependency: [D5/S3/Quantum/Decoherence/FourLevelBathCubic](FourLevelBathCubic.md)
- Dependency: [D5/S3/Quantum/Information/CoherentCopyCorrelationTax](../Information/CoherentCopyCorrelationTax.md)
- Dependency: [D5/S3/Quantum/PureState/JointRecordDecoding](../PureState/JointRecordDecoding.md)
