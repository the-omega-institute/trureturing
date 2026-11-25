# One-way Fourier readout of the purified bath

## Abstract

A Fourier measurement on the reference and an outcome-dependent bath measurement recover the label.

Use the coherent preparation of the fixed-bath observer and keep access to both systems. Measure the reference in the four-point Fourier basis, send its outcome k to the bath observer, and use the corresponding phase-adjusted projectors on the bath. The measurement model grants phase-sensitive control on each side.

**Theorem 1.1 (Reference projectors).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.referenceEffect_projection`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.referenceEffect_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each Fourier column defines a self-adjoint projection in the reference space.

**Theorem 1.2 (Four reference outcomes).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.referenceEffect_complete`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.referenceEffect_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four Fourier basis projectors sum to the reference identity.

**Theorem 1.3 (Effect of the partial inner product).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.fourierAnalysis_effect`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.fourierAnalysis_effect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The branch operator I_B ⊗ ⟨fₖ| has adjoint product I_B ⊗ |fₖ⟩⟨fₖ|.

**Theorem 1.4 (Orthogonal bath columns in each branch).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.fourierColumns_isometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.fourierColumns_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conjugated Fourier character is a diagonal unitary on B and preserves the weighted column Gram matrix.

**Theorem 1.5 (The actual subnormalized bath branch).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.fourierBranch_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.fourierBranch_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On basis input i, reference outcome k leaves 1/4 times the rank-one operator of the phase-adjusted bath column for i.

**Theorem 1.6 (Uniform outcome on the reference).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.fourier_outcome_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.fourier_outcome_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each k has probability 1/4 for every input label under the weighted Gram identity.

**Theorem 1.7 (Exact label readout after one message).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.fourier_decoder_born`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.fourier_decoder_born` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Archibald Wheeler (1999). *Information, Physics, Quantum: The Search for Links*. DOI: [10.1201/9780429500459-19](https://doi.org/10.1201/9780429500459-19). URL: <https://cqi.inf.usi.ch/qic/wheeler.pdf>.

*Commentary.*

The joint probability of (k,o) is 1/4 when o reports the input label and zero otherwise, including the complementary outcome. Thus every k yields the correct decoded label. For a prescribed j, testing whether the bath result is j gives the corresponding yes-or-no answer.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.fourierAnalysis_effect`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.fourierBranch_eq`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.fourierColumns_isometry`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.fourier_decoder_born`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.fourier_outcome_uniform`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.referenceEffect_complete`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.referenceEffect_projection`
- Dependency: [D5/S3/Quantum/Decoherence/FourLevelBathObserver](FourLevelBathObserver.md)
- Dependency: [D5/S3/Quantum/Dynamics/PolygonalFourierCouplings](../Dynamics/PolygonalFourierCouplings.md)
