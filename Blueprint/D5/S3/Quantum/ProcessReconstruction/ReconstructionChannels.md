# Reduced Unitary Channels

## Abstract

Finite reduced conjugation channels and reference-amplified trace pairings.

**Definition 1.1 (Unitary evolution followed by output restriction).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/ReconstructionChannels.reducedConjugation`

*Formalization.* `D5/S3/Quantum/ProcessReconstruction/ReconstructionChannels.reducedConjugation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite basis with an equivalence to a product of discarded and kept coordinates, apply unitary conjugation on the entire input and trace out the discarded output coordinates. The result is a canonical quantum channel from the entire input to the kept output.

**Lemma 1.2 (Partial trace and lifted observables are dual).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/ReconstructionChannels.trace_liftObservable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/ReconstructionChannels.trace_liftObservable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite reference coordinates, pairing the reduced joint matrix with an observable on the reference and kept output equals pairing the global joint matrix with its observable lift. The identity holds on complex matrices by expanding the two traces and reindexing the sums.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/ReconstructionChannels.reducedConjugation`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/ReconstructionChannels.trace_liftObservable`
- Dependency: [D5/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence](../Entanglement/LocalObservationPartialTraceEquivalence.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteDiamondDistance](../Foundation/FiniteDiamondDistance.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
