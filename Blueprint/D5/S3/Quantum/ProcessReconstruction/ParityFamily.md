# Parity Obstruction to Local-Output Reconstruction

## Abstract

An explicit unital entanglement-breaking pair agrees on every proper output marginal and has diamond distance two.

On any finite qubit register with a chosen input site i, both channels measure the global input in the computational basis. The first prepares the uniform diagonal state on the parity class specified by input bit i. The second interchanges the parity classes. This gives the claimed failure of the single-output reconstruction implication for every register with at least two sites.

**Proposition 1.1 (Measure-and-prepare form on the full input algebra).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/ParityFamily.parityChannel_measure_prepare`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/ParityFamily.parityChannel_measure_prepare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michał Horodecki, Peter W. Shor and Mary Beth Ruskai (2003). *Entanglement Breaking Channels*. DOI: [10.1142/S0129055X03001709](https://doi.org/10.1142/S0129055X03001709). URL: <https://arxiv.org/abs/quant-ph/0302031v2>.

*Acknowledgement.* Ehud D. Karnin, Jonathan W. Greene and Martin E. Hellman (1983). *On Secret Sharing Systems*. DOI: [10.1109/TIT.1983.1056621](https://doi.org/10.1109/TIT.1983.1056621). URL: <https://www-ee.stanford.edu/~hellman/publications/45.pdf>.

*Commentary.*

For each choice of i and either flip, the channel has positive measurement effects summing to the identity and density states as preparations. On every complex input matrix the output is the sum of these states weighted by the trace pairings with the effects. By Horodecki, Shor and Ruskai, Theorem 2, this is the entanglement-breaking characterization.

**Proposition 1.2 (Each parity channel fixes the identity).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/ParityFamily.parityChannel_unital`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/ParityFamily.parityChannel_unital` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ehud D. Karnin, Jonathan W. Greene and Martin E. Hellman (1983). *On Secret Sharing Systems*. DOI: [10.1109/TIT.1983.1056621](https://doi.org/10.1109/TIT.1983.1056621). URL: <https://www-ee.stanford.edu/~hellman/publications/45.pdf>.

*Commentary.*

Each computational input bit value occurs equally often in the identity. The opposite parity weights therefore cancel in each output diagonal entry.

**Proposition 1.3 (All proper output marginal channels coincide).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/ParityFamily.parityChannel_proper_marginals`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/ParityFamily.parityChannel_proper_marginals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ehud D. Karnin, Jonathan W. Greene and Martin E. Hellman (1983). *On Secret Sharing Systems*. DOI: [10.1109/TIT.1983.1056621](https://doi.org/10.1109/TIT.1983.1056621). URL: <https://www-ee.stanford.edu/~hellman/publications/45.pdf>.

*Commentary.*

For every proper subset of the output sites, partial trace onto that subset gives equal channels with the entire global input. A toggle at a discarded site pairs the opposite parities, leaving the same uniform reduced output. Channel equality also gives equality after arbitrary finite reference amplification.

**Proposition 1.4 (Their global unhalved diamond distance is two).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/ParityFamily.parityChannel_maximal_diamond`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/ParityFamily.parityChannel_maximal_diamond` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michał Horodecki, Peter W. Shor and Mary Beth Ruskai (2003). *Entanglement Breaking Channels*. DOI: [10.1142/S0129055X03001709](https://doi.org/10.1142/S0129055X03001709). URL: <https://arxiv.org/abs/quant-ph/0302031v2>.

*Acknowledgement.* Ehud D. Karnin, Jonathan W. Greene and Martin E. Hellman (1983). *On Secret Sharing Systems*. DOI: [10.1109/TIT.1983.1056621](https://doi.org/10.1109/TIT.1983.1056621). URL: <https://www-ee.stanford.edu/~hellman/publications/45.pdf>.

*Commentary.*

The all-zero computational basis input makes the output supports disjoint, so their trace distance reaches the universal upper bound of two already with a one-dimensional reference. The diamond distance allows every finite reference. The Lean statement requires only a chosen site.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/ParityFamily.parityChannel_maximal_diamond`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/ParityFamily.parityChannel_measure_prepare`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/ParityFamily.parityChannel_proper_marginals`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/ParityFamily.parityChannel_unital`
- Dependency: [D5/S3/Quantum/Foundation/FinitePreparationChannel](../Foundation/FinitePreparationChannel.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/ReconstructionChannels](ReconstructionChannels.md)
