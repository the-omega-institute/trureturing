# Channel Fixed-Block Decomposition

## Abstract

A record channel fixes exactly the full matrix blocks on its record classes.

**Theorem 1.1 (Channel fixed-block decomposition).**

$$\begin{aligned}\forall d, e: \mathbb{N}, Lambda: \operatorname{Type}, [\operatorname{Fintype}(Lambda)], [\operatorname{DecidableEq}(Lambda)],\\\forall record: \operatorname{Fin}(d) \to \operatorname{Fin}(e) \to \mathbb{C}, classOf: \operatorname{Fin}(d) \to Lambda,\\(\forall i, j: \operatorname{Fin}(d), \operatorname{recordGram}(record, i, j) = 1 \iff classOf\left(i\right) = classOf\left(j\right)) \Rightarrow \\(\forall \rho: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), \operatorname{recordChannel}(record, \rho) = \rho \iff \forall i, j: \operatorname{Fin}(d), classOf\left(i\right) \neq classOf\left(j\right) \Rightarrow \operatorname{entry}(\rho, i, j) = 0) \land\\(\forall blocks: \prod_{alpha: Lambda} \operatorname{Matrix}(\left\{classOf\left(i\right) = alpha \mid i \in \operatorname{Fin}(d)\right\}, \left\{classOf\left(i\right) = alpha \mid i \in \operatorname{Fin}(d)\right\}, \mathbb{C}), alpha: Lambda, i, j: \left\{classOf\left(i\right) = alpha \mid i \in \operatorname{Fin}(d)\right\}, \operatorname{entry}(\operatorname{classifiedBlockAlgEquiv}(classOf)\left(blocks\right), i, j) = \operatorname{entry}(blocks\left(alpha\right), i, j)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedAlgebra/ChannelFixedBlockDecomposition.channel_fixed_block_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d and e be natural dimensions and Lambda a finite decidable record-class type. The environment record is a complex amplitude table, and classOf assigns each address to its record class.

The public classification premise identifies Gram entry one exactly with equality of record classes. The channel and Gram matrix are the canonical primitives imported from the record family.

The class-supported algebra is defined directly by vanishing of entries between different classes. It is not defined as the range of the block map or as the channel fixed set.

The named classifiedBlockAlgEquiv first embeds one full matrix algebra per proof-relevant class fiber and then applies the canonical sigma-fiber reindexing. The second displayed clause pins this equivalence to the original within-class matrix entries.

## References

- Truth anchor: `D5/S3/Quantum/FixedAlgebra/ChannelFixedBlockDecomposition.channel_fixed_block_decomposition`
- Dependency: [D5/S3/Quantum/FixedAlgebra/RecordFixedAlgebraDecomposition](RecordFixedAlgebraDecomposition.md)
- Dependency: [D5/S3/Quantum/FixedAlgebra/SingletonRecordClassicality](SingletonRecordClassicality.md)
