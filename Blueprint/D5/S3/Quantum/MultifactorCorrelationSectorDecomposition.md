# Multifactor Correlation Sector Decomposition

## Abstract

Finite Hermitian tensor products split into subset-indexed correlation sectors.

**Theorem 1.1 (Correlation order decomposes the global traceless carrier).**

$$\begin{gathered}\forall I: \operatorname{Type}, \operatorname{Fintype}\left(I\right),\\{}d: I \to \mathbb{N}, (\forall i: I, \operatorname{d}\left(i\right) \geq 1) \Rightarrow\\{}\operatorname{InternalDirectSum}\left(\operatorname{correlationSector}\left(d\right)\right) \land\\{}\operatorname{iSupNonempty}\left(\operatorname{correlationSector}\left(d\right)\right) = \operatorname{traceZeroGlobal}\left(d\right) \land\\{}\operatorname{finrankR}\left(\operatorname{traceZeroGlobal}\left(d\right)\right) = {\prod_{i\in I} \operatorname{d}\left(i\right)}^{2} - 1 \land\\{}(\forall S: \operatorname{Finset}\left(I\right), \operatorname{finrankR}\left(\operatorname{correlationSector}\left(d, S\right)\right) = \prod_{i\in S} {\operatorname{d}\left(i\right)^{2} - 1}) \land\\{}(\forall k\in \mathbb{N}, \operatorname{finrankR}\left(\operatorname{unobservedHighOrder}\left(d, k\right)\right) = \sum_{S: \operatorname{Finset}\left(I\right), \operatorname{card}\left(S\right) > k} \prod_{i\in S} {\operatorname{d}\left(i\right)^{2} - 1}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/MultifactorCorrelationSectorDecomposition.multifactor_correlation_sector_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite family of positive local dimensions, split each real Hermitian space into its scalar identity line and trace-zero subspace. Distributing the tensor product over these local splittings produces one sector for every subset of factors.

The sectors form an internal direct sum. The nonempty sectors are exactly the global trace-zero carrier, and the sector indexed by S has dimension equal to the product of d_i squared minus one over the indices in S.

Consequently, readouts retaining sectors of order at most k leave a residual whose dimension is the sum of those products over subsets of cardinality greater than k. This dimension statement does not assert that a nonzero high-order component is entangled.

The source statement omitted positivity of the local dimensions. The formal theorem assumes every d_i is nonzero: in dimension zero the identity is zero, so the scalar identity sector is not one-dimensional and the stated formulas fail.

## References

- Truth anchor: `D5/S3/Quantum/MultifactorCorrelationSectorDecomposition.multifactor_correlation_sector_decomposition`
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](Entanglement/BipartiteSectorDecomposition.md)
