# Bipartite Hermitian Sector Decomposition

## Abstract

Traceless bipartite Hermitian tensors split into three orthogonal sectors.

**Lemma 1.1 (Hermitian matrices have square real dimension).**

$$\forall d, \operatorname{finrankR}\left(\operatorname{HermitianSpace}\left(d\right)\right) = d^{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition.hermitian_space_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real vector space of Hermitian complex d-by-d matrices has dimension d squared. Thus imposing Hermitian symmetry halves the real dimension of the unrestricted complex matrix space.

The dimension calculation decomposes every complex matrix uniquely into its Hermitian real part and i times its Hermitian imaginary part. Comparing the two resulting copies and cancelling their common factor gives the stated square dimension.

**Lemma 1.2 (Traceless Hermitian matrices have codimension one).**

$$\forall d \geq 1, \operatorname{finrankR}\left(\operatorname{traceZeroHermitian}\left(d\right)\right) = d^{2} - 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition.trace_zero_hermitian_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive d, the traceless Hermitian matrices form a real subspace of dimension d squared minus one. The missing direction is exactly the scalar identity line.

The Hilbert--Schmidt inner product with the identity reads off the real trace of a Hermitian matrix. Consequently the trace-zero space is the orthogonal complement of the nonzero identity line, so its dimension is one less than that of the full Hermitian space.

**Theorem 1.3 (The bipartite traceless space splits into three orthogonal sectors).**

$$\begin{gathered}\forall m, n, m \geq 1 \land n \geq 1 \Rightarrow \\{}\operatorname{Sup}\left(\operatorname{localASector}\left(m, n\right), \operatorname{localBSector}\left(m, n\right), \operatorname{correlationSector}\left(m, n\right)\right) = \operatorname{bipartiteTraceZero}\left(m, n\right) \land\\{}\operatorname{Orthogonal}\left(\operatorname{localASector}\left(m, n\right), \operatorname{localBSector}\left(m, n\right)\right) \land \operatorname{Orthogonal}\left(\operatorname{localASector}\left(m, n\right), \operatorname{correlationSector}\left(m, n\right)\right) \land\\{}\operatorname{Orthogonal}\left(\operatorname{localBSector}\left(m, n\right), \operatorname{correlationSector}\left(m, n\right)\right) \land\\{}\operatorname{finrankR}\left(\operatorname{localASector}\left(m, n\right)\right) = m^{2} - 1 \land\\{}\operatorname{finrankR}\left(\operatorname{localBSector}\left(m, n\right)\right) = n^{2} - 1 \land\\{}\operatorname{finrankR}\left(\operatorname{correlationSector}\left(m, n\right)\right) = m^{2} - 1 \times n^{2} - 1.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition.bipartite_sector_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two nonzero finite dimensions, the traceless bipartite Hermitian space consists of three sectors: a traceless operator on A tensored with the scalar identity on B, the symmetric local sector on B, and operators traceless in both factors.

The three sectors are pairwise orthogonal for the real Hilbert--Schmidt inner product, and their join is the entire orthogonal complement of the scalar-scalar identity line. This gives an orthogonal internal decomposition rather than only a dimension count.

Their real dimensions are respectively m squared minus one, n squared minus one, and the product of those two quantities. Tensor-product inner products establish orthogonality, while the product dimension formula and the codimension-one identity sector show that the contained sum already has the full traceless dimension.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition.bipartite_sector_decomposition`
- Truth anchor: `D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition.hermitian_space_finrank`
- Truth anchor: `D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition.trace_zero_hermitian_finrank`
- Dependency: [D5/S3/Quantum/Measurement/BasisMeasurementProjection](../Measurement/BasisMeasurementProjection.md)
