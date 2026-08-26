# Local B Readout Residual Dimension

## Abstract

Local B readout leaves the A-local and correlation sectors invisible.

**Theorem 1.1 (The B-local invisible sector has the stated dimension).**

$$\begin{gathered}\forall m: \operatorname{Nat}, n: \operatorname{Nat}, m \geq 1 \land n \geq 1 \Rightarrow\\{}\operatorname{finrankR}(\operatorname{bipartiteTraceZero}(m, n)) = {m \times n}^{2} - 1 \land\\{}\operatorname{finrankR}(\operatorname{localBSector}(m, n)) = n^{2} - 1 \land\\{}\operatorname{finrankR}(\operatorname{Sup}(\operatorname{localASector}(m, n), \operatorname{correlationSector}(m, n))) = n^{2} \times {m^{2} - 1}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/LocalBReadoutResidualDimension.local_b_readout_residual_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical bipartite traceless Hermitian carrier splits into the A-local, B-local, and correlation sectors.

A complete readout restricted to subsystem B occupies the B-local sector. Its invisible complement is the orthogonal join of the A-local and correlation sectors.

The imported sector decomposition supplies orthogonality and the individual ranks; finite-dimensional join formulas give all three displayed dimensions.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/LocalBReadoutResidualDimension.local_b_readout_residual_dimension`
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](BipartiteSectorDecomposition.md)
