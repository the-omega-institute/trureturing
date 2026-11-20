# Column evolution with a central weld

## Abstract

The binary-tree column sizes and neighbor counts determine the exact compressed walk.

**Theorem 1.1 (Normalized columns and endpoint evolution).**

Lean statement: `D5/S3/Quantum/Dynamics/WeldedColumnEvolution.central_defect_column_evolution`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/WeldedColumnEvolution.central_defect_column_evolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

Let a finite simple graph have columns numbered from zero to 2d+1. Column j has size two raised to the smaller of j and 2d+1-j. Assume the following neighbor counts at each actual vertex. Its neighbors lie in the adjacent columns. From column i to i+1 the count is two for i at most d and one for i greater than d. In the reverse direction from i+1 to i it is one for i below d and two for i at least d.

Take the graph adjacency divided by the square root of two as the graph Hamiltonian. Put the normalized column indicators in the columns of Q. The resulting weighted path has unit nearest-neighbor weights and a central edge of weight square root of two. For every real time t, the indicators are orthonormal, and the actual matrix exponentials of minus i times t times the two Hamiltonians intertwine through Q. The graph exponential entry from the first singleton column to the last equals the endpoint entry of the path exponential.

The neighbor counts act on the normalized indicators with the factor given by the ratio of adjacent square-root sizes. The resulting rectangular matrix identity lifts to the exponential using a block diagonal matrix and its commuting off-diagonal block.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/WeldedColumnEvolution.central_defect_column_evolution`
- Dependency: [D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap](../Matrix/CentralSqrtTwoDefectGap.md)
