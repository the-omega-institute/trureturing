# Subsystem monotonicity of generalized concentratable entanglement for graph states

## Abstract

For normalized graph states, generalized concentratable entanglement is monotone under subsystem inclusion at every real order greater than one.

The graph is any symmetric binary adjacency matrix with zero diagonal. The state has computational coefficients 2^(-N/2) times the sign of the graph's ordered binary quadratic phase. The matrix reduction uses the original coefficients and sums exactly over each omitted binary configuration.

**Theorem 1.1 (Exact cut-rank moments and subsystem monotonicity).**

$$\forall N \in \mathbb{N},\; \forall K \in \mathbb{R},\; \forall A \in \operatorname{BinaryMatrices}\left(\operatorname{Fin}\left(N\right)\right),\; ((\operatorname{Symmetric}\left(A\right)) \land ((\operatorname{ZeroDiagonal}\left(A\right)) \land (1 < K))) \Rightarrow ((\forall U \in \operatorname{Subsets}\left(\operatorname{Fin}\left(N\right)\right),\; \operatorname{TrPower}\left(A, K, U\right) = 2^{\left(1 - K\right) \cdot \operatorname{cutRank}\left(A, U\right)}) \land (\operatorname{Monotone}\left(\operatorname{GCE}\left(A, K\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateConcentratableEntanglement.physical_graph_gce_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

For a subset U of the qubits, r(U) is the binary rank of the rectangular adjacency block from U to its complement. Summing the characters of the omitted bit strings shows that the original reduced density matrix is a trace-one positive multiple of a projector; the real functional calculus gives its exact moment for arbitrary real K > 1. The proof of cut-rank submodularity uses supported subspaces and the dimension identity for their sum and intersection.

Complement symmetry and the Ahlswede–Daykin four-functions theorem show the average of these moments decreases under inclusion. Subtracting it from one and dividing by K - 1 gives the stated increase. This is a positive graph-state class for the measure in Liu, Knörzer, Wang and Tura; it does not overturn the repository's four-qubit refutation for arbitrary pure states or assert an arbitrary stabilizer-state physical transport theorem.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateConcentratableEntanglement.physical_graph_gce_monotone`
