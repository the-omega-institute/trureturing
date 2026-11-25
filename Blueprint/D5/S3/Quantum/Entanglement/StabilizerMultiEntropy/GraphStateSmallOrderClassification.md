# Which connected graph states admit arbitrarily low real GCE orders?

## Abstract

Rank-one pair classes separate connected graph states with low-order hit laws from those with a finite forbidden interval.

**Theorem 1.1 (A finite parity inequality detects an actual negative Walsh mass).**

$$p \le mpp$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateSmallOrderClassification.physical_gap_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

Take a finite connected simple graph with no isolated vertices. If it is neither a star nor a clique, cutting a proper rank-one pair class C leaves cut rank one, whereas every pair meeting both sides has cut rank two. The actual trace moments therefore force singleton hit probability p and independent cross-class hit pairs.

The whole hit set has even parity. If its intersection with C is odd, there is at least one crossing pair. A nonnegative law would require p at most m times the square of p, with m the product of the two side sizes. Below that threshold a straddling even coefficient of the actual physical Walsh transform is strictly negative.

Stars and cliques satisfy the exact converse at all real orders. Their law is a mixture of the empty-set atom and the uniform even law. The same finite parity comparison certifies a negative rate for every other connected graph, which is equivalent to failure of conditional negative definiteness. Disconnected component transport and infinite divisibility under XOR are not claimed in this formal module.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateSmallOrderClassification.physical_gap_readout`
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateConcentratableEntanglement](GraphStateConcentratableEntanglement.md)
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateSmallOrderWalsh](GraphStateSmallOrderWalsh.md)
