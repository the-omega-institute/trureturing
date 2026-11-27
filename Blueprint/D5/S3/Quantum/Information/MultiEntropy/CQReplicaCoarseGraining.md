# Tripartite Rényi multi-entropy for classical–quantum marginals

## Abstract

A classical–quantum marginal gives a positive tripartite replica moment and all three coarse-graining inequalities.

**Theorem 1.1 (Trace formula for the tripartite moment).**

Lean statement: `D5/S3/Quantum/Information/MultiEntropy/CQReplicaCoarseGraining.E_eq_trace_tensor_sum_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/MultiEntropy/CQReplicaCoarseGraining.E_eq_trace_tensor_sum_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Gadde, S. Jain, V. Krishna, H. Kulkarni, and T. Sharma (2024). *Monotonicity conjecture for multi-party entanglement. Part I*. DOI: [10.1007/JHEP02(2024)025](https://doi.org/10.1007/JHEP02(2024)025). URL: <https://arxiv.org/abs/2308.16247v1>.

*Commentary.*

The tripartite contraction is the trace of the n-th power of the sum of the n-fold tensor powers of the classical–quantum blocks. The classical labels are constant on each cycle of the first replica translation. The second replica translation gives ordered traces of products of the quantum blocks, which may fail to commute.

**Theorem 1.2 (All three ways to merge two parties).**

Lean statement: `D5/S3/Quantum/Information/MultiEntropy/CQReplicaCoarseGraining.E_coarseGraining_all_mergers`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/MultiEntropy/CQReplicaCoarseGraining.E_coarseGraining_all_mergers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Gadde, S. Jain, V. Krishna, H. Kulkarni, and T. Sharma (2024). *Monotonicity conjecture for multi-party entanglement. Part I*. DOI: [10.1007/JHEP02(2024)025](https://doi.org/10.1007/JHEP02(2024)025). URL: <https://arxiv.org/abs/2308.16247v1>.

*Commentary.*

Let A, B and C have finite bases, let the pure state be normalized, and let the AB marginal be block diagonal along A. The positive quantum blocks may fail to commute. At every integer replica order n ≥ 2, the tripartite moment is real and strictly positive. It is bounded above by the n-th power of the bipartite replica moment after each of the mergers AB, AC and BC. These are the raw moment inequalities of Gadde et al., arXiv:2308.16247, equation (1.13), in this state class. Tasuki, arXiv:2611.34715v1, §2.3, discusses the all-state result at n=2 and the continuum vacuum case. The proof expresses the finite tripartite moment as the trace of a power of a positive sum of tensor powers. The three bounds use the Schatten triangle inequality, the scalar power-sum inequality and monotonicity under positive semidefinite order.

**Theorem 1.3 (Rényi entropy after merging parties).**

Lean statement: `D5/S3/Quantum/Information/MultiEntropy/CQReplicaCoarseGraining.renyi_coarseGraining_all_mergers`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/MultiEntropy/CQReplicaCoarseGraining.renyi_coarseGraining_all_mergers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Gadde, S. Jain, V. Krishna, H. Kulkarni, and T. Sharma (2024). *Monotonicity conjecture for multi-party entanglement. Part I*. DOI: [10.1007/JHEP02(2024)025](https://doi.org/10.1007/JHEP02(2024)025). URL: <https://arxiv.org/abs/2308.16247v1>.

*Commentary.*

The merged bipartite moments are strictly positive. Taking real logarithms with the normalization of equation (1.11) bounds each merged bipartite Rényi entropy above by the tripartite Rényi multi-entropy, for the same finite classical–quantum marginal and replica orders.

## References

- Truth anchor: `D5/S3/Quantum/Information/MultiEntropy/CQReplicaCoarseGraining.E_coarseGraining_all_mergers`
- Truth anchor: `D5/S3/Quantum/Information/MultiEntropy/CQReplicaCoarseGraining.E_eq_trace_tensor_sum_pow`
- Truth anchor: `D5/S3/Quantum/Information/MultiEntropy/CQReplicaCoarseGraining.renyi_coarseGraining_all_mergers`
- Dependency: [D5/S3/Quantum/Entanglement/HiguchiSudbery/HS4Assembly](../../Entanglement/HiguchiSudbery/HS4Assembly.md)
- Dependency: [D5/S3/Quantum/Information/MultiEntropyPositivityRefutation](../MultiEntropyPositivityRefutation.md)
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound](../../Matrix/LinGProperty/ArithmeticBound.md)
- Dependency: [D5/S3/Quantum/NormCompression/UpperBranchReduction](../../NormCompression/UpperBranchReduction.md)
