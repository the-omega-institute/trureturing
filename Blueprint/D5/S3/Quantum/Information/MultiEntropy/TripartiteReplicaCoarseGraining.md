# Tripartite replica coarse graining

## Abstract

Coarse graining of finite tripartite Rényi replica moments.

**Theorem 1.1 (Absolute replica moment bound for each merger).**

Lean statement: `D5/S3/Quantum/Information/MultiEntropy/TripartiteReplicaCoarseGraining.E_abs_coarseGraining_all_mergers`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/MultiEntropy/TripartiteReplicaCoarseGraining.E_abs_coarseGraining_all_mergers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Gadde, S. Jain, V. Krishna, H. Kulkarni, and T. Sharma (2024). *Monotonicity conjecture for multi-party entanglement. Part I*. DOI: [10.1007/JHEP02(2024)025](https://doi.org/10.1007/JHEP02(2024)025). URL: <https://arxiv.org/abs/2308.16247v1>.

*Commentary.*

The original tripartite contraction is the trace of a power of a row transfer matrix. A rectangular Gram factorization expresses the transfer matrix as a compression of a replica permutation. Schatten Hölder bounds the absolute moment by the corresponding grouped bipartite moment raised to the replica order. Replica relabeling gives every merger.

**Theorem 1.2 (Rényi entropies on the positive-moment domain).**

Lean statement: `D5/S3/Quantum/Information/MultiEntropy/TripartiteReplicaCoarseGraining.renyi_coarseGraining_all_mergers_of_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/MultiEntropy/TripartiteReplicaCoarseGraining.renyi_coarseGraining_all_mergers_of_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Gadde, S. Jain, V. Krishna, H. Kulkarni, and T. Sharma (2024). *Monotonicity conjecture for multi-party entanglement. Part I*. DOI: [10.1007/JHEP02(2024)025](https://doi.org/10.1007/JHEP02(2024)025). URL: <https://arxiv.org/abs/2308.16247v1>.

*Commentary.*

When the tripartite moment is positive, the logarithmic Rényi multi-entropy is at least the Rényi entropy of each bipartite merger.

## References

- Truth anchor: `D5/S3/Quantum/Information/MultiEntropy/TripartiteReplicaCoarseGraining.E_abs_coarseGraining_all_mergers`
- Truth anchor: `D5/S3/Quantum/Information/MultiEntropy/TripartiteReplicaCoarseGraining.renyi_coarseGraining_all_mergers_of_positive`
