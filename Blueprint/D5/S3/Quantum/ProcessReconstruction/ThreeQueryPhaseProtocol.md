# Three-query longitudinal dephasing discrimination

## Abstract

A strict adaptive advantage in three independent queries to a qubit dephasing channel.

**Theorem 1.1 (A common isometric control separates the two strategy classes).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/ThreeQueryPhaseProtocol.three_query_adaptive_advantage`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/ThreeQueryPhaseProtocol.three_query_adaptive_advantage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stanisław Sieniawski and Rafał Demkowicz-Dobrzański (2026). *Adaptive quantum channel discrimination using methods of quantum metrology*. DOI: [10.1088/1367-2630/ae3edd](https://doi.org/10.1088/1367-2630/ae3edd). URL: <https://arxiv.org/abs/2510.15506v3>.

*Commentary.*

The two hypotheses preserve the computational-basis populations and multiply the upper coherence by 3/4 plus or minus 5i/16. A diagonal path Gram matrix covers normalized pure parallel probes with arbitrary finite auxiliary memory. A feasible dual matrix bounds their trace distance. A normalized input, isometric control and Hermitian contraction realize a larger readout in the adaptive protocol. The exact certificate gives a trace-distance gap of at least 2281037/4096000000.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/ThreeQueryPhaseProtocol.three_query_adaptive_advantage`
- Dependency: [D5/S3/Quantum/Foundation/FiniteHermitianTraceDuality](../Foundation/FiniteHermitianTraceDuality.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
