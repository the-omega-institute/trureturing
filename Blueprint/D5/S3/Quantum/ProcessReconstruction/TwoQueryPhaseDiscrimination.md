# Two-query longitudinal dephasing discrimination

## Abstract

Sharp trace-distance separation for two independent phase-dephasing queries.

**Theorem 1.1 (An upper bound for strategies with finite retained memory).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/TwoQueryPhaseDiscrimination.experiment_traceNorm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/TwoQueryPhaseDiscrimination.experiment_traceNorm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stanisław Sieniawski and Rafał Demkowicz-Dobrzański (2026). *Adaptive quantum channel discrimination using methods of quantum metrology*. DOI: [10.1088/1367-2630/ae3edd](https://doi.org/10.1088/1367-2630/ae3edd). URL: <https://arxiv.org/abs/2510.15506v3>.

*Commentary.*

A complementary mixture of two phase unitaries represents each hypothesis. At two queries the mixed-label terms cancel, even through an isometric control. Comparing the remaining pure paths through their common intermediate path gives the upper bound.

**Theorem 1.2 (A parallel pure probe attains the bound).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/TwoQueryPhaseDiscrimination.parallel_attains`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/TwoQueryPhaseDiscrimination.parallel_attains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stanisław Sieniawski and Rafał Demkowicz-Dobrzański (2026). *Adaptive quantum channel discrimination using methods of quantum metrology*. DOI: [10.1088/1367-2630/ae3edd](https://doi.org/10.1088/1367-2630/ae3edd). URL: <https://arxiv.org/abs/2510.15506v3>.

*Commentary.*

A two-qubit input places equal weights on complementary basis strings. Choosing the total weight on the equal strings minimizes the overlap of the two extreme pure outputs. This saturates the trace-distance bound.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/TwoQueryPhaseDiscrimination.experiment_traceNorm_le`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/TwoQueryPhaseDiscrimination.parallel_attains`
- Dependency: [D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability](../Entanglement/ConicalDesignConcurrenceComparability.md)
- Dependency: [D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation](../Information/ChenKatoBrandaoTraceNormCMIRefutation.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/PureDistance](PureDistance.md)
