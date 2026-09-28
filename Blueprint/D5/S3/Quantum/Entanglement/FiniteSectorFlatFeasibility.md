# Flat Sector Rank Feasibility

## Abstract

Exact flat basis output under arbitrary positive source and target sector ranks.

**Theorem 1.1 (Positive rank multiples characterize feasibility).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorFlatFeasibility.flat_feasibility`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FiniteSectorFlatFeasibility.flat_feasibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of positive sector-rank functions r and d, two actual local quantum channels produce the exact flat target state on each logical basis sector if and only if r(s)=d(s)m(s) for a positive integer m(s) in every sector.

Necessity uses actual finite dilations. Purity of the joint flat output forces the local amplitudes through the target vector, and an environment projection identifies an integer rank. Sufficiency constructs sectorwise coordinate equivalences, combines them into a local isometry, traces out the residual coordinate, and verifies each exact basis output.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteSectorFlatFeasibility.flat_feasibility`
- Dependency: [D5/S3/Quantum/Entanglement/FiniteSectorChannelModel](FiniteSectorChannelModel.md)
- Dependency: [D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction](FiniteSectorPhysicalConstruction.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
