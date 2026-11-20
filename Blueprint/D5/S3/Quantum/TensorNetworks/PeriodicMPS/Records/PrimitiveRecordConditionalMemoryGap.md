# Conditional entropy gain from retaining the visible pair

## Abstract

Conditional entropy gain from retaining the visible pair

**Theorem 1.1 (Conditional mutual information of the literal record).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordConditionalMemoryGap.collision_cmi_eq_memory_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordConditionalMemoryGap.collision_cmi_eq_memory_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Acknowledgement.* John Goold, Marcus Huber, Arnau Riera, Lídia del Rio, Paul Skrzypczyk (2016). *The role of quantum information in thermodynamics — a topical review*. DOI: [10.1088/1751-8113/49/14/143001](https://doi.org/10.1088/1751-8113/49/14/143001).

*Commentary.*

For the fair classical label X, visible pair O, and complementary record E, the conditional entropy reduction from adding O to E equals the quantum conditional mutual information I(X:O|E) of the relabeled finite c-q state.

**Theorem 1.2 (Exact leading gain).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordConditionalMemoryGap.collision_memory_gap_asymptotic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordConditionalMemoryGap.collision_memory_gap_asymptotic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Acknowledgement.* John Goold, Marcus Huber, Arnau Riera, Lídia del Rio, Paul Skrzypczyk (2016). *The role of quantum information in thermodynamics — a topical review*. DOI: [10.1088/1751-8113/49/14/143001](https://doi.org/10.1088/1751-8113/49/14/143001).

*Commentary.*

The literal conditional entropy with full ring memory has coefficient one half at the alpha-to-twice-the-ring-length scale. The complementary-only coefficient is larger. Their difference has positive coefficient (302433 - 46875 sqrt(41)) / 16384 and is strictly positive at all sufficiently large ring lengths. In the cited independent-copy erasure model with degenerate Hamiltonians, a bath at fixed temperature, and a work battery, this entropy gain multiplies k_B T to give the work-rate gain. Each erasure-rate limit holds at fixed ring length before the ring-length limit.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordConditionalMemoryGap.collision_cmi_eq_memory_gap`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordConditionalMemoryGap.collision_memory_gap_asymptotic`
- Dependency: [D5/S3/Quantum/Information/OrthogonalRecordEntropy](../../../Information/OrthogonalRecordEntropy.md)
- Dependency: [D5/S3/Quantum/Information/StrongSubadditivity](../../../Information/StrongSubadditivity.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordDiamondCoefficient](PrimitiveRecordDiamondCoefficient.md)
