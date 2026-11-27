# The information threshold for writing two records

## Abstract

Two binary registers reach a prescribed common mutual information at an exact bath variation cost.

**Theorem 1.1 (Information bound from the two branch biases).**

Lean statement: `D5/S3/Quantum/Information/RecordWriting/TwoRegisterInformation.J_le_g_of_bias`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/RecordWriting/TwoRegisterInformation.J_le_g_of_bias` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Wonyong Chung (2026). *The thermodynamic budget of objectivity*. URL: <https://arxiv.org/abs/2611.34909v1>.

*Commentary.*

For a uniform event and a binary readout, let t be the mean of the absolute branch biases. The information in nats is bounded by g(t), the binary Jensen–Shannon information of conditional probabilities min(1, 1/2+t) and min(1, 1/2+t)−t. Opposing signs maximize the marginal entropy at fixed bias magnitudes. Convexity along the remaining interval gives the extremal pair.

**Theorem 1.2 (Each common threshold determines one budget).**

Lean statement: `D5/S3/Quantum/Information/RecordWriting/TwoRegisterInformation.existsUnique_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/RecordWriting/TwoRegisterInformation.existsUnique_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Wonyong Chung (2026). *The thermodynamic budget of objectivity*. URL: <https://arxiv.org/abs/2611.34909v1>.

*Commentary.*

For every information threshold from zero to log 2 nats there is a unique t in the closed unit interval whose g(t) equals the threshold.

**Theorem 1.3 (Two readouts at a common information threshold require bath variation).**

Lean statement: `D5/S3/Quantum/Information/RecordWriting/TwoRegisterInformation.recording_information_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/RecordWriting/TwoRegisterInformation.recording_information_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Wonyong Chung (2026). *The thermodynamic budget of objectivity*. URL: <https://arxiv.org/abs/2611.34909v1>.

*Commentary.*

The event is equiprobable. Each branch starts at the uniform two-bit law and can use its own list of local baths and joint reversible permutations. The bath variation sums the joint endpoint total variations across bath steps with zero charge for permutations. For t in the closed unit interval, if each output marginal carries at least g(t) nats, the mean branch cost is at least t. The range potential bounds the sum of the absolute bias magnitudes before any comparison between branches.

**Theorem 1.4 (A controlled joint permutation attains the threshold).**

Lean statement: `D5/S3/Quantum/Information/RecordWriting/TwoRegisterInformation.recording_information_bound_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/RecordWriting/TwoRegisterInformation.recording_information_bound_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Wonyong Chung (2026). *The thermodynamic budget of objectivity*. URL: <https://arxiv.org/abs/2611.34909v1>.

*Commentary.*

Use the same local resets in both branches to prepare product biases min(1, 2t) and 2t−min(1, 2t). Swap and complement both outputs in the second branch. The two marginals each have information g(t), and the mean bath variation is exactly t. The construction uses ideal weight-one resets in the finite protocol model.

## References

- Truth anchor: `D5/S3/Quantum/Information/RecordWriting/TwoRegisterInformation.J_le_g_of_bias`
- Truth anchor: `D5/S3/Quantum/Information/RecordWriting/TwoRegisterInformation.existsUnique_budget`
- Truth anchor: `D5/S3/Quantum/Information/RecordWriting/TwoRegisterInformation.recording_information_bound`
- Truth anchor: `D5/S3/Quantum/Information/RecordWriting/TwoRegisterInformation.recording_information_bound_sharp`
- Dependency: [D5/S3/DivergenceSupport/LogSumInequality](../../../DivergenceSupport/LogSumInequality.md)
- Dependency: [D5/S3/Quantum/Information/RecordWriting/TwoRegister](TwoRegister.md)
- Dependency: [D5/S3/TotalVariation/ProductSubadditive](../../../TotalVariation/ProductSubadditive.md)
