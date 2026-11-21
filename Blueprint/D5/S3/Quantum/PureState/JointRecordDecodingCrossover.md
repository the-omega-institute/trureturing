# Finite-scale crossover of joint binary-record decoding

## Abstract

Attaining joint POVMs realize the finite-scale limit on the original carriers.

**Theorem 1.1 (The optimum for guessing the full word tends to exp(−scale / 4)).**

Lean statement: `D5/S3/Quantum/PureState/JointRecordDecodingCrossover.pGuess_productRecord_crossover`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/JointRecordDecodingCrossover.pGuess_productRecord_crossover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each index n, the carrier is finite and may depend on n. The pair of complex amplitudes each has squared norm one. With k_n independent fair bits and squared overlap x_n, assume x_n tends to zero, is eventually nonzero, and k_n x_n tends to the finite real scale. The optimal full-word success on the original product carrier tends to exp(−scale / 4).

**Theorem 1.2 (An attaining family and an upper bound uniform over competing POVMs).**

Lean statement: `D5/S3/Quantum/PureState/JointRecordDecodingCrossover.productRecordPOVM_crossover`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/JointRecordDecodingCrossover.productRecordPOVM_crossover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses there is a family of joint POVMs on the original product carriers with success equal to the optimum at every index. Its success converges to exp(−scale / 4). For each positive tolerance, all POVMs at sufficiently large indices have success strictly below the limit plus that tolerance.

## References

- Truth anchor: `D5/S3/Quantum/PureState/JointRecordDecodingCrossover.pGuess_productRecord_crossover`
- Truth anchor: `D5/S3/Quantum/PureState/JointRecordDecodingCrossover.productRecordPOVM_crossover`
- Dependency: [D5/S3/Quantum/PureState/BinaryPureRecordDecoding](BinaryPureRecordDecoding.md)
- Dependency: [D5/S3/Quantum/PureState/PureRecordDecodingThreshold](PureRecordDecodingThreshold.md)
