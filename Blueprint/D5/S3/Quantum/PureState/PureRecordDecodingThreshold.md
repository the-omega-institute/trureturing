# Finite-scale limit of the scalar decoding law

## Abstract

The scalar success curve has logarithmic slope minus one quarter at zero.

**Theorem 1.1 (The success powers converge to exp(−scale / 4)).**

Lean statement: `D5/S3/Quantum/PureState/PureRecordDecodingThreshold.joint_success_crossover`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PureRecordDecodingThreshold.joint_success_crossover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let x_n be real and k_n be a natural copy count. Assume x_n tends to zero, is eventually nonzero, and k_n x_n tends to the finite real scale. Then ((1 + sqrt(1 - x_n)) / 2)^k_n tends to exp(−scale / 4). For the decoding application x_n is the squared overlap, while the scalar theorem allows real inputs.

The logarithm of the one-label success curve has derivative −1/4 at zero. The slope limit on the punctured neighborhood combines with the copy scale, and exponentiation gives the claimed limit.

## References

- Truth anchor: `D5/S3/Quantum/PureState/PureRecordDecodingThreshold.joint_success_crossover`
