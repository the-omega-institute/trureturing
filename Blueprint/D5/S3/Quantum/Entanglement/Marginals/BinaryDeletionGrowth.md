# Exponential growth of the binary deletion kernel

## Abstract

Growth of the one-site deletion kernel on open chains with forbidden occupied runs.

**Theorem 1.1 (Uniform lower bound).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionGrowth.kernelDimension_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionGrowth.kernelDimension_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider a chain of k plus two sites that forbids a run of length K. When K is at least four, the dimension of the supported one-site deletion kernel is at least (9/4) to the power k. The bound also holds when the forbidden run is longer than the chain.

Begin with two opposite differences. Track the ages of the last occurrences of the two orientations. The six states have two distinct ages between zero and three. A move repeats the newer orientation, emits the older orientation, or adds agreement. Every permitted move keeps both ages below four. The resulting patterns contain both orientations in each window of four, and hence in each longer window.

Weight the states with ages (0,1), (0,2), (0,3), (1,2), (1,3), and (2,3) by 100, 75, 43, 58, 32, and 18 respectively. At each state the sum of successor weights is at least 9/4 times its weight. Induction on the number of remaining moves gives the lower bound from the initial state, whose weight is 100. Each valid output encodes its moves uniquely.

**Theorem 1.2 (Growth relative to the allowed space).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionGrowth.kernelDimension_to_allowedCount`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionGrowth.kernelDimension_to_allowedCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The number of allowed words is positive because the all-zero word is allowed. There are at most 2^(k+2) words. Dividing the kernel lower bound by this upper bound shows that the ratio of the kernel dimension to the number of allowed words is at least one quarter of (9/8) to the power k.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionGrowth.kernelDimension_lower`
- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionGrowth.kernelDimension_to_allowedCount`
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionDimension](BinaryDeletionDimension.md)
