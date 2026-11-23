# Exponential growth of the binary deletion kernel

## Abstract

Growth of the one-site deletion kernel on open chains with forbidden occupied runs.

**Theorem 1.1 (Uniform lower bound).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionGrowth.kernelDimension_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionGrowth.kernelDimension_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider a chain of k plus two sites that forbids a run of length K. When K is at least four, the dimension of the supported one-site deletion kernel is at least (100/43) to the power k. The bound also holds when the forbidden run is longer than the chain.

Begin with two opposite differences. Track the ages of the last occurrences of the two orientations. The six states have two distinct ages between zero and three. A move repeats the newer orientation, emits the older orientation, or adds agreement. Every permitted move keeps both ages below four. The resulting patterns contain both orientations in each window of four, and hence in each longer window.

Weight the states with ages (0,1), (0,2), (0,3), (1,2), (1,3), and (2,3) by 100, 75, 43, 58, 32, and 18 respectively. At each state the sum of successor weights is at least 100/43 times its weight. Induction on the number of remaining moves gives the lower bound from the initial state, whose weight is 100. Each valid output encodes its moves uniquely.

**Theorem 1.2 (Growth relative to the allowed space).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionGrowth.kernelDimension_to_allowedCount`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionGrowth.kernelDimension_to_allowedCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider k plus two sites and forbid an occupied run of length K, with K at least four. The number of allowed words is positive because the all-zero word is allowed. There are at most 2^(k+2) words. Dividing the kernel lower bound by this upper bound shows that the ratio of the kernel dimension to the number of allowed words is at least one quarter of (50/43) to the power k.

**Theorem 1.3 (Exact recurrence for four-site windows).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionGrowth.kernelDimension_four_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionGrowth.kernelDimension_four_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d(n) be the dimension of the one-site deletion kernel on an open chain of n sites with no four consecutive occupied sites. For n at least four, d(n+6) + d(n+1) + d(n) equals d(n+5) + 2d(n+4) + 2d(n+3) + 2d(n+2).

Each surviving pattern has both directions in its first four sites. Its first window determines the two ages and the newer direction. Every subsequent legal symbol determines a unique move. Conversely, each allowed move sequence produces one surviving pattern. The six-state successor operator satisfies the displayed recurrence, so summing the exact extension counts over the first windows proves it.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionGrowth.kernelDimension_four_recurrence`
- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionGrowth.kernelDimension_lower`
- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionGrowth.kernelDimension_to_allowedCount`
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionDimension](BinaryDeletionDimension.md)
