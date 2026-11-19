# The signed two-mode endpoint

## Abstract

The endpoint applies the two local maps on different tensor factors with a diagonal sign conjugation.

Write λ = √(2/3). The local map mixes diagonal entries with weights 5/6 and 1/6 and multiplies off-diagonal entries by λ. On the two-mode space, the sign operator is −1 at 10 and +1 at the other three coordinates. The entrywise formula follows by composing the two local maps and the sign conjugations.

A diagonal entry uses the four input entries with respective weights 25/36, 5/36, 5/36 and 1/36. If precisely the second bit changes, the mixed weights are 5λ/6 and λ/6. If precisely the first bit changes, they are 5λ/6 and −λ/6. If both bits change, the entry is multiplied by 2/3 (`A₁_apply`).

**Definition 1.1 (Local mixing map).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankOneEndpointFloor.localMap`

*Formalization.* `D5/S3/Quantum/Semigroups/WuRankOneEndpointFloor.localMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal pair is averaged with weights 5/6 and 1/6. Off-diagonal entries are scaled by λ.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankOneEndpointFloor.localMap`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Information/Pauli/PauliMatrix](../Information/Pauli/PauliMatrix.md)
