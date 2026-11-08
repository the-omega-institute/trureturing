# Integer Horner recurrence 12

## Abstract

Integer Horner recurrence 12

The coefficient list and private integer vectors are fixed in the data module. Every displayed step is equality of functions on Fin(8192), checked with kernel reduction.

**Theorem 1.1 (step48).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(48\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, 5347591521504921, 0\right)\right) = \operatorname{state}\left(49, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart12.step48` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

**Theorem 1.2 (step49).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(49\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, 0, 0\right)\right) = \operatorname{state}\left(50, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart12.step49` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

**Theorem 1.3 (step50).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(50\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, \operatorname{Negate}\left(762922848588417\right), 0\right)\right) = \operatorname{state}\left(51, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart12.step50` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

**Theorem 1.4 (step51).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(51\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, 0, 0\right)\right) = \operatorname{state}\left(52, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart12.step51` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart12.step48`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart12.step49`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart12.step50`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart12.step51`
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData](PonciniRasmussenNineHornerData.md)
