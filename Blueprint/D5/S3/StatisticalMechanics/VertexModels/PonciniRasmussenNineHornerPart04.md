# Integer Horner recurrence 4

## Abstract

Integer Horner recurrence 4

The coefficient list and private integer vectors are fixed in the data module. Every displayed step is equality of functions on Fin(8192), checked with kernel reduction.

**Theorem 1.1 (step16).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(16\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, 1188246329388, 0\right)\right) = \operatorname{state}\left(17, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart04.step16` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

**Theorem 1.2 (step17).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(17\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, 0, 0\right)\right) = \operatorname{state}\left(18, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart04.step17` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

**Theorem 1.3 (step18).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(18\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, \operatorname{Negate}\left(10605723426434\right), 0\right)\right) = \operatorname{state}\left(19, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart04.step18` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

**Theorem 1.4 (step19).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(19\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, 0, 0\right)\right) = \operatorname{state}\left(20, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart04.step19` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart04.step16`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart04.step17`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart04.step18`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart04.step19`
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData](PonciniRasmussenNineHornerData.md)
