# Integer Horner recurrence 5

## Abstract

Integer Horner recurrence 5

The coefficient list and private integer vectors are fixed in the data module. Every displayed step is equality of functions on Fin(8192), checked with kernel reduction.

**Theorem 1.1 (step20).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(20\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, 76659122475479, 0\right)\right) = \operatorname{state}\left(21, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step20` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

**Theorem 1.2 (step21).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(21\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, 0, 0\right)\right) = \operatorname{state}\left(22, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step21` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

**Theorem 1.3 (step22).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(22\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, \operatorname{Negate}\left(450854928573687\right), 0\right)\right) = \operatorname{state}\left(23, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step22` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

**Theorem 1.4 (step23).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(23\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, 0, 0\right)\right) = \operatorname{state}\left(24, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step23` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step20`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step21`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step22`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step23`
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData](PonciniRasmussenNineHornerData.md)
