# Integer Horner recurrence 8

## Abstract

Integer Horner recurrence 8

The coefficient list and private integer vectors are fixed in the data module. Every displayed step is equality of functions on Fin(8192), checked with kernel reduction.

**Theorem 1.1 (step32).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(32\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, 145778728152448221, 0\right)\right) = \operatorname{state}\left(33, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart08.step32` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

**Theorem 1.2 (step33).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(33\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, 0, 0\right)\right) = \operatorname{state}\left(34, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart08.step33` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

**Theorem 1.3 (step34).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(34\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, \operatorname{Negate}\left(244086630072528699\right), 0\right)\right) = \operatorname{state}\left(35, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart08.step34` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

**Theorem 1.4 (step35).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(35\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, 0, 0\right)\right) = \operatorname{state}\left(36, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart08.step35` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart08.step32`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart08.step33`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart08.step34`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart08.step35`
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData](PonciniRasmussenNineHornerData.md)
