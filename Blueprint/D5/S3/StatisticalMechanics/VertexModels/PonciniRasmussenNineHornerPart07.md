# Integer Horner recurrence 7

## Abstract

Integer Horner recurrence 7

The coefficient list and private integer vectors are fixed in the data module. Every displayed step is equality of functions on Fin(8192), checked with kernel reduction.

**Theorem 1.1 (step28).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(28\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, 26973986982247197, 0\right)\right) = \operatorname{state}\left(29, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart07.step28` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

**Theorem 1.2 (step29).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(29\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, 0, 0\right)\right) = \operatorname{state}\left(30, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart07.step29` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

**Theorem 1.3 (step30).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(30\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, \operatorname{Negate}\left(69786597194594871\right), 0\right)\right) = \operatorname{state}\left(31, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart07.step30` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

**Theorem 1.4 (step31).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{Add}\left(\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(31\right), i\right), \operatorname{If}\left(\operatorname{val}\left(i\right) = 4861, 0, 0\right)\right) = \operatorname{state}\left(32, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart07.step31` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality combines the split kernel-checked integer coordinate equalities.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart07.step28`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart07.step29`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart07.step30`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart07.step31`
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData](PonciniRasmussenNineHornerData.md)
