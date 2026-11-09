# Integer Horner recurrence 12

## Abstract

Integer Horner recurrence 12

The state function and coefficient list are fixed integer data. Each equality uses the literal sparseHamiltonian callback and the Boolean comparison of Fin.val with the identity coordinate 4861.

**Theorem 1.1 (step48).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(48\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), 5347591521504921, 0\right))) = \operatorname{state}\left(49\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart12.step48` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

**Theorem 1.2 (step49).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(49\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), 0, 0\right))) = \operatorname{state}\left(50\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart12.step49` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

**Theorem 1.3 (step50).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(50\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), -(762922848588417), 0\right))) = \operatorname{state}\left(51\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart12.step50` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

**Theorem 1.4 (step51).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(51\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), 0, 0\right))) = \operatorname{state}\left(52\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart12.step51` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart12.step48`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart12.step49`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart12.step50`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart12.step51`
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData](PonciniRasmussenNineHornerData.md)
