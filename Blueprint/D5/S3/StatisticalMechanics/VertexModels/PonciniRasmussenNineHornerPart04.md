# Integer Horner recurrence 4

## Abstract

Integer Horner recurrence 4

The state function and coefficient list are fixed integer data. Each equality uses the literal sparseHamiltonian callback and the Boolean comparison of Fin.val with the identity coordinate 4861.

**Theorem 1.1 (step16).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(16\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), 1188246329388, 0\right))) = \operatorname{state}\left(17\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart04.step16` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

**Theorem 1.2 (step17).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(17\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), 0, 0\right))) = \operatorname{state}\left(18\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart04.step17` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

**Theorem 1.3 (step18).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(18\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), -(10605723426434), 0\right))) = \operatorname{state}\left(19\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart04.step18` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

**Theorem 1.4 (step19).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(19\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), 0, 0\right))) = \operatorname{state}\left(20\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart04.step19` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart04.step16`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart04.step17`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart04.step18`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart04.step19`
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData](PonciniRasmussenNineHornerData.md)
