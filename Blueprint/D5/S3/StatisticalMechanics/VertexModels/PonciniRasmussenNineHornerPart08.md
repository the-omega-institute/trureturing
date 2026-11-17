# Integer Horner recurrence 8

## Abstract

Integer Horner recurrence 8

The state function and coefficient list are fixed integer data. Each equality uses the literal sparseHamiltonian callback and the Boolean comparison of Fin.val with the identity coordinate 4861.

**Theorem 1.1 (step32).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(32\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), 145778728152448221, 0\right))) = \operatorname{state}\left(33\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart08.step32` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

**Theorem 1.2 (step33).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(33\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), 0, 0\right))) = \operatorname{state}\left(34\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart08.step33` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

**Theorem 1.3 (step34).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(34\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), -(244086630072528699), 0\right))) = \operatorname{state}\left(35\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart08.step34` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

**Theorem 1.4 (step35).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(35\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), 0, 0\right))) = \operatorname{state}\left(36\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart08.step35` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart08.step32`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart08.step33`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart08.step34`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart08.step35`
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData](PonciniRasmussenNineHornerData.md)
