# Integer Horner recurrence 5

## Abstract

Integer Horner recurrence 5

The state function and coefficient list are fixed integer data. Each equality uses the literal sparseHamiltonian callback and the Boolean comparison of Fin.val with the identity coordinate 4861.

**Theorem 1.1 (step20).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(20\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), 76659122475479, 0\right))) = \operatorname{state}\left(21\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step20` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

**Theorem 1.2 (step21).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(21\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), 0, 0\right))) = \operatorname{state}\left(22\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step21` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

**Theorem 1.3 (step22).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(22\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), -(450854928573687), 0\right))) = \operatorname{state}\left(23\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step22` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

**Theorem 1.4 (step23).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(23\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), 0, 0\right))) = \operatorname{state}\left(24\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step23` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step20`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step21`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step22`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step23`
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData](PonciniRasmussenNineHornerData.md)
