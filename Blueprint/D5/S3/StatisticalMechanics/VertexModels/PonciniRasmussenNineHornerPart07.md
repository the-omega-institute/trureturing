# Integer Horner recurrence 7

## Abstract

Integer Horner recurrence 7

The state function and coefficient list are fixed integer data. Each equality uses the literal sparseHamiltonian callback and the Boolean comparison of Fin.val with the identity coordinate 4861.

**Theorem 1.1 (step28).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(28\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), 26973986982247197, 0\right))) = \operatorname{state}\left(29\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart07.step28` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

**Theorem 1.2 (step29).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(29\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), 0, 0\right))) = \operatorname{state}\left(30\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart07.step29` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

**Theorem 1.3 (step30).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(30\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), -(69786597194594871), 0\right))) = \operatorname{state}\left(31\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart07.step30` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

**Theorem 1.4 (step31).**

$$((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(\operatorname{state}\left(31\right), i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), 0, 0\right))) = \operatorname{state}\left(32\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart07.step31` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality holds as a function on Fin 8192.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart07.step28`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart07.step29`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart07.step30`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart07.step31`
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData](PonciniRasmussenNineHornerData.md)
