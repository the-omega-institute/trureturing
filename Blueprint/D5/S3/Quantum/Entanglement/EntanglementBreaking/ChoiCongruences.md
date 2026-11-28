# Choi congruences and entanglement breaking

## Abstract

Rectangular Choi congruences and the k-entanglement-breaking condition.

**Definition 1.1 (Input-first Choi matrix).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.inputChoi`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.inputChoi` (`✓ std3`).

*Citation.* Repana Devendra, Nirupama Mallick and K. Sumesh (2023). *Mapping cone of k-entanglement breaking maps*. DOI: [10.1007/s11117-022-00956-4](https://doi.org/10.1007/s11117-022-00956-4). URL: <https://arxiv.org/abs/2105.14991v2>.

*Commentary.*

The entry with row (i, u) and column (j, v) is the (u, v) entry of the image of the (i, j) matrix unit. This corresponds to the input-first convention in Section 2 of Devendra, Mallick and Sumesh (2023).

**Definition 1.2 (Entanglement breaking at a fixed amplification).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.IsKEB`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.IsKEB` (`✓ std3`).

*Citation.* Repana Devendra, Nirupama Mallick and K. Sumesh (2023). *Mapping cone of k-entanglement breaking maps*. DOI: [10.1007/s11117-022-00956-4](https://doi.org/10.1007/s11117-022-00956-4). URL: <https://arxiv.org/abs/2105.14991v2>.

*Commentary.*

Definition 3.1 of Devendra, Mallick and Sumesh requires a complex-linear map and a positive k-fold left amplification. Every positive semidefinite input to that amplification must give a finite sum of Kronecker products of positive semidefinite factors.

**Theorem 1.3 (Choi compressions suffice for entanglement breaking).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.isKEB_of_choi_congruences`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.isKEB_of_choi_congruences` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rank-one positive input amplifies to a rectangular local congruence of the input-first Choi matrix. A positive semidefinite input is a finite sum of these rank-one inputs. Separability is preserved under their sum.

**Definition 1.4 (From input choi).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.fromInputChoi`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.fromInputChoi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reindex the supplied input-first matrix by swapping the two factors and apply the inverse Choi map.

**Theorem 1.5 (Input choi from input choi).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.inputChoi_fromInputChoi`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.inputChoi_fromInputChoi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Starting from any input-first matrix, inverse Choi conversion followed by input-first Choi conversion gives back the same matrix.

**Definition 1.6 (Amplify).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.amplify`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.amplify` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Tensor the identity map on k by k complex matrices with the given map, with the ancilla as the first factor.

**Theorem 1.7 (Amplify apply).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.amplify_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.amplify_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The amplified entry is the sum over input indices i and j of the Choi entry times the corresponding input block entry.

**Theorem 1.8 (Amplify vec mul vec).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.amplify_vecMulVec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.amplify_vecMulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive rank-one matrix of a vector with coefficient matrix A amplifies to the local congruence of the Choi matrix by A tensor the output identity.

**Theorem 1.9 (Separable local congruence).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.separable_local_congruence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.separable_local_congruence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rectangular local congruence on the first factor preserves separability. It replaces every first positive factor P by A P A*.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.IsKEB`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.amplify`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.amplify_apply`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.amplify_vecMulVec`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.fromInputChoi`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.inputChoi`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.inputChoi_fromInputChoi`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.isKEB_of_choi_congruences`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.separable_local_congruence`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../../Foundation/FiniteKrausRepresentation.md)
