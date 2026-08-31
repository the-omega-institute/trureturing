# An Orthogonal Bell Pair in the Local-Global Residual

## Abstract

Orthogonal Bell pure states have identical complete local marginals.

**Definition 1.1 (Negative-phase Bell coefficients).**

Lean statement: `D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual.bellMinusCoefficients`

*Formalization.* `D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual.bellMinusCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The named two-by-two coefficient matrix has entries one and minus one on the diagonal and zero off the diagonal.

**Definition 1.2 (Negative-phase Bell vector).**

Lean statement: `D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual.bellMinusVector`

*Formalization.* `D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual.bellMinusVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Dividing the named coefficient matrix by the square root of two gives the vector represented by 00 minus 11.

**Definition 1.3 (Negative-phase Bell density).**

Lean statement: `D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual.bellMinusDensity`

*Formalization.* `D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual.bellMinusDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The outer product of the negative-phase Bell vector with its adjoint is its named rank-one density matrix.

**Definition 1.4 (Two-qubit local-global residual).**

Lean statement: `D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual.twoQubitLocalGlobalResidual`

*Formalization.* `D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual.twoQubitLocalGlobalResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the two-factor instance of the source definition. It consists of distinct positive trace-one matrices whose two canonical partial traces agree.

**Theorem 1.5 (The orthogonal Bell pair is locally indistinguishable).**

$$(rhoPlus, rhoMinus) \in QLGRes2 \land\\{}\operatorname{rank}\left(rhoPlus\right) = 1 \land \operatorname{rank}\left(rhoMinus\right) = 1 \land\\{}\operatorname{inner}\left(PhiPlus, PhiMinus\right) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual.bell_pair_local_global_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported positive-phase witness supplies positivity, trace one, rank one, and both local marginals for the first state.

Direct finite calculations give the same data for the negative-phase state. Their off-diagonal density entries differ, while the inner product of the defining vectors is zero.

**Theorem 1.6 (Complete local data do not determine the global state).**

$$QLGRes2 \neq \emptyset.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual.two_qubit_local_global_residual_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive- and negative-phase Bell densities give an explicit member of the two-qubit local-global residual.

**Theorem 1.7 (Degenerate equal pairs are excluded).**

$$\forall \rho, \neg {(\rho, \rho) \in QLGRes2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual.diagonal_pair_not_mem_two_qubit_local_global_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every self-pair is excluded by global distinctness. In particular, this covers the zero pair, identity pair, and every constant self-pair.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual.bellMinusCoefficients`
- Truth anchor: `D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual.bellMinusDensity`
- Truth anchor: `D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual.bellMinusVector`
- Truth anchor: `D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual.bell_pair_local_global_residual`
- Truth anchor: `D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual.diagonal_pair_not_mem_two_qubit_local_global_residual`
- Truth anchor: `D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual.twoQubitLocalGlobalResidual`
- Truth anchor: `D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual.two_qubit_local_global_residual_nonempty`
- Dependency: [D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot](LocalMarginalCorrelationBlindSpot.md)
