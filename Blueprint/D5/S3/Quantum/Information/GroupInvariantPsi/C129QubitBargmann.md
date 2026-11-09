# C129 qubit three-label orientation

## Abstract

The ordered qubit Bargmann trace is the Bloch scalar-plus-oriented-volume formula.

**Definition 1.1 (Pauli combination).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.pauliCombination`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.pauliCombination` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit two by two complex matrix with the three real coordinates in the Pauli X, Y and Z slots.

**Definition 1.2 (Bloch projector expression).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.qubitProjector`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.qubitProjector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The affine half-sum of the identity matrix and the Pauli combination. Unit Bloch vectors give the pure-qubit projector case.

**Definition 1.3 (Ordered triple trace).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.tripleBargmann`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.tripleBargmann` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The trace of the ordered product of the three Bloch projector expressions.

**Definition 1.4 (Rank-one state projector).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.stateProjector`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.stateProjector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rank-one density matrix built from a two-component complex amplitude vector.

**Definition 1.5 (Computational basis state).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vZero`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The amplitude vector for the state |0⟩.

**Definition 1.6 (Real equatorial state).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vPlus`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vPlus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The amplitude vector (|0⟩+|1⟩)/√2.

**Definition 1.7 (Positive Y state).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vYPlus`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vYPlus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The amplitude vector (|0⟩+i|1⟩)/√2.

**Definition 1.8 (Negative Y state).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vYMinus`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vYMinus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The amplitude vector (|0⟩−i|1⟩)/√2.

**Definition 1.9 (State triple trace).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.stateTripleBargmann`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.stateTripleBargmann` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The trace of the ordered product of three rank-one state projectors.

**Theorem 1.10 (Bloch formula for the ordered qubit trace).**

$$\forall r \in (\operatorname{Fin}\left(3\right)) \to (\mathbb{R}),\; \forall s \in (\operatorname{Fin}\left(3\right)) \to (\mathbb{R}),\; \forall t \in (\operatorname{Fin}\left(3\right)) \to (\mathbb{R}),\; \operatorname{tripleBargmann}\left(r, s, t\right) = \frac{\operatorname{Complex.ofReal}\left((1: \mathbb{R}) + \operatorname{dotProduct}\left(r, s\right) + \operatorname{dotProduct}\left(s, t\right) + \operatorname{dotProduct}\left(t, r\right)\right)}{4} + \frac{\operatorname{Complex.ofReal}\left(\operatorname{dotProduct}\left(r, \operatorname{crossProduct}\left(s, t\right)\right)\right) \cdot \mathrm{i}}{4}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.triple_bargmann_bloch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity is proved by expanding the three explicit two by two matrices. It is stated for arbitrary real three-coordinate vectors; unit-norm vectors give the pure-qubit interpretation from the source atom. The scalar terms are the three pairwise dot products and the imaginary term is the oriented scalar triple product.

**Theorem 1.11 (Opposite Bloch orientations).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.explicit_qubit_orientation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.explicit_qubit_orientation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordered coordinate triples (0,0,1), (1,0,0), and (0,±1,0) give the two values (1+i)/4 and (1-i)/4. The pairwise dot products vanish while the oriented triple product changes sign.

**Theorem 1.12 (Explicit pure-state witnesses).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.explicit_state_orientation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.explicit_state_orientation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For v₁=|0⟩, v₂=(|0⟩+|1⟩)/√2, and v₃±=(|0⟩±i|1⟩)/√2, the rank-one density matrices have ordered traces (1±i)/4. This records the concrete two-sign witness; the remaining geometric interpretation of zero added orthogonal remainder stays in the source prose.

## References

- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.explicit_qubit_orientation`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.explicit_state_orientation`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.pauliCombination`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.qubitProjector`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.stateProjector`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.stateTripleBargmann`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.tripleBargmann`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.triple_bargmann_bloch`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vPlus`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vYMinus`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vYPlus`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vZero`
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../../PureState/PureStateHandshake.md)
