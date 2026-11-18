# Single-party and Bell witnesses

## Abstract

Density operators used to distinguish tensor-index permutation trace norms.

**Definition 1.1 (Correlated basis strings).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.bitPattern`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.bitPattern` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For local dimension d at least two, a subset S of the parties and a bit t, bitPattern is the computational basis string equal to t on S and zero off S.

**Definition 1.2 (The two-string inclusion).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.witnessEmbedding`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.witnessEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For nonempty S, witnessEmbedding includes the all-zero string and the string with ones on S as two orthonormal computational basis vectors; all remaining coordinates are zero.

**Definition 1.3 (The single-party mixed state).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.singleWitness`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.singleWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For party i, singleWitness is the equal mixture of the all-zero string and the string with one at i and zero at all other parties. It is the maximally mixed qubit state at i tensor the zero pure state at every other party.

**Theorem 1.4 (The mixed witness is a density operator).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.singleWitness_isDensity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.singleWitness_isDensity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every number of parties, local dimension at least two and chosen party i, singleWitness is positive semidefinite and has trace one. The two-string inclusion is isometric and preserves the trace of its half-identity block.

**Definition 1.5 (The embedded Bell state).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.bellWitness`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.bellWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For parties i and j, bellWitness is the pure equal superposition of the all-zero string and the string with ones on the set containing i and j. When i and j are distinct, this is the two-party Bell state tensor zero pure states on the other parties.

**Theorem 1.6 (The Bell witness is a density operator).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.bellWitness_isDensity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.bellWitness_isDensity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every number of parties, local dimension at least two and parties i,j, bellWitness is positive semidefinite and has trace one. Distinctness of i and j is not needed for this density assertion.

**Theorem 1.7 (Two diagonal half entries).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.singleWitness_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.singleWitness_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

singleWitness equals the sum of the two matrix units at its correlated zero and one basis strings, each with coefficient one half.

**Theorem 1.8 (Four Bell half entries).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.bellWitness_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.bellWitness_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

bellWitness equals the sum of all four matrix units between its correlated zero and one basis strings, each with coefficient one half.

**Theorem 1.9 (The mixed-state separation).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.singleWitness_traceNorm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.singleWitness_traceNorm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every local dimension at least two, party i and position permutation sigma, the trace norm of the permuted singleWitness is the square root of one half when the ket and bra positions of i are sent to the same output side, and one otherwise. The two nonzero entries are a column, a row, or a pair in distinct rows and columns.

**Theorem 1.10 (Dependence preserves local side status).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.dependent_sameSide`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.dependent_sameSide` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two permutations have equal trace norms on every positive trace-one state in local dimension at least two, then at each party their ket and bra positions lie on the same output side for one permutation if and only if they do so for the other. The positive square root of one half differs from one, so a single-party mixed witness separates the two cases.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.bellWitness`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.bellWitness_eq`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.bellWitness_isDensity`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.bitPattern`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.dependent_sameSide`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.singleWitness`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.singleWitness_eq`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.singleWitness_isDensity`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.singleWitness_traceNorm`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses.witnessEmbedding`
- Dependency: [D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks](BellBlocks.md)
- Dependency: [D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery](RowSetRecovery.md)
