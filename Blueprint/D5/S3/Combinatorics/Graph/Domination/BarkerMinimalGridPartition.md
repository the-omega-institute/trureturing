# The total transfer partition

## Abstract

The literal partition covers every full state and carries terminal vectors and all 64 starts to the exact 59-class quotient.

**Definition 1.1 (The total partition).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.classOf`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.classOf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every one of the 4672 full states maps to its literal class in Fin 59, using 73 literal pages of 64 entries indexed by all 4672 state values. Unreachable states remain included.

**Definition 1.2 (Every admitted successor).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.successors`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.successors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The list contains the class of append s m once for every accepted real mask m.

**Definition 1.3 (Expanded quotient rows).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.quotientSuccessors`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.quotientSuccessors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sparse integer weight of each quotient row entry is expanded into that many copies of its destination class.

**Theorem 1.4 (Every full row).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.row_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.row_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every full state s, the complete admitted-successor class list is a permutation of its expanded quotient row. This verifies all destinations and multiplicities without restricting to reachable states.

**Theorem 1.5 (Every full terminal weight).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.terminal_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.terminal_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every full state s, the full terminal weight equals the quotient terminal value at classOf s.

**Definition 1.6 (The initial quotient row).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.alpha`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.alpha` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The 59 exact initial class multiplicities retain all 64 labelled two-column starts.

**Definition 1.7 (Every initial class).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.initialClasses`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.initialClasses` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The class list enumerates the first 64 full states in order.

**Definition 1.8 (Expanded initial row).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.alphaClasses`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.alphaClasses` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The alpha entry at each quotient class is expanded into its stated multiplicity.

**Theorem 1.9 (All initial multiplicities).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.initial_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.initial_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The 64 initial classes are a permutation of alphaClasses, retaining every initial labelled pair exactly once.

The row, terminal and initial multiset identities are checked against the actual transfer predicate for every full state. These finite identities connect the literal data to the all-length actual-subset counting argument.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.alpha`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.alphaClasses`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.classOf`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.initialClasses`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.initial_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.quotientSuccessors`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.row_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.successors`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.terminal_certificate`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient](BarkerMinimalGridQuotient.md)
- Dependency: [D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer](BarkerMinimalGridTransfer.md)
