# Ordered signed columns

## Abstract

Adaptive signed columns with literal finite histories and prescribed reservoirs.

**Definition 1.1 (Finite dynamic history).**

Lean statement: `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.OrderedHistory`

*Formalization.* `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.OrderedHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A history of depth q stores the target indices, target clopens, finite clopen test families and every actual row's auxiliary indices on Fin(q). A column may contain countably many independent row choices.

**Definition 1.2 (One measured column).**

Lean statement: `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.OrderedColumn`

*Formalization.* `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.OrderedColumn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The column stores the target index and clopen, the fixed finite tests and one auxiliary index for every row.

**Definition 1.3 (Literal append).**

Lean statement: `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.append`

*Formalization.* `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.append` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All four old arrays are retained by Fin.snoc. The new entry is appended at the last index.

**Definition 1.4 (Exact truncation).**

Lean statement: `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.restrict`

*Formalization.* `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.restrict` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Truncation restricts every array along Fin.castSucc.

**Definition 1.5 (Measured extension obligations).**

Lean statement: `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.Spec`

*Formalization.* `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.Spec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate records exact truncation, increasing indices, the active row set, the literal finite exclusion and target slice, target whole-fibre constancy and signed mass, the finite test family, pool membership and every-lift finite signed marginal bounds. It is an output predicate, not a prefix assumption.

**Theorem 1.6 (Adaptive signed column).**

Lean statement: `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.exists_ordered_signed_column`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.exists_ordered_signed_column` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite set of rows with code below q and all earlier columns determine the exclusion. Compact separation derives every fixed clopen fibre test from the original continuous separating coordinates, including empty carriers or coordinate families. The target index retains the earlier tests; its literal slice supplies fibre constancy at that same index. Only then are all earlier tests and the three clopens B(q), H(q), R(q) combined, and each row chooses its next auxiliary index independently.

The row bases form a dependent family. Inputs are actual signed references and infinite reservoirs, coordinate-E, positive target-variation convergence and the previous measured history. No moving-test estimate or suitable successor split is assumed. The one-column theorem does not choose old/new birth reservoirs or initialize the residual label.

**Definition 1.7 (Old reservoirs and the new row's signed pool).**

Lean statement: `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.ordinaryPool`

*Formalization.* `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.ordinaryPool` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Old J and permanent N have proof-indexed domains excluding the distinguished new row. Their intersection uses the original column parity. The new row instead uses its signed convergence pool; no old J or N is supplied at birth.

**Definition 1.8 (Old references and the constructed birth reference).**

Lean statement: `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.ordinaryReference`

*Formalization.* `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.ordinaryReference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An inherited signed reference is supplied only on old rows. The distinguished new row uses its independently extracted signed cluster. This definition never requests an old reference on the new row.

## References

- Truth anchor: `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.OrderedColumn`
- Truth anchor: `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.OrderedHistory`
- Truth anchor: `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.Spec`
- Truth anchor: `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.append`
- Truth anchor: `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.exists_ordered_signed_column`
- Truth anchor: `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.ordinaryPool`
- Truth anchor: `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.ordinaryReference`
- Truth anchor: `D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.restrict`
- Dependency: [D5/S3/Topology/Measures/SignedSplitSuccessorSupport](SignedSplitSuccessorSupport.md)
