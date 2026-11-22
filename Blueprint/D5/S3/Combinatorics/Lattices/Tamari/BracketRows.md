# Interval rows in the bracket lattice

## Abstract

Interval rows compare by their endpoints in the complete bracket order.

**Definition 1.1 (Bracket inequalities).**

$$\forall n \in \mathbb{N},\; \forall a \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(n\right),\; \operatorname{IsBracketing}\left(a\right) \Leftrightarrow \left((\forall i \in \operatorname{Fin}\left(n\right),\; i \le a\left(i\right)) \land (\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \left(i \le j \land j \le a\left(i\right)\right) \Rightarrow a\left(j\right) \le a\left(i\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.IsBracketing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A bracketing function on Fin n is extensive. Every coordinate between i and its endpoint has endpoint at most the endpoint of i.

**Definition 1.2 (Bracketing functions).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.BracketingFunctions`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.BracketingFunctions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The subtype of functions Fin n → Fin n satisfying IsBracketing carries the pointwise order.

**Definition 1.3 (Row indices).**

$$\forall n \in \mathbb{N},\; \operatorname{RowIndex}\left(n\right) = \{s \mid 1 \le s \land s \le n\}$$

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.RowIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index s ranges over the one-based proper right endpoints 1 ≤ s ≤ n in ambient size n + 1.

**Definition 1.4 (Admissible left endpoints).**

$$\forall n \in \mathbb{N},\; \forall s \in \operatorname{RowIndex}\left(n\right),\; \operatorname{LeftEndpoint}\left(s\right) = \{a \mid 1 \le a \land a \le \operatorname{val}\left(s\right)\}$$

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.LeftEndpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The left endpoint of row s is between 1 and s inclusive.

**Definition 1.5 (Zero-based indexing).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.rowIndexEquiv`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.rowIndexEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equivalence from Fin n to RowIndex(n) adds one to the coordinate. Its inverse subtracts one.

**Definition 1.6 (The bracket row).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.row`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.row` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The one-based row takes value s on the inclusive interval from a to s and n + 1 off that interval.

**Theorem 1.7 (One-based row values).**

$$\forall n \in \mathbb{N},\; \forall s \in \operatorname{RowIndex}\left(n\right),\; \forall a \in \operatorname{LeftEndpoint}\left(s\right),\; \forall i \in \operatorname{Fin}\left(n + 1\right),\; \operatorname{val}\left(\operatorname{val}\left(\operatorname{row}\left(s, a\right)\right)\left(i\right)\right) + 1 = \operatorname{ite}\left((\operatorname{val}\left(a\right) \le \operatorname{val}\left(i\right) + 1 \land \operatorname{val}\left(i\right) + 1 \le \operatorname{val}\left(s\right)), \operatorname{val}\left(s\right), n + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.row_value_oneBased` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula converts the Fin coordinate and its output to one-based values.

**Theorem 1.8 (Comparison of two rows).**

$$\forall n \in \mathbb{N},\; \forall s \in \operatorname{RowIndex}\left(n\right),\; \forall t \in \operatorname{RowIndex}\left(n\right),\; \forall a \in \operatorname{LeftEndpoint}\left(s\right),\; \forall b \in \operatorname{LeftEndpoint}\left(t\right),\; (\operatorname{row}\left(s, a\right) \le \operatorname{row}\left(t, b\right)) \Leftrightarrow (s = t \land \operatorname{val}\left(a\right) \le \operatorname{val}\left(b\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.row_le_row_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rows at different right endpoints are incomparable. At the same right endpoint their order is the order of their left endpoints.

**Definition 1.9 (A family of rows).**

$$\forall n \in \mathbb{N},\; \forall A \in \pi (s:\operatorname{RowIndex}\left(n\right)) \operatorname{LeftEndpoint}\left(s\right),\; \forall s \in \operatorname{RowIndex}\left(n\right),\; \operatorname{rowFamily}\left(A, s\right) = \operatorname{row}\left(s, A\left(s\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.rowFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The row associated to index s uses left endpoint A(s).

**Theorem 1.10 (Generated lower sets).**

$$\forall n \in \mathbb{N},\; \forall A \in \pi (s:\operatorname{RowIndex}\left(n\right)) \operatorname{LeftEndpoint}\left(s\right),\; \forall B \in \pi (s:\operatorname{RowIndex}\left(n\right)) \operatorname{LeftEndpoint}\left(s\right),\; (\operatorname{lowerClosure}\left(\operatorname{range}\left(\operatorname{rowFamily}\left(A\right)\right)\right) \le \operatorname{lowerClosure}\left(\operatorname{range}\left(\operatorname{rowFamily}\left(B\right)\right)\right)) \Leftrightarrow (\forall s \in \operatorname{RowIndex}\left(n\right),\; \operatorname{val}\left(A\left(s\right)\right) \le \operatorname{val}\left(B\left(s\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.lowerClosure_rowFamily_le_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every generator must be dominated by some generator of the upper family. Row comparison forces the same index and compares the left endpoints there.

**Theorem 1.11 (Distinct row indices).**

$$\forall n \in \mathbb{N},\; \forall A \in \pi (s:\operatorname{RowIndex}\left(n\right)) \operatorname{LeftEndpoint}\left(s\right),\; \operatorname{Injective}\left(\operatorname{rowFamily}\left(A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.rowFamily_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The row comparison shows that equal rows have equal right endpoints.

**Theorem 1.12 (Number of rows).**

$$\forall n \in \mathbb{N},\; \forall A \in \pi (s:\operatorname{RowIndex}\left(n\right)) \operatorname{LeftEndpoint}\left(s\right),\; \operatorname{ncard}\left(\operatorname{range}\left(\operatorname{rowFamily}\left(A\right)\right)\right) = n$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.rowFamily_ncard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are n distinct rows, one per index.

**Definition 1.13 (Complete bracket lattice).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.bracketCompleteLattice`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.bracketCompleteLattice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a family of brackets on Fin(n + 1), take the coordinate minima with n adjoined. The resulting function is a bracket and the greatest lower bound.

**Theorem 1.14 (Coordinate minima).**

$$\forall n \in \mathbb{N},\; \forall C \in \operatorname{Set}\left(\operatorname{BracketingFunctions}\left(n + 1\right)\right),\; \forall i \in \operatorname{Fin}\left(n + 1\right),\; \operatorname{val}\left(\operatorname{val}\left(\operatorname{sInf}\left(C\right)\right)\left(i\right)\right) = \operatorname{sInf}\left(\operatorname{insert}\left(n, \{\operatorname{val}\left(\operatorname{val}\left(b\right)\left(i\right)\right) \mid b \in C\}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.sInf_coord_min` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The adjoined value supplies the coordinate of the empty meet.

**Theorem 1.15 (A coordinate minimum is attained or last).**

$$\forall n \in \mathbb{N},\; \forall C \in \operatorname{Set}\left(\operatorname{BracketingFunctions}\left(n + 1\right)\right),\; \forall i \in \operatorname{Fin}\left(n + 1\right),\; (\operatorname{val}\left(\operatorname{sInf}\left(C\right)\right)\left(i\right) = \operatorname{last}\left(n\right)) \lor (\exists b \in C,\; \operatorname{val}\left(\operatorname{sInf}\left(C\right)\right)\left(i\right) = \operatorname{val}\left(b\right)\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.sInf_coord_eq_or` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the minimum is not the last coordinate, it comes from one of the given brackets.

**Theorem 1.16 (The top bracket).**

$$\forall n \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(n + 1\right),\; \operatorname{val}\left(\operatorname{top}\right)\left(i\right) = \operatorname{last}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.top_coord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every coordinate of the top bracket on Fin(n + 1) is the last coordinate.

**Theorem 1.17 (Join as an infimum).**

$$\forall n \in \mathbb{N},\; \forall a \in \operatorname{BracketingFunctions}\left(n + 1\right),\; \forall b \in \operatorname{BracketingFunctions}\left(n + 1\right),\; \operatorname{sup}\left(a, b\right) = \operatorname{sInf}\left(\{c \mid a \le c \land b \le c\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.sup_eq_inf_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The join of two brackets is the meet of their common upper bounds.

## References

- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.BracketingFunctions`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.IsBracketing`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.LeftEndpoint`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.RowIndex`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.bracketCompleteLattice`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.lowerClosure_rowFamily_le_iff`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.row`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.rowFamily`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.rowFamily_injective`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.rowFamily_ncard`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.rowIndexEquiv`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.row_le_row_iff`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.row_value_oneBased`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.sInf_coord_eq_or`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.sInf_coord_min`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.sup_eq_inf_upper`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/BracketRows.top_coord`
