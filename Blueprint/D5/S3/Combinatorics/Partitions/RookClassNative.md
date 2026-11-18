# Native rook classes and common padding

## Abstract

Native m-level placements give a finite unrestricted class carrier and a common padding bound.

**Definition 1.1 (Bottom-aligned cells).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookClassNative.cells`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookClassNative.cells` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing normalizedColumnsEquiv sends a positive increasing column tuple to its actual finite Young diagram. Its first coordinate is the row counted from the bottom and its second coordinate counts columns from the right. This horizontal reflection preserves column conflicts and bottom-aligned levels. No zero column or horizontal translation is a new normalized shape.

**Definition 1.2 (Literal area).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookClassNative.area`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookClassNative.area` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The area is the sum of the positive column heights, equal to the cardinality of cells.

**Definition 1.3 (The native conflict rule).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookClassNative.Nonattacking`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookClassNative.Nonattacking` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every two distinct cells in the subset, the second coordinates differ and the integer quotients of the first coordinates by m differ. Thus there is at most one rook in each column and in each bottom-aligned block of m rows. For m greater than one, individual row distinctness is insufficient.

**Definition 1.4 (Unlabeled placements).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookClassNative.placements`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookClassNative.placements` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filter the k-element subsets of the actual cells by Nonattacking. Each cell subset has weight one, independent of any ordering of its rooks.

**Definition 1.5 (Finite native rook numbers).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookClassNative.rookCount`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookClassNative.rookCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native rook number is the cardinality of placements, a finite subset enumeration. It is not defined from a root polynomial or from an assumed paper theorem.

**Theorem 1.6 (The empty placement).**

$$\forall m \in Nat,\; \forall b \in PositiveColumns,\; \operatorname{rookCount}\left(m, b, 0\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookClassNative.rookCount_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unique zero-element subset is empty and satisfies both conflict conditions.

**Theorem 1.7 (One rook counts the area).**

$$\forall m \in Nat,\; \forall b \in PositiveColumns,\; \operatorname{rookCount}\left(m, b, 1\right) = \operatorname{area}\left(b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookClassNative.rookCount_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every singleton cell subset is legal. Its count equals the sum of the source column heights via the existing normalization equivalence and Young-diagram area identity.

**Theorem 1.8 (Vanishing above the area).**

$$\forall m \in Nat,\; \forall b \in PositiveColumns,\; \forall k \in Nat,\; \operatorname{area}\left(b\right) < k \Rightarrow \operatorname{rookCount}\left(m, b, k\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookClassNative.rookCount_eq_zero_of_area_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No subset of the board has more cells than the area. This bound does not assume a width or singleton condition.

**Definition 1.9 (Every native rook number).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookClassNative.RookEquivalent`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookClassNative.RookEquivalent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two normalized shapes are equivalent exactly when their rookCount values agree for every natural k, including zero.

**Theorem 1.10 (A complete finite comparison).**

$$\forall m \in Nat,\; \forall a \in PositiveColumns,\; \forall b \in PositiveColumns,\; \operatorname{RookEquivalent}\left(m, a, b\right) \Leftrightarrow (\operatorname{area}\left(a\right) = \operatorname{area}\left(b\right) \land (\forall k \in Nat,\; \operatorname{mem}\left(k, \operatorname{Icc}\left(1, \operatorname{area}\left(b\right)\right)\right) \Rightarrow \operatorname{rookCount}\left(m, a, k\right) = \operatorname{rookCount}\left(m, b, k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookClassNative.rookEquivalent_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common area follows from the one-rook count. The positive indices through that area suffice: the zero index is one and every larger index is zero. Icc denotes the inclusive interval of natural indices.

**Definition 1.11 (The unrestricted native class).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookClassNative.RookClass`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookClassNative.RookClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The subtype contains every normalized positive-column shape with the same native rook numbers. Its definition imposes no width or height bound.

**Theorem 1.12 (Finiteness before cardinality conventions).**

$$\forall m \in Nat,\; \forall b \in PositiveColumns,\; \operatorname{Finite}\left(\operatorname{RookClass}\left(m, b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookClassNative.rookClass_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a cell with coordinates i and j, lower closure supplies i+1 cells in its column and j+1 in its row. Both coordinates are strictly below the area. Equal rook numbers force equal area. Sending a class member to its actual cells therefore embeds the entire class into the powerset of the area by area square. Finite is established without using Nat.card on an unproved finite carrier.

**Definition 1.13 (One fixed padding).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookClassNative.pad`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookClassNative.pad` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At length N, prepend N minus the positive-column length zero entries. This is the lower-right alignment convention.

**Theorem 1.14 (All registered common lengths).**

$$\forall m \in Nat,\; \forall b \in PositiveColumns,\; \forall n \in Nat,\; \operatorname{area}\left(b\right) + 1 \le n \Rightarrow \left(\forall a \in \operatorname{RookClass}\left(m, b\right),\; \operatorname{length}\left(\operatorname{columns}\left(a\right)\right) < n \land (\operatorname{length}\left(\operatorname{pad}\left(n, \operatorname{board}\left(a\right)\right)\right) = n \land (\operatorname{head}\left(\operatorname{pad}\left(n, \operatorname{board}\left(a\right)\right)\right) = \operatorname{some}\left(0\right) \land (\operatorname{sum}\left(\operatorname{pad}\left(n, \operatorname{board}\left(a\right)\right)\right) = \operatorname{area}\left(b\right))))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookClassNative.class_padding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every native class member and every N at least area(b)+1, its positive-column length is below N, its padding has length N, the head is zero, and the padded sum is area(b). The empty board and zero padding are included. In the formula, columns(a) is the underlying positive list of the class member, board(a) is that normalized shape, and head returns an Option natural.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassNative.Nonattacking`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassNative.RookClass`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassNative.RookEquivalent`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassNative.area`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassNative.cells`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassNative.class_padding`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassNative.pad`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassNative.placements`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassNative.rookClass_finite`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassNative.rookCount`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassNative.rookCount_eq_zero_of_area_lt`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassNative.rookCount_one`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassNative.rookCount_zero`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassNative.rookEquivalent_iff`
- Dependency: [D5/S3/Combinatorics/Partitions/BarreseSourceNormalization](BarreseSourceNormalization.md)
