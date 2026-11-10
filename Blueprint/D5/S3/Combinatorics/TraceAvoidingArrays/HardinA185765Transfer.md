# HardinA185765Transfer

## Abstract

Six-column binary arrays and Hardin's trace-avoidance recurrence.

**Definition 1.1 (The trace of a contiguous block).**

$$\forall (n : \mathbb{N}), \forall (A : \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(6\right), \operatorname{Fin}\left(2\right)\right)), \forall (i : \operatorname{Fin}\left(n\right)), \forall (j : \operatorname{Fin}\left(5\right)), \operatorname{blockTrace}\left(A, i, j\right) = \operatorname{Matrix.trace}\left((r : \operatorname{Fin}\left(2\right)) \mapsto (c : \operatorname{Fin}\left(2\right)) \mapsto \operatorname{val}\left(A\left(\operatorname{ite}\left(r = 0, \operatorname{Fin.castSucc}\left(i\right), \operatorname{Fin.succ}\left(i\right)\right), \operatorname{ite}\left(c = 0, \operatorname{Fin.castSucc}\left(j\right), \operatorname{Fin.succ}\left(j\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.blockTrace` (`✓ std3`).

*Citation.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

Number of (n+1)X6 binary arrays with no 2X2 subblock trace equal to any horizontal or vertical neighbor 2X2 subblock trace. NAME field, OEIS A185765 revision 9, without page numbering. The block at origin (i,j) uses rows i,i+1 and columns j,j+1. Its entries are cast to natural numbers before Matrix.trace.

**Definition 1.2 (Unequal neighboring traces).**

$$\forall (n : \mathbb{N}), \forall (A : \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(6\right), \operatorname{Fin}\left(2\right)\right)), (\operatorname{Admissible}\left(A\right)) \Leftrightarrow ((\forall (i : \operatorname{Fin}\left(n\right)), \forall (j : \operatorname{Fin}\left(5\right)), \forall (k : \operatorname{Fin}\left(5\right)), (\operatorname{val}\left(k\right) = \operatorname{val}\left(j\right) + 1) \Rightarrow (\operatorname{blockTrace}\left(A, i, j\right) \ne \operatorname{blockTrace}\left(A, i, k\right))) \land (\forall (i : \operatorname{Fin}\left(n\right)), \forall (h : \operatorname{Fin}\left(n\right)), \forall (j : \operatorname{Fin}\left(5\right)), (\operatorname{val}\left(h\right) = \operatorname{val}\left(i\right) + 1) \Rightarrow (\operatorname{blockTrace}\left(A, i, j\right) \ne \operatorname{blockTrace}\left(A, h, j\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.Admissible` (`✓ std3`).

*Citation.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

Number of (n+1)X6 binary arrays with no 2X2 subblock trace equal to any horizontal or vertical neighbor 2X2 subblock trace. NAME field, OEIS A185765 revision 9, without page numbering. Adjacent origins differ by one in exactly one coordinate. Arrays have open rectangular boundaries.

**Definition 1.3 (The cardinality of labeled arrays).**

$$\forall (n : \mathbb{N}), \operatorname{a}\left(n\right) = \operatorname{Nat.card}\left(\{A : \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(6\right), \operatorname{Fin}\left(2\right)\right) // \operatorname{Admissible}\left(A\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.a` (`✓ std3`).

*Citation.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

Number of (n+1)X6 binary arrays with no 2X2 subblock trace equal to any horizontal or vertical neighbor 2X2 subblock trace. NAME field, OEIS A185765 revision 9, without page numbering. The offset is 1,1. The subtype consists of all labeled admissible arrays; no symmetry quotient is taken.

**Definition 1.4 (Block traces in the row encoding).**

$$\forall (r : \operatorname{Fin}\left(64\right)), \forall (s : \operatorname{Fin}\left(64\right)), \forall (j : \operatorname{Fin}\left(5\right)), \operatorname{tau}\left(r, s, j\right) = \operatorname{blockTrace}\left(\operatorname{Fin.cons}\left(\operatorname{Equiv.symm}\left((finFunctionFinEquiv : \operatorname{Equiv}\left((\operatorname{Fin}\left(6\right)) \to (\operatorname{Fin}\left(2\right)), \operatorname{Fin}\left(64\right)\right))\right)\left(r\right), \operatorname{Fin.cons}\left(\operatorname{Equiv.symm}\left((finFunctionFinEquiv : \operatorname{Equiv}\left((\operatorname{Fin}\left(6\right)) \to (\operatorname{Fin}\left(2\right)), \operatorname{Fin}\left(64\right)\right))\right)\left(s\right), \operatorname{Fin.elim0}\right)\right), 0, j\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.tau` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

The finite equivalence finFunctionFinEquiv encodes each six-entry binary row by an element of Fin 64. The trace is blockTrace of the two decoded rows at row origin zero.

**Definition 1.5 (Horizontal comparisons).**

$$\forall (r : \operatorname{Fin}\left(64\right)), \forall (s : \operatorname{Fin}\left(64\right)), (\operatorname{H}\left(r, s\right)) \Leftrightarrow (\operatorname{Admissible}\left(\operatorname{Fin.cons}\left(\operatorname{Equiv.symm}\left((finFunctionFinEquiv : \operatorname{Equiv}\left((\operatorname{Fin}\left(6\right)) \to (\operatorname{Fin}\left(2\right)), \operatorname{Fin}\left(64\right)\right))\right)\left(r\right), \operatorname{Fin.cons}\left(\operatorname{Equiv.symm}\left((finFunctionFinEquiv : \operatorname{Equiv}\left((\operatorname{Fin}\left(6\right)) \to (\operatorname{Fin}\left(2\right)), \operatorname{Fin}\left(64\right)\right))\right)\left(s\right), \operatorname{Fin.elim0}\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.H` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

Admissible is applied to the two decoded rows. Its vertical condition is vacuous, and its horizontal condition compares the four adjacent block origins.

**Definition 1.6 (Vertical comparisons).**

$$\forall (r : \operatorname{Fin}\left(64\right)), \forall (s : \operatorname{Fin}\left(64\right)), \forall (t : \operatorname{Fin}\left(64\right)), (\operatorname{V}\left(r, s, t\right)) \Leftrightarrow (\forall (j : \operatorname{Fin}\left(5\right)), \operatorname{tau}\left(r, s, j\right) \ne \operatorname{tau}\left(s, t, j\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.V` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

The five traces in successive overlapping row pairs must differ coordinatewise.

**Definition 1.7 (One continuation step).**

$$\forall (v : (\operatorname{Fin}\left(64\right)) \to ((\operatorname{Fin}\left(64\right)) \to (\mathbb{Z}))), \forall (r : \operatorname{Fin}\left(64\right)), \forall (s : \operatorname{Fin}\left(64\right)), \operatorname{step}\left(v, r, s\right) = \operatorname{ite}\left(\operatorname{H}\left(r, s\right), \sum_{t : \operatorname{Fin}\left(64\right)} (\operatorname{ite}\left(\operatorname{V}\left(r, s, t\right), v\left(s, t\right), 0\right)), 0\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.step` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

A horizontally valid row pair sums the continuation values at each vertically compatible next row. Invalid row pairs have value zero.

**Definition 1.8 (Continuation counts).**

$$\forall (r : \operatorname{Fin}\left(64\right)), \forall (s : \operatorname{Fin}\left(64\right)), (\operatorname{u}\left(0, r, s\right) = \operatorname{ite}\left(\operatorname{H}\left(r, s\right), 1, 0\right)) \land (\forall (k : \mathbb{N}), \operatorname{u}\left(k + 1, r, s\right) = \operatorname{step}\left(\operatorname{u}\left(k\right), r, s\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.u` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

The initial vector is one on horizontally valid pairs and zero elsewhere. Each further vector applies step.

**Theorem 1.9 (Literal arrays and continuation counts).**

$$\forall (k : \mathbb{N}), (\operatorname{a}\left(k + 1\right) : \mathbb{Z}) = \sum_{r : \operatorname{Fin}\left(64\right)} (\sum_{s : \operatorname{Fin}\left(64\right)} (\operatorname{u}\left(k, r, s\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.counting_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

Encoding rows and splitting their finite function space at its first two entries gives this identity. Induction on the remaining rows identifies the finite sum with u.

**Definition 1.10 (The fifteen integer tables).**

$$tables : \operatorname{Array}\left(\operatorname{Array}\left(\operatorname{Array}\left(\mathbb{Z}\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.tables` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

The literal array stores fifteen 64 by 64 integer tables, in order from continuation length zero through fourteen. Rows and columns use finFunctionFinEquiv. Entries outside horizontally valid row pairs are zero. The initial table gives horizontal compatibility, and fourteen transitions give the successive continuation counts.

**Definition 1.11 (The successor lists).**

$$adjData : \operatorname{Array}\left(\operatorname{Array}\left(\operatorname{List}\left(\operatorname{Fin}\left(64\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.adjData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

This literal 64 by 64 array of lists records successor rows. A list at a horizontally valid pair contains exactly the rows satisfying the horizontal and vertical comparisons for the next pair.

**Definition 1.12 (Sparse continuation step).**

$$\forall (v : (\operatorname{Fin}\left(64\right)) \to ((\operatorname{Fin}\left(64\right)) \to (\mathbb{Z}))), \forall (r : \operatorname{Fin}\left(64\right)), \forall (s : \operatorname{Fin}\left(64\right)), \operatorname{fastStep}\left(v, r, s\right) = \operatorname{ite}\left(\operatorname{H}\left(r, s\right), \sum_{t \in \operatorname{List.toFinset}\left(((adjData)[\operatorname{val}\left(r\right)]!)[\operatorname{val}\left(s\right)]!\right)} (v\left(s, t\right)), 0\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.fastStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

The sparse sum uses the finite successor set in place of testing all 64 rows.

**Definition 1.13 (Table entries on valid row pairs).**

$$\forall (k : \mathbb{N}), \forall (r : \operatorname{Fin}\left(64\right)), \forall (s : \operatorname{Fin}\left(64\right)), \operatorname{table}\left(k, r, s\right) = \operatorname{ite}\left(\operatorname{H}\left(r, s\right), (((tables)[k]!)[\operatorname{val}\left(r\right)]!)[\operatorname{val}\left(s\right)]!, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

The table at k has the entries of the kth literal integer array on H and is zero elsewhere. Each exclamation-mark array index uses Lean default-value indexing.

**Theorem 1.14 (The sparse transfer evaluated from the integer data).**

$$\forall (k : \mathbb{N}), \forall (r : \operatorname{Fin}\left(64\right)), \forall (s : \operatorname{Fin}\left(64\right)), \operatorname{fastStep}\left(\operatorname{table}\left(k\right), r, s\right) = \operatorname{ite}\left(\operatorname{H}\left(r, s\right), \sum_{t \in \operatorname{List.toFinset}\left(((adjData)[\operatorname{val}\left(r\right)]!)[\operatorname{val}\left(s\right)]!\right)} ((((tables)[k]!)[\operatorname{val}\left(s\right)]!)[\operatorname{val}\left(t\right)]!), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.fastStep_table_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

Every successor satisfies the horizontal comparisons, so its guarded table entry equals the corresponding integer entry.

**Theorem 1.15 (The initial table).**

$$\forall (r : \operatorname{Fin}\left(64\right)), \forall (s : \operatorname{Fin}\left(64\right)), \operatorname{u}\left(0, r, s\right) = \operatorname{table}\left(0, r, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table_base` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

The zeroth table agrees with the initial continuation vector at every row pair.

**Theorem 1.16 (Sparse evaluation of a table).**

$$\forall (k : \mathbb{N}), \operatorname{step}\left(\operatorname{table}\left(k\right)\right) = \operatorname{fastStep}\left(\operatorname{table}\left(k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.step_table_fast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

Each table vanishes outside H, so its two transfer steps agree.

**Theorem 1.17 (The transfer from table 0 to 1).**

$$\forall (r : \operatorname{Fin}\left(64\right)), \forall (s : \operatorname{Fin}\left(64\right)), \operatorname{step}\left(\operatorname{table}\left(0\right), r, s\right) = \operatorname{table}\left(1, r, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table_step_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

At every row pair, the transfer of the table at 0 equals the table at 1.

**Theorem 1.18 (The transfer from table 1 to 2).**

$$\forall (r : \operatorname{Fin}\left(64\right)), \forall (s : \operatorname{Fin}\left(64\right)), \operatorname{step}\left(\operatorname{table}\left(1\right), r, s\right) = \operatorname{table}\left(2, r, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table_step_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

At every row pair, the transfer of the table at 1 equals the table at 2.

**Theorem 1.19 (The transfer from table 2 to 3).**

$$\forall (r : \operatorname{Fin}\left(64\right)), \forall (s : \operatorname{Fin}\left(64\right)), \operatorname{step}\left(\operatorname{table}\left(2\right), r, s\right) = \operatorname{table}\left(3, r, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table_step_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

At every row pair, the transfer of the table at 2 equals the table at 3.

**Theorem 1.20 (The transfer from table 3 to 4).**

$$\forall (r : \operatorname{Fin}\left(64\right)), \forall (s : \operatorname{Fin}\left(64\right)), \operatorname{step}\left(\operatorname{table}\left(3\right), r, s\right) = \operatorname{table}\left(4, r, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table_step_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

At every row pair, the transfer of the table at 3 equals the table at 4.

**Theorem 1.21 (The transfer from table 4 to 5).**

$$\forall (r : \operatorname{Fin}\left(64\right)), \forall (s : \operatorname{Fin}\left(64\right)), \operatorname{step}\left(\operatorname{table}\left(4\right), r, s\right) = \operatorname{table}\left(5, r, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table_step_4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

At every row pair, the transfer of the table at 4 equals the table at 5.

**Theorem 1.22 (The transfer from table 11 to 12).**

$$\forall (r : \operatorname{Fin}\left(64\right)), \forall (s : \operatorname{Fin}\left(64\right)), \operatorname{step}\left(\operatorname{table}\left(11\right), r, s\right) = \operatorname{table}\left(12, r, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table_step_11` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

At every row pair, the transfer of the table at 11 equals the table at 12.

**Theorem 1.23 (The transfer from table 12 to 13).**

$$\forall (r : \operatorname{Fin}\left(64\right)), \forall (s : \operatorname{Fin}\left(64\right)), \operatorname{step}\left(\operatorname{table}\left(12\right), r, s\right) = \operatorname{table}\left(13, r, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table_step_12` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

At every row pair, the transfer of the table at 12 equals the table at 13.

**Theorem 1.24 (The transfer from table 13 to 14).**

$$\forall (r : \operatorname{Fin}\left(64\right)), \forall (s : \operatorname{Fin}\left(64\right)), \operatorname{step}\left(\operatorname{table}\left(13\right), r, s\right) = \operatorname{table}\left(14, r, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table_step_13` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

At every row pair, the transfer of the table at 13 equals the table at 14.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.Admissible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.H`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.V`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.adjData`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.blockTrace`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.counting_bridge`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.fastStep`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.fastStep_table_data`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.step`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.step_table_fast`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table_base`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table_step_0`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table_step_1`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table_step_11`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table_step_12`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table_step_13`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table_step_2`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table_step_3`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.table_step_4`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.tables`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.tau`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.u`
