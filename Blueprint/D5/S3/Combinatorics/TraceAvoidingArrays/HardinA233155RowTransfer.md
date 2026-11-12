# Three-state row transfer

## Abstract

Row sequences retain every labelled array and both kinds of excluded bond.

**Definition 1.1 (Row).**

$$\forall k \in \operatorname{Nat},\; Row\left(k\right) = \left(Fin\left(k\right) \to Fin\left(3\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233155: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233155>.

*Commentary.*

A row is a function from the columns to the three states.

**Definition 1.2 (rowLegal).**

$$\forall k \in \operatorname{Nat},\; \forall r \in Row\left(k\right),\; rowLegal\left(r\right) = \left(\forall j \in Fin\left(k\right),\; \forall h \in Fin.val\left(j\right) + 1 < k,\; Fin.val\left(r\left(j\right)\right) + Fin.val\left(r\left(\langle Fin.val\left(j\right) + 1, h\rangle\right)\right) \ne 2\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.rowLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233155: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233155>.

*Commentary.*

Each horizontal bond has sum different from two.

**Definition 1.3 (compatible).**

$$\forall k \in \operatorname{Nat},\; \forall r \in Row\left(k\right),\; \forall s \in Row\left(k\right),\; compatible\left(r, s\right) = \left(\forall j \in Fin\left(k\right),\; \forall h \in Fin.val\left(j\right) + 1 < k,\; Fin.val\left(r\left(\langle Fin.val\left(j\right) + 1, h\rangle\right)\right) + Fin.val\left(s\left(j\right)\right) \ne 2\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233155: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233155>.

*Commentary.*

The upper row's next entry and the lower row's current entry have sum different from two.

**Definition 1.4 (Legal).**

$$\forall k \in \operatorname{Nat},\; \forall n \in \operatorname{Nat},\; \forall f \in Fin\left(n\right) \times Fin\left(k\right) \to Fin\left(3\right),\; Legal\left(f\right) = \left((\forall i \in Fin\left(n\right),\; rowLegal\left((\lambda j: Fin\left(k\right) \mapsto (f\left((i, j)\right)))\right)) \land (\forall i \in Fin\left(n\right),\; \forall h \in Fin.val\left(i\right) + 1 < n,\; compatible\left((\lambda j: Fin\left(k\right) \mapsto (f\left((i, j)\right))), (\lambda j: Fin\left(k\right) \mapsto (f\left((\langle Fin.val\left(i\right) + 1, h\rangle, j)\right)))\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233155: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233155>.

*Commentary.*

Every row is legal and every consecutive pair is compatible.

**Definition 1.5 (T).**

$$\forall k \in \operatorname{Nat},\; \forall n \in \operatorname{Nat},\; T\left(k, n\right) = Finset.card\left(Finset.filter\left((\lambda f: Fin\left(n\right) \times Fin\left(k\right) \to Fin\left(3\right) \mapsto (Legal\left(f\right))), \operatorname{Finset.univ}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.T` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233155: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233155>.

*Commentary.*

The filtered finite set counts every function on the rectangle.

**Definition 1.6 (decode).**

$$\forall k \in \operatorname{Nat},\; \forall c \in Fin\left((3)^{k}\right),\; decode\left(k, c\right) = finFunctionFinEquiv.symm\left(c\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.decode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233155: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233155>.

*Commentary.*

Base-three codes enumerate all rows.

**Definition 1.7 (legalCodes).**

$$\forall k \in \operatorname{Nat},\; legalCodes\left(k\right) = List.filter\left((\lambda c: Fin\left((3)^{k}\right) \mapsto (decide\left(rowLegal\left(decode\left(k, c\right)\right)\right))), List.finRange\left((3)^{k}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.legalCodes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233155: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233155>.

*Commentary.*

Filtering the complete code list retains exactly the legal rows.

**Theorem 1.8 (row_sum).**

$$\forall k \in \operatorname{Nat},\; \forall F \in Row\left(k\right) \to \operatorname{Int},\; \sum_{(r: Row\left(k\right))} \operatorname{if} rowLegal\left(r\right) \operatorname{then} F\left(r\right) \operatorname{else} 0 = List.sum\left(List.map\left((\lambda c: Fin\left((3)^{k}\right) \mapsto (F\left(decode\left(k, c\right)\right))), legalCodes\left(k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.row_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233155: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233155>.

*Commentary.*

The sum over legal row functions equals the sum over their codes.

**Theorem 1.9 (row_sequence_bridge).**

$$\forall k \in \operatorname{Nat},\; \forall n \in \operatorname{Nat},\; T\left(k, n + 1\right) = Nat.card\left(\{r: Fin\left(n + 1\right) \to Row\left(k\right) \mid (\forall i \in Fin\left(n + 1\right),\; rowLegal\left(r\left(i\right)\right)) \land (\forall i \in Fin\left(n + 1\right),\; \forall h \in Fin.val\left(i\right) + 1 < n + 1,\; compatible\left(r\left(i\right), r\left(\langle Fin.val\left(i\right) + 1, h\rangle\right)\right))\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.row_sequence_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233155: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233155>.

*Commentary.*

Currying gives a bijection between literal arrays and row sequences with their local constraints.

**Theorem 1.10 (count_transfer).**

$$\forall k \in \operatorname{Nat},\; \forall q \in \operatorname{Nat},\; \forall cls \in Row\left(k\right) \to Fin\left(q\right),\; \forall Q \in Matrix\left(Fin\left(q\right), Fin\left(q\right), \operatorname{Int}\right),\; \forall w \in Fin\left(q\right) \to \operatorname{Int},\; (\forall r \in Row\left(k\right),\; (rowLegal\left(r\right)) \Rightarrow (\forall s \in Fin\left(q\right),\; \sum_{(c: Row\left(k\right))} \operatorname{if} (rowLegal\left(c\right)) \land ((compatible\left(r, c\right)) \land (cls\left(c\right) = s)) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0 = Q\left(cls\left(r\right), s\right))) \Rightarrow ((\forall s \in Fin\left(q\right),\; \sum_{(r: Row\left(k\right))} \operatorname{if} (rowLegal\left(r\right)) \land (cls\left(r\right) = s) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0 = w\left(s\right)) \Rightarrow (\forall n \in \operatorname{Nat},\; (T\left(k, n + 2\right): \operatorname{Int}) = dotProduct\left(w, Matrix.mulVec\left((Q)^{n + 1}, (1: Fin\left(q\right) \to \operatorname{Int})\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.count_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233155: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233155>.

*Commentary.*

Equal successor counts in each class give a matrix quotient. Initial class multiplicities and a matrix power count strips of every height at least two.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.Row`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.T`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.count_transfer`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.decode`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.legalCodes`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.rowLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.row_sequence_bridge`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.row_sum`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
