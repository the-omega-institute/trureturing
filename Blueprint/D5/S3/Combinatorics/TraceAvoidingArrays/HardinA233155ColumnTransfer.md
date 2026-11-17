# Three-state column transfer

## Abstract

Unrestricted columns retain the literal horizontal and antidiagonal bonds.

**Definition 1.1 (columnCompatible).**

$$\forall k \in \operatorname{Nat},\; \forall r \in Row\left(k\right),\; \forall s \in Row\left(k\right),\; columnCompatible\left(r, s\right) = \left((\forall i \in Fin\left(k\right),\; Fin.val\left(r\left(i\right)\right) + Fin.val\left(s\left(i\right)\right) \ne 2) \land (\forall i \in Fin\left(k\right),\; \forall h \in Fin.val\left(i\right) + 1 < k,\; Fin.val\left(s\left(i\right)\right) + Fin.val\left(r\left(\langle Fin.val\left(i\right) + 1, h\rangle\right)\right) \ne 2)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer.columnCompatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233155: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233155>.

*Commentary.*

Every horizontal and antidiagonal bond between the two columns excludes sum two.

**Definition 1.2 (relabel).**

$$\forall k \in \operatorname{Nat},\; \forall e \in Equiv.Perm\left(Fin\left(3\right)\right),\; relabel\left(e\right) = Equiv.arrowCongr\left(Equiv.refl\left(Fin\left(k\right)\right), e\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer.relabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233155: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233155>.

*Commentary.*

A color permutation acts pointwise on a column.

**Definition 1.3 (properEquiv).**

$$\forall k \in \operatorname{Nat},\; \forall n \in \operatorname{Nat},\; (properEquiv\left(k, n\right): Equiv\left(Subtype\left((\lambda f: (Fin\left(k\right) \times Fin\left(n\right)) \to Fin\left(3\right) \mapsto (Legal\left(f\right)))\right), Subtype\left((\lambda P: (Fin\left(k\right) \times Fin\left(n\right)) \to Fin\left(3\right) \mapsto (\forall j \in Fin\left(n\right),\; \forall h \in Fin.val\left(j\right) + 1 < n,\; \forall r \in Fin\left(k\right),\; \forall s \in Fin\left(k\right),\; ((r = s) \lor (Fin.val\left(r\right) = Fin.val\left(s\right) + 1)) \Rightarrow (P\left((r, j)\right) \ne P\left((s, \langle Fin.val\left(j\right) + 1, h\rangle)\right))))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer.properEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233155: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233155>.

*Commentary.*

Let c be Fin.revPerm on Fin 3, with values [2,1,0]. Applying c to the power j at every cell in column j gives an equivalence from all labelled sum-exclusion arrays to proper colourings. Injectivity cancels the common power at the ends of each bond; x differs from c(y) exactly when the two natural values have sum different from two. The inverse applies the inverse permutation separately at every cell. Empty dimensions are included.

**Definition 1.4 (successorClasses).**

$$\forall k \in \operatorname{Nat},\; \forall q \in \operatorname{Nat},\; \forall cls \in Row\left(k\right) \to Fin\left(q\right),\; \forall r \in Row\left(k\right),\; successorClasses\left(cls, r\right) = List.map\left((\lambda c: Fin\left((3)^{k}\right) \mapsto (cls\left(decode\left(k, c\right)\right))), List.filter\left((\lambda c: Fin\left((3)^{k}\right) \mapsto (decide\left(columnCompatible\left(r, decode\left(k, c\right)\right)\right))), List.finRange\left((3)^{k}\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer.successorClasses` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233155: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233155>.

*Commentary.*

The list records each compatible successor class in base-three code order.

**Theorem 1.5 (quotient_rows).**

$$\forall k \in \operatorname{Nat},\; \forall q \in \operatorname{Nat},\; \forall cls \in Row\left(k\right) \to Fin\left(q\right),\; \forall rep \in Fin\left(q\right) \to Row\left(k\right),\; \forall Q \in Matrix\left(Fin\left(q\right), Fin\left(q\right), \operatorname{Int}\right),\; (\forall e \in Equiv.Perm\left(Fin\left(3\right)\right),\; \forall r \in Row\left(k\right),\; cls\left(relabel\left(e, r\right)\right) = cls\left(r\right)) \Rightarrow ((\forall r \in Row\left(k\right),\; \exists e \in Equiv.Perm\left(Fin\left(3\right)\right),\; relabel\left(e, r\right) = rep\left(cls\left(r\right)\right)) \Rightarrow ((\forall i \in Fin\left(q\right),\; \forall s \in Fin\left(q\right),\; List.sum\left(List.map\left((\lambda j: Fin\left(q\right) \mapsto (\operatorname{if} j = s \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0)), successorClasses\left(cls, rep\left(i\right)\right)\right)\right) = Q\left(i, s\right)) \Rightarrow (\forall r \in Row\left(k\right),\; \forall s \in Fin\left(q\right),\; \sum_{(c: Row\left(k\right))} \operatorname{if} (columnCompatible\left(r, c\right)) \land (cls\left(c\right) = s) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0 = Q\left(cls\left(r\right), s\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer.quotient_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233155: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233155>.

*Commentary.*

Permutation-invariant equality classes and their representative successor lists determine all quotient entries.

**Theorem 1.6 (count_transfer).**

$$\forall k \in \operatorname{Nat},\; \forall q \in \operatorname{Nat},\; \forall cls \in Row\left(k\right) \to Fin\left(q\right),\; \forall Q \in Matrix\left(Fin\left(q\right), Fin\left(q\right), \operatorname{Int}\right),\; \forall w \in Fin\left(q\right) \to \operatorname{Int},\; (\forall r \in Row\left(k\right),\; \forall s \in Fin\left(q\right),\; \sum_{(c: Row\left(k\right))} \operatorname{if} (columnCompatible\left(r, c\right)) \land (cls\left(c\right) = s) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0 = Q\left(cls\left(r\right), s\right)) \Rightarrow ((\forall s \in Fin\left(q\right),\; \sum_{(r: Row\left(k\right))} \operatorname{if} cls\left(r\right) = s \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0 = w\left(s\right)) \Rightarrow (\forall n \in \operatorname{Nat},\; (T\left(n + 2, k\right): \operatorname{Int}) = dotProduct\left(w, Matrix.mulVec\left((Q)^{n + 1}, (1: Fin\left(q\right) \to \operatorname{Int})\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer.count_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233155: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233155>.

*Commentary.*

Currying along columns identifies literal arrays with constrained words. The quotient and its initial multiplicities count every length at least two.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer.columnCompatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer.count_transfer`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer.properEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer.quotient_rows`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer.relabel`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer.successorClasses`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer](HardinA233155RowTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
