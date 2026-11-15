# OEIS A233157

## Abstract

The number of labelled 4-row arrays obeys the order-3 recurrence from OEIS A233157.

**Definition 1.1 (U4).**

$$\forall n \in \operatorname{Nat},\; U_{4}\left(n\right) = Finset.card\left(Finset.filter\left((\lambda f: (Fin\left(4\right) \times Fin\left(n\right)) \to Fin\left(3\right) \mapsto (Legal\left(f\right))), \operatorname{Finset.univ}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.U4` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233157: 4-row three-state sum exclusion*. URL: <https://oeis.org/A233157>.

*Commentary.*

Every labelled function satisfying horizontal and antidiagonal sum exclusion is counted.

**Definition 1.2 (classes).**

$$\forall a \in Fin\left(3\right),\; \forall b \in Fin\left(3\right),\; \forall c \in Fin\left(3\right),\; \forall d \in Fin\left(3\right),\; classes\left(a, b, c, d\right) = HardinA233177PairTransfer.cls\left((a, (b, (c, d)))\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.classes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233157: 4-row three-state sum exclusion*. URL: <https://oeis.org/A233157>.

*Commentary.*

The existing first-appearance orbit index assigns the equality pattern.

**Definition 1.3 (classify).**

$$\forall r \in Row\left(4\right),\; classify\left(r\right) = classes\left(r\left(0\right), r\left(1\right), r\left(2\right), r\left(3\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.classify` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233157: 4-row three-state sum exclusion*. URL: <https://oeis.org/A233157>.

*Commentary.*

The coordinates select one of the 14 equality classes.

**Definition 1.4 (representatives).**

$$\forall i \in Fin\left(14\right),\; representatives\left(i\right) = HardinA233177PairTransfer.column\left(HardinA233177PairTransfer.representatives\left(i\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.representatives` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233157: 4-row three-state sum exclusion*. URL: <https://oeis.org/A233157>.

*Commentary.*

The existing representative tuple is read in row order.

**Definition 1.5 (quotient).**

$$(quotient: Matrix\left(Fin\left(14\right), Fin\left(14\right), \operatorname{Int}\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.quotient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233157: 4-row three-state sum exclusion*. URL: <https://oeis.org/A233157>.

*Commentary.*

The fixed 14 by 14 integer table records compatible successor multiplicities between equality classes.

**Definition 1.6 (weights).**

$$(weights: Fin\left(14\right) \to \operatorname{Int})$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.weights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233157: 4-row three-state sum exclusion*. URL: <https://oeis.org/A233157>.

*Commentary.*

The fixed 14-entry integer vector records three labelled constant columns in the constant class and six labelled columns in every other equality class.

**Theorem 1.7 (finite_certificate).**

$$(\forall r \in Row\left(4\right),\; \forall s \in Fin\left(14\right),\; \sum_{(c: Row\left(4\right))} \operatorname{if} (columnCompatible\left(r, c\right)) \land (classify\left(c\right) = s) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0 = quotient\left(classify\left(r\right), s\right)) \land ((\forall s \in Fin\left(14\right),\; \sum_{(c: Row\left(4\right))} \operatorname{if} classify\left(c\right) = s \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0 = weights\left(s\right)) \land (Matrix.mulVec\left((quotient)^{4 + 3}, (1: Fin\left(14\right) \to \operatorname{Int})\right) = \sum_{(j: Fin\left(3\right))} HSMul.hSMul\left(![6, -15, 9]\left(j\right), Matrix.mulVec\left((quotient)^{4 + Fin.val\left(j\right)}, (1: Fin\left(14\right) \to \operatorname{Int})\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233157: 4-row three-state sum exclusion*. URL: <https://oeis.org/A233157>.

*Commentary.*

The three identities specify the quotient, the initial class counts and the finite relation among matrix powers.

**Theorem 1.8 (result).**

$$\forall n \in \operatorname{Nat},\; (U_{4}\left(n + 8\right): \operatorname{Int}) = 9 \cdot (U_{4}\left(n + 7\right): \operatorname{Int}) - 15 \cdot (U_{4}\left(n + 6\right): \operatorname{Int}) + 6 \cdot (U_{4}\left(n + 5\right): \operatorname{Int})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233157` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233157","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233157: 4-row three-state sum exclusion*. URL: <https://oeis.org/A233157>.

*Commentary.*

Multiplication by every further matrix power extends the finite relation to all strip lengths in the displayed range.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.U4`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.classes`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.classify`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.quotient`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.representatives`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.weights`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer](HardinA233155ColumnTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer](HardinA233155RowTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer](HardinA233177PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
