# OEIS A233158

## Abstract

The number of labelled 5-row arrays obeys the order-7 recurrence from OEIS A233158.

**Definition 1.1 (U5).**

$$\forall n \in \operatorname{Nat},\; U_{5}\left(n\right) = Finset.card\left(Finset.filter\left((\lambda f: (Fin\left(5\right) \times Fin\left(n\right)) \to Fin\left(3\right) \mapsto (Legal\left(f\right))), \operatorname{Finset.univ}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.U5` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233158: 5-row three-state sum exclusion*. URL: <https://oeis.org/A233158>.

*Commentary.*

Every labelled function satisfying horizontal and antidiagonal sum exclusion is counted.

**Definition 1.2 (classes).**

$$(classes: Fin\left(3\right) \to \left(Fin\left(3\right) \to \left(Fin\left(3\right) \to \left(Fin\left(3\right) \to \left(Fin\left(3\right) \to Fin\left(41\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.classes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233158: 5-row three-state sum exclusion*. URL: <https://oeis.org/A233158>.

*Commentary.*

The fixed lookup table assigns a class in Fin 41 to each tuple of 5 colors according to its equality pattern.

**Definition 1.3 (classify).**

$$\forall r \in Row\left(5\right),\; classify\left(r\right) = classes\left(r\left(0\right), r\left(1\right), r\left(2\right), r\left(3\right), r\left(4\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.classify` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233158: 5-row three-state sum exclusion*. URL: <https://oeis.org/A233158>.

*Commentary.*

The coordinates select one of the 41 equality classes.

**Definition 1.4 (representatives).**

$$(representatives: Fin\left(41\right) \to Row\left(5\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.representatives` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233158: 5-row three-state sum exclusion*. URL: <https://oeis.org/A233158>.

*Commentary.*

The fixed table selects one canonical 5-entry column for each of the 41 equality classes.

**Definition 1.5 (quotient).**

$$(quotient: Matrix\left(Fin\left(41\right), Fin\left(41\right), \operatorname{Int}\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.quotient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233158: 5-row three-state sum exclusion*. URL: <https://oeis.org/A233158>.

*Commentary.*

The fixed 41 by 41 integer table records compatible successor multiplicities between equality classes.

**Definition 1.6 (weights).**

$$(weights: Fin\left(41\right) \to \operatorname{Int})$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.weights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233158: 5-row three-state sum exclusion*. URL: <https://oeis.org/A233158>.

*Commentary.*

The fixed 41-entry integer vector records three labelled constant columns in the constant class and six labelled columns in every other equality class.

**Theorem 1.7 (finite_certificate).**

$$(\forall r \in Row\left(5\right),\; \forall s \in Fin\left(41\right),\; \sum_{(c: Row\left(5\right))} \operatorname{if} (columnCompatible\left(r, c\right)) \land (classify\left(c\right) = s) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0 = quotient\left(classify\left(r\right), s\right)) \land ((\forall s \in Fin\left(41\right),\; \sum_{(c: Row\left(5\right))} \operatorname{if} classify\left(c\right) = s \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0 = weights\left(s\right)) \land (Matrix.mulVec\left((quotient)^{4 + 7}, (1: Fin\left(41\right) \to \operatorname{Int})\right) = \sum_{(j: Fin\left(7\right))} HSMul.hSMul\left(![-8, 48, -84, 17, 76, -64, 16]\left(j\right), Matrix.mulVec\left((quotient)^{4 + Fin.val\left(j\right)}, (1: Fin\left(41\right) \to \operatorname{Int})\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233158: 5-row three-state sum exclusion*. URL: <https://oeis.org/A233158>.

*Commentary.*

The three identities specify the quotient, the initial class counts and the finite relation among matrix powers.

**Theorem 1.8 (result).**

$$\forall n \in \operatorname{Nat},\; (U_{5}\left(n + 12\right): \operatorname{Int}) = 16 \cdot (U_{5}\left(n + 11\right): \operatorname{Int}) - 64 \cdot (U_{5}\left(n + 10\right): \operatorname{Int}) + 76 \cdot (U_{5}\left(n + 9\right): \operatorname{Int}) + 17 \cdot (U_{5}\left(n + 8\right): \operatorname{Int}) - 84 \cdot (U_{5}\left(n + 7\right): \operatorname{Int}) + 48 \cdot (U_{5}\left(n + 6\right): \operatorname{Int}) - 8 \cdot (U_{5}\left(n + 5\right): \operatorname{Int})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233158: 5-row three-state sum exclusion*. URL: <https://oeis.org/A233158>.

*Commentary.*

Multiplication by every further matrix power extends the finite relation to all strip lengths in the displayed range.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.U5`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.classes`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.classify`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.quotient`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.representatives`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.weights`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer](HardinA233155ColumnTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer](HardinA233155RowTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
