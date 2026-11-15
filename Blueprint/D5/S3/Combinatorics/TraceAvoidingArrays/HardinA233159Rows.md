# OEIS A233159

## Abstract

Equality patterns and their quotient determine labelled six-row strip counts.

**Definition 1.1 (U6).**

$$\forall n \in \operatorname{Nat},\; U_{6}\left(n\right) = Finset.card\left(Finset.filter\left((\lambda f: (Fin\left(6\right) \times Fin\left(n\right)) \to Fin\left(3\right) \mapsto (Legal\left(f\right))), \operatorname{Finset.univ}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.U6` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233159: 6-row three-state sum exclusion*. URL: <https://oeis.org/A233159>.

*Commentary.*

Every labelled function satisfying horizontal and antidiagonal sum exclusion is counted.

**Definition 1.2 (classes).**

$$\forall a \in Fin\left(3\right),\; \forall b \in Fin\left(3\right),\; \forall c \in Fin\left(3\right),\; \forall d \in Fin\left(3\right),\; \forall e \in Fin\left(3\right),\; \forall f \in Fin\left(3\right),\; classes\left(a, b, c, d, e, f\right) = HardinA233179PairTransfer.orbit\left((a, (b, (c, (d, (e, f)))))\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.classes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233159: 6-row three-state sum exclusion*. URL: <https://oeis.org/A233159>.

*Commentary.*

The existing first-appearance orbit index assigns the equality pattern.

**Definition 1.3 (classify).**

$$\forall r \in Row\left(6\right),\; classify\left(r\right) = classes\left(r\left(0\right), r\left(1\right), r\left(2\right), r\left(3\right), r\left(4\right), r\left(5\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.classify` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233159: 6-row three-state sum exclusion*. URL: <https://oeis.org/A233159>.

*Commentary.*

The coordinates select one of the 122 equality classes.

**Definition 1.4 (representatives).**

$$\forall i \in Fin\left(122\right),\; representatives\left(i\right) = HardinA233179PairTransfer.column\left(HardinA233179PairTransfer.representatives\left(i\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.representatives` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233159: 6-row three-state sum exclusion*. URL: <https://oeis.org/A233159>.

*Commentary.*

The existing representative tuple is read in row order.

**Definition 1.5 (quotient).**

$$\forall i \in Fin\left(122\right),\; \forall s \in Fin\left(122\right),\; quotient\left(i, s\right) = List.sum\left(List.map\left((\lambda j: Fin\left(122\right) \mapsto (\operatorname{if} j = s \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0)), successors\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.quotient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233159: 6-row three-state sum exclusion*. URL: <https://oeis.org/A233159>.

*Commentary.*

The quotient entry is the multiplicity of a class in the successor list.

**Definition 1.6 (weights).**

$$(weights: Fin\left(122\right) \to \operatorname{Int})$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.weights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233159: 6-row three-state sum exclusion*. URL: <https://oeis.org/A233159>.

*Commentary.*

The fixed 122-entry integer vector records three labelled constant columns in the constant class and six labelled columns in every other equality class.

**Definition 1.7 (successors).**

$$(successors: Fin\left(122\right) \to List\left(Fin\left(122\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.successors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233159: 6-row three-state sum exclusion*. URL: <https://oeis.org/A233159>.

*Commentary.*

The fixed table assigns each of the 122 representatives its list of compatible successor classes in base-three code order, retaining multiplicities.

**Theorem 1.8 (equality_classes).**

$$(\forall e \in Equiv.Perm\left(Fin\left(3\right)\right),\; \forall r \in Row\left(6\right),\; classify\left(relabel\left(e, r\right)\right) = classify\left(r\right)) \land (\forall r \in Row\left(6\right),\; \exists e \in Equiv.Perm\left(Fin\left(3\right)\right),\; relabel\left(e, r\right) = representatives\left(classify\left(r\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.equality_classes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233159: 6-row three-state sum exclusion*. URL: <https://oeis.org/A233159>.

*Commentary.*

Color permutations preserve the equality class and carry each column to its representative.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.U6`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.classes`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.classify`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.equality_classes`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.quotient`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.representatives`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.successors`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.weights`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer](HardinA233155ColumnTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer](HardinA233155RowTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer](HardinA233179PairTransfer.md)
