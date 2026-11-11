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

$$\forall a \in Fin\left(3\right),\; \forall b \in Fin\left(3\right),\; \forall c \in Fin\left(3\right),\; \forall d \in Fin\left(3\right),\; \forall e \in Fin\left(3\right),\; \forall f \in Fin\left(3\right),\; classes\left(a, b, c, d, e, f\right) = \operatorname{if} b = a \operatorname{then} \operatorname{if} c = a \operatorname{then} \operatorname{if} d = a \operatorname{then} \operatorname{if} e = a \operatorname{then} \operatorname{if} f = a \operatorname{then} 0 \operatorname{else} 1 \operatorname{else} \operatorname{if} f = a \operatorname{then} 2 \operatorname{else} \operatorname{if} f = e \operatorname{then} 3 \operatorname{else} 4 \operatorname{else} \operatorname{if} e = a \operatorname{then} \operatorname{if} f = a \operatorname{then} 5 \operatorname{else} \operatorname{if} f = d \operatorname{then} 6 \operatorname{else} 7 \operatorname{else} \operatorname{if} e = d \operatorname{then} \operatorname{if} f = a \operatorname{then} 8 \operatorname{else} \operatorname{if} f = d \operatorname{then} 9 \operatorname{else} 10 \operatorname{else} \operatorname{if} f = a \operatorname{then} 11 \operatorname{else} \operatorname{if} f = d \operatorname{then} 12 \operatorname{else} 13 \operatorname{else} \operatorname{if} d = a \operatorname{then} \operatorname{if} e = a \operatorname{then} \operatorname{if} f = a \operatorname{then} 14 \operatorname{else} \operatorname{if} f = c \operatorname{then} 15 \operatorname{else} 16 \operatorname{else} \operatorname{if} e = c \operatorname{then} \operatorname{if} f = a \operatorname{then} 17 \operatorname{else} \operatorname{if} f = c \operatorname{then} 18 \operatorname{else} 19 \operatorname{else} \operatorname{if} f = a \operatorname{then} 20 \operatorname{else} \operatorname{if} f = c \operatorname{then} 21 \operatorname{else} 22 \operatorname{else} \operatorname{if} d = c \operatorname{then} \operatorname{if} e = a \operatorname{then} \operatorname{if} f = a \operatorname{then} 23 \operatorname{else} \operatorname{if} f = c \operatorname{then} 24 \operatorname{else} 25 \operatorname{else} \operatorname{if} e = c \operatorname{then} \operatorname{if} f = a \operatorname{then} 26 \operatorname{else} \operatorname{if} f = c \operatorname{then} 27 \operatorname{else} 28 \operatorname{else} \operatorname{if} f = a \operatorname{then} 29 \operatorname{else} \operatorname{if} f = c \operatorname{then} 30 \operatorname{else} 31 \operatorname{else} \operatorname{if} e = a \operatorname{then} \operatorname{if} f = a \operatorname{then} 32 \operatorname{else} \operatorname{if} f = c \operatorname{then} 33 \operatorname{else} 34 \operatorname{else} \operatorname{if} e = c \operatorname{then} \operatorname{if} f = a \operatorname{then} 35 \operatorname{else} \operatorname{if} f = c \operatorname{then} 36 \operatorname{else} 37 \operatorname{else} \operatorname{if} f = a \operatorname{then} 38 \operatorname{else} \operatorname{if} f = c \operatorname{then} 39 \operatorname{else} 40 \operatorname{else} \operatorname{if} c = a \operatorname{then} \operatorname{if} d = a \operatorname{then} \operatorname{if} e = a \operatorname{then} \operatorname{if} f = a \operatorname{then} 41 \operatorname{else} \operatorname{if} f = b \operatorname{then} 42 \operatorname{else} 43 \operatorname{else} \operatorname{if} e = b \operatorname{then} \operatorname{if} f = a \operatorname{then} 44 \operatorname{else} \operatorname{if} f = b \operatorname{then} 45 \operatorname{else} 46 \operatorname{else} \operatorname{if} f = a \operatorname{then} 47 \operatorname{else} \operatorname{if} f = b \operatorname{then} 48 \operatorname{else} 49 \operatorname{else} \operatorname{if} d = b \operatorname{then} \operatorname{if} e = a \operatorname{then} \operatorname{if} f = a \operatorname{then} 50 \operatorname{else} \operatorname{if} f = b \operatorname{then} 51 \operatorname{else} 52 \operatorname{else} \operatorname{if} e = b \operatorname{then} \operatorname{if} f = a \operatorname{then} 53 \operatorname{else} \operatorname{if} f = b \operatorname{then} 54 \operatorname{else} 55 \operatorname{else} \operatorname{if} f = a \operatorname{then} 56 \operatorname{else} \operatorname{if} f = b \operatorname{then} 57 \operatorname{else} 58 \operatorname{else} \operatorname{if} e = a \operatorname{then} \operatorname{if} f = a \operatorname{then} 59 \operatorname{else} \operatorname{if} f = b \operatorname{then} 60 \operatorname{else} 61 \operatorname{else} \operatorname{if} e = b \operatorname{then} \operatorname{if} f = a \operatorname{then} 62 \operatorname{else} \operatorname{if} f = b \operatorname{then} 63 \operatorname{else} 64 \operatorname{else} \operatorname{if} f = a \operatorname{then} 65 \operatorname{else} \operatorname{if} f = b \operatorname{then} 66 \operatorname{else} 67 \operatorname{else} \operatorname{if} c = b \operatorname{then} \operatorname{if} d = a \operatorname{then} \operatorname{if} e = a \operatorname{then} \operatorname{if} f = a \operatorname{then} 68 \operatorname{else} \operatorname{if} f = b \operatorname{then} 69 \operatorname{else} 70 \operatorname{else} \operatorname{if} e = b \operatorname{then} \operatorname{if} f = a \operatorname{then} 71 \operatorname{else} \operatorname{if} f = b \operatorname{then} 72 \operatorname{else} 73 \operatorname{else} \operatorname{if} f = a \operatorname{then} 74 \operatorname{else} \operatorname{if} f = b \operatorname{then} 75 \operatorname{else} 76 \operatorname{else} \operatorname{if} d = b \operatorname{then} \operatorname{if} e = a \operatorname{then} \operatorname{if} f = a \operatorname{then} 77 \operatorname{else} \operatorname{if} f = b \operatorname{then} 78 \operatorname{else} 79 \operatorname{else} \operatorname{if} e = b \operatorname{then} \operatorname{if} f = a \operatorname{then} 80 \operatorname{else} \operatorname{if} f = b \operatorname{then} 81 \operatorname{else} 82 \operatorname{else} \operatorname{if} f = a \operatorname{then} 83 \operatorname{else} \operatorname{if} f = b \operatorname{then} 84 \operatorname{else} 85 \operatorname{else} \operatorname{if} e = a \operatorname{then} \operatorname{if} f = a \operatorname{then} 86 \operatorname{else} \operatorname{if} f = b \operatorname{then} 87 \operatorname{else} 88 \operatorname{else} \operatorname{if} e = b \operatorname{then} \operatorname{if} f = a \operatorname{then} 89 \operatorname{else} \operatorname{if} f = b \operatorname{then} 90 \operatorname{else} 91 \operatorname{else} \operatorname{if} f = a \operatorname{then} 92 \operatorname{else} \operatorname{if} f = b \operatorname{then} 93 \operatorname{else} 94 \operatorname{else} \operatorname{if} d = a \operatorname{then} \operatorname{if} e = a \operatorname{then} \operatorname{if} f = a \operatorname{then} 95 \operatorname{else} \operatorname{if} f = b \operatorname{then} 96 \operatorname{else} 97 \operatorname{else} \operatorname{if} e = b \operatorname{then} \operatorname{if} f = a \operatorname{then} 98 \operatorname{else} \operatorname{if} f = b \operatorname{then} 99 \operatorname{else} 100 \operatorname{else} \operatorname{if} f = a \operatorname{then} 101 \operatorname{else} \operatorname{if} f = b \operatorname{then} 102 \operatorname{else} 103 \operatorname{else} \operatorname{if} d = b \operatorname{then} \operatorname{if} e = a \operatorname{then} \operatorname{if} f = a \operatorname{then} 104 \operatorname{else} \operatorname{if} f = b \operatorname{then} 105 \operatorname{else} 106 \operatorname{else} \operatorname{if} e = b \operatorname{then} \operatorname{if} f = a \operatorname{then} 107 \operatorname{else} \operatorname{if} f = b \operatorname{then} 108 \operatorname{else} 109 \operatorname{else} \operatorname{if} f = a \operatorname{then} 110 \operatorname{else} \operatorname{if} f = b \operatorname{then} 111 \operatorname{else} 112 \operatorname{else} \operatorname{if} e = a \operatorname{then} \operatorname{if} f = a \operatorname{then} 113 \operatorname{else} \operatorname{if} f = b \operatorname{then} 114 \operatorname{else} 115 \operatorname{else} \operatorname{if} e = b \operatorname{then} \operatorname{if} f = a \operatorname{then} 116 \operatorname{else} \operatorname{if} f = b \operatorname{then} 117 \operatorname{else} 118 \operatorname{else} \operatorname{if} f = a \operatorname{then} 119 \operatorname{else} \operatorname{if} f = b \operatorname{then} 120 \operatorname{else} 121$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.classes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233159: 6-row three-state sum exclusion*. URL: <https://oeis.org/A233159>.

*Commentary.*

The equality tests assign one class to each column pattern.

**Definition 1.3 (classify).**

$$\forall r \in Row\left(6\right),\; classify\left(r\right) = classes\left(r\left(0\right), r\left(1\right), r\left(2\right), r\left(3\right), r\left(4\right), r\left(5\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.classify` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233159: 6-row three-state sum exclusion*. URL: <https://oeis.org/A233159>.

*Commentary.*

The coordinates select one of the 122 equality classes.

**Definition 1.4 (representatives).**

$$(representatives: Fin\left(122\right) \to Row\left(6\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.representatives` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233159: 6-row three-state sum exclusion*. URL: <https://oeis.org/A233159>.

*Commentary.*

The fixed table selects one canonical 6-entry column for each of the 122 equality classes.

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
