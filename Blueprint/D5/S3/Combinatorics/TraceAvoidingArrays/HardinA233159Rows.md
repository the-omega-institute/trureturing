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

$$representatives = ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 1], ![0, 0, 0, 1, 0, 2], ![0, 0, 0, 1, 1, 0], ![0, 0, 0, 1, 1, 1], ![0, 0, 0, 1, 1, 2], ![0, 0, 0, 1, 2, 0], ![0, 0, 0, 1, 2, 1], ![0, 0, 0, 1, 2, 2], ![0, 0, 1, 0, 0, 0], ![0, 0, 1, 0, 0, 1], ![0, 0, 1, 0, 0, 2], ![0, 0, 1, 0, 1, 0], ![0, 0, 1, 0, 1, 1], ![0, 0, 1, 0, 1, 2], ![0, 0, 1, 0, 2, 0], ![0, 0, 1, 0, 2, 1], ![0, 0, 1, 0, 2, 2], ![0, 0, 1, 1, 0, 0], ![0, 0, 1, 1, 0, 1], ![0, 0, 1, 1, 0, 2], ![0, 0, 1, 1, 1, 0], ![0, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 2], ![0, 0, 1, 1, 2, 0], ![0, 0, 1, 1, 2, 1], ![0, 0, 1, 1, 2, 2], ![0, 0, 1, 2, 0, 0], ![0, 0, 1, 2, 0, 1], ![0, 0, 1, 2, 0, 2], ![0, 0, 1, 2, 1, 0], ![0, 0, 1, 2, 1, 1], ![0, 0, 1, 2, 1, 2], ![0, 0, 1, 2, 2, 0], ![0, 0, 1, 2, 2, 1], ![0, 0, 1, 2, 2, 2], ![0, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 2], ![0, 1, 0, 0, 1, 0], ![0, 1, 0, 0, 1, 1], ![0, 1, 0, 0, 1, 2], ![0, 1, 0, 0, 2, 0], ![0, 1, 0, 0, 2, 1], ![0, 1, 0, 0, 2, 2], ![0, 1, 0, 1, 0, 0], ![0, 1, 0, 1, 0, 1], ![0, 1, 0, 1, 0, 2], ![0, 1, 0, 1, 1, 0], ![0, 1, 0, 1, 1, 1], ![0, 1, 0, 1, 1, 2], ![0, 1, 0, 1, 2, 0], ![0, 1, 0, 1, 2, 1], ![0, 1, 0, 1, 2, 2], ![0, 1, 0, 2, 0, 0], ![0, 1, 0, 2, 0, 1], ![0, 1, 0, 2, 0, 2], ![0, 1, 0, 2, 1, 0], ![0, 1, 0, 2, 1, 1], ![0, 1, 0, 2, 1, 2], ![0, 1, 0, 2, 2, 0], ![0, 1, 0, 2, 2, 1], ![0, 1, 0, 2, 2, 2], ![0, 1, 1, 0, 0, 0], ![0, 1, 1, 0, 0, 1], ![0, 1, 1, 0, 0, 2], ![0, 1, 1, 0, 1, 0], ![0, 1, 1, 0, 1, 1], ![0, 1, 1, 0, 1, 2], ![0, 1, 1, 0, 2, 0], ![0, 1, 1, 0, 2, 1], ![0, 1, 1, 0, 2, 2], ![0, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 0, 1], ![0, 1, 1, 1, 0, 2], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 1], ![0, 1, 1, 1, 1, 2], ![0, 1, 1, 1, 2, 0], ![0, 1, 1, 1, 2, 1], ![0, 1, 1, 1, 2, 2], ![0, 1, 1, 2, 0, 0], ![0, 1, 1, 2, 0, 1], ![0, 1, 1, 2, 0, 2], ![0, 1, 1, 2, 1, 0], ![0, 1, 1, 2, 1, 1], ![0, 1, 1, 2, 1, 2], ![0, 1, 1, 2, 2, 0], ![0, 1, 1, 2, 2, 1], ![0, 1, 1, 2, 2, 2], ![0, 1, 2, 0, 0, 0], ![0, 1, 2, 0, 0, 1], ![0, 1, 2, 0, 0, 2], ![0, 1, 2, 0, 1, 0], ![0, 1, 2, 0, 1, 1], ![0, 1, 2, 0, 1, 2], ![0, 1, 2, 0, 2, 0], ![0, 1, 2, 0, 2, 1], ![0, 1, 2, 0, 2, 2], ![0, 1, 2, 1, 0, 0], ![0, 1, 2, 1, 0, 1], ![0, 1, 2, 1, 0, 2], ![0, 1, 2, 1, 1, 0], ![0, 1, 2, 1, 1, 1], ![0, 1, 2, 1, 1, 2], ![0, 1, 2, 1, 2, 0], ![0, 1, 2, 1, 2, 1], ![0, 1, 2, 1, 2, 2], ![0, 1, 2, 2, 0, 0], ![0, 1, 2, 2, 0, 1], ![0, 1, 2, 2, 0, 2], ![0, 1, 2, 2, 1, 0], ![0, 1, 2, 2, 1, 1], ![0, 1, 2, 2, 1, 2], ![0, 1, 2, 2, 2, 0], ![0, 1, 2, 2, 2, 1], ![0, 1, 2, 2, 2, 2]]$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.representatives` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233159: 6-row three-state sum exclusion*. URL: <https://oeis.org/A233159>.

*Commentary.*

Each equality pattern has a representative using colors in order of first occurrence.

**Definition 1.5 (quotient).**

$$\forall i \in Fin\left(122\right),\; \forall s \in Fin\left(122\right),\; quotient\left(i, s\right) = List.sum\left(List.map\left((\lambda j: Fin\left(122\right) \mapsto (\operatorname{if} j = s \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0)), successors\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.quotient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233159: 6-row three-state sum exclusion*. URL: <https://oeis.org/A233159>.

*Commentary.*

The quotient entry is the multiplicity of a class in the successor list.

**Definition 1.6 (weights).**

$$weights = ![3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6]$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.weights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233159: 6-row three-state sum exclusion*. URL: <https://oeis.org/A233159>.

*Commentary.*

The weights count all columns in each class, including constant columns.

**Definition 1.7 (successors).**

$$successors = ![[0, 81, 41, 27, 14, 54, 68, 9, 5, 72, 50, 18, 23, 45, 77, 3, 2, 78, 44, 24, 17, 51, 71, 6, 8, 69, 53, 15, 26, 42, 80, 1, 1, 80, 42, 26, 15, 53, 69, 8, 6, 71, 51, 17, 24, 44, 78, 2, 3, 77, 45, 23, 18, 50, 72, 5, 9, 68, 54, 14, 27, 41, 81, 0], [0, 81, 41, 27, 14, 54, 68, 9, 5, 72, 50, 18, 23, 45, 77, 3, 1, 82, 43, 28, 16, 55, 70, 10, 7, 73, 52, 19, 25, 46, 79, 4], [0, 81, 41, 27, 14, 54, 68, 9, 1, 80, 42, 26, 15, 53, 69, 8], [0, 81, 41, 27, 14, 54, 68, 9, 2, 84, 47, 30, 20, 57, 74, 12, 1, 82, 43, 28, 16, 55, 70, 10, 3, 85, 49, 31, 22, 58, 76, 13], [4, 83, 48, 29, 21, 56, 75, 11, 3, 85, 49, 31, 22, 58, 76, 13], [0, 81, 41, 27, 2, 78, 44, 24, 1, 80, 42, 26, 3, 77, 45, 23], [0, 81, 41, 27, 1, 82, 43, 28], [3, 77, 45, 23, 4, 79, 46, 25], [0, 81, 41, 27, 5, 90, 59, 36, 1, 80, 42, 26, 7, 89, 60, 35], [0, 81, 41, 27, 5, 90, 59, 36, 2, 84, 47, 30, 8, 93, 65, 39, 1, 82, 43, 28, 6, 91, 61, 37, 3, 85, 49, 31, 9, 94, 67, 40], [4, 83, 48, 29, 10, 92, 66, 38, 3, 85, 49, 31, 9, 94, 67, 40], [11, 87, 62, 33, 13, 86, 63, 32], [8, 93, 65, 39, 9, 94, 67, 40], [13, 86, 63, 32, 10, 92, 66, 38, 12, 88, 64, 34, 9, 94, 67, 40], [0, 81, 5, 72, 2, 78, 8, 69, 1, 80, 6, 71, 3, 77, 9, 68], [0, 81, 5, 72, 1, 82, 7, 73], [3, 77, 9, 68, 4, 79, 10, 70], [0, 81, 1, 80], [0, 81, 2, 84, 1, 82, 3, 85], [4, 83, 3, 85], [8, 69, 9, 68], [11, 75, 13, 76], [9, 68, 12, 74, 10, 70, 13, 76], [0, 81, 14, 108, 2, 78, 20, 105, 1, 80, 16, 107, 3, 77, 22, 104], [0, 81, 14, 108, 1, 82, 15, 109], [3, 77, 22, 104, 4, 79, 21, 106], [0, 81, 14, 108, 5, 90, 23, 117, 1, 80, 16, 107, 7, 89, 25, 116], [0, 81, 14, 108, 5, 90, 23, 117, 2, 84, 17, 111, 8, 93, 26, 120, 1, 82, 15, 109, 6, 91, 24, 118, 3, 85, 18, 112, 9, 94, 27, 121], [4, 83, 19, 110, 10, 92, 28, 119, 3, 85, 18, 112, 9, 94, 27, 121], [11, 87, 29, 114, 13, 86, 31, 113], [8, 93, 26, 120, 9, 94, 27, 121], [13, 86, 31, 113, 10, 92, 28, 119, 12, 88, 30, 115, 9, 94, 27, 121], [32, 99, 38, 96, 34, 98, 40, 95], [32, 99, 33, 100], [40, 95, 39, 97], [23, 117, 25, 116], [23, 117, 26, 120, 24, 118, 27, 121], [28, 119, 27, 121], [38, 96, 29, 114, 40, 95, 31, 113], [35, 102, 26, 120, 36, 103, 27, 121], [40, 95, 31, 113, 37, 101, 28, 119, 39, 97, 30, 115, 36, 103, 27, 121], [0, 14, 5, 23, 2, 17, 8, 26, 1, 15, 6, 24, 3, 18, 9, 27], [0, 14, 5, 23, 1, 16, 7, 25], [3, 18, 9, 27, 4, 19, 10, 28], [0, 14, 1, 15], [0, 14, 2, 20, 1, 16, 3, 22], [4, 21, 3, 22], [8, 26, 9, 27], [11, 29, 13, 31], [9, 27, 12, 30, 10, 28, 13, 31], [0, 2, 1, 3], [0, 1], [3, 4], [0, 5, 1, 7], [0, 5, 2, 8, 1, 6, 3, 9], [4, 10, 3, 9], [11, 13], [8, 9], [13, 10, 12, 9], [23, 26, 24, 27], [23, 25], [27, 28], [32, 33], [32, 38, 34, 40], [39, 40], [26, 35, 27, 36], [29, 38, 31, 40], [27, 36, 30, 39, 28, 37, 31, 40], [0, 41, 5, 59, 2, 47, 8, 65, 1, 43, 6, 61, 3, 49, 9, 67], [0, 41, 5, 59, 1, 42, 7, 60], [3, 49, 9, 67, 4, 48, 10, 66], [0, 41, 1, 43], [0, 41, 2, 44, 1, 42, 3, 45], [4, 46, 3, 45], [8, 65, 9, 67], [11, 62, 13, 63], [9, 67, 12, 64, 10, 66, 13, 63], [0, 41, 14, 68, 2, 47, 20, 74, 1, 43, 16, 70, 3, 49, 22, 76], [0, 41, 14, 68, 1, 42, 15, 69], [3, 49, 22, 76, 4, 48, 21, 75], [0, 41, 14, 68, 5, 50, 23, 77, 1, 43, 16, 70, 7, 52, 25, 79], [0, 41, 14, 68, 5, 50, 23, 77, 2, 44, 17, 71, 8, 53, 26, 80, 1, 42, 15, 69, 6, 51, 24, 78, 3, 45, 18, 72, 9, 54, 27, 81], [4, 46, 19, 73, 10, 55, 28, 82, 3, 45, 18, 72, 9, 54, 27, 81], [11, 56, 29, 83, 13, 58, 31, 85], [8, 53, 26, 80, 9, 54, 27, 81], [13, 58, 31, 85, 10, 55, 28, 82, 12, 57, 30, 84, 9, 54, 27, 81], [32, 86, 38, 92, 34, 88, 40, 94], [32, 86, 33, 87], [40, 94, 39, 93], [23, 77, 25, 79], [23, 77, 26, 80, 24, 78, 27, 81], [28, 82, 27, 81], [38, 92, 29, 83, 40, 94, 31, 85], [35, 89, 26, 80, 36, 90, 27, 81], [40, 94, 31, 85, 37, 91, 28, 82, 39, 93, 30, 84, 36, 90, 27, 81], [95, 113, 101, 119, 97, 115, 103, 121], [95, 113, 96, 114], [103, 121, 102, 120], [95, 97], [95, 98, 96, 99], [100, 99], [119, 121], [116, 117], [121, 118, 120, 117], [68, 74, 70, 76], [68, 69], [76, 75], [68, 77, 70, 79], [68, 77, 71, 80, 69, 78, 72, 81], [73, 82, 72, 81], [83, 85], [80, 81], [85, 82, 84, 81], [113, 86, 119, 92, 115, 88, 121, 94], [113, 86, 114, 87], [121, 94, 120, 93], [104, 77, 106, 79], [104, 77, 107, 80, 105, 78, 108, 81], [109, 82, 108, 81], [119, 92, 110, 83, 121, 94, 112, 85], [116, 89, 107, 80, 117, 90, 108, 81], [121, 94, 112, 85, 118, 91, 109, 82, 120, 93, 111, 84, 117, 90, 108, 81]]$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.successors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233159: 6-row three-state sum exclusion*. URL: <https://oeis.org/A233159>.

*Commentary.*

Each representative has exactly the displayed list of successor classes.

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
