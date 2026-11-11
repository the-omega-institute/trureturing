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

$$classes = (![![![![![0, 1, 1], ![2, 3, 4], ![2, 4, 3]], ![![5, 6, 7], ![8, 9, 10], ![11, 12, 13]], ![![5, 7, 6], ![11, 13, 12], ![8, 10, 9]]], ![![![14, 15, 16], ![17, 18, 19], ![20, 21, 22]], ![![23, 24, 25], ![26, 27, 28], ![29, 30, 31]], ![![32, 33, 34], ![35, 36, 37], ![38, 39, 40]]], ![![![14, 16, 15], ![20, 22, 21], ![17, 19, 18]], ![![32, 34, 33], ![38, 40, 39], ![35, 37, 36]], ![![23, 25, 24], ![29, 31, 30], ![26, 28, 27]]]], ![![![![27, 26, 28], ![24, 23, 25], ![30, 29, 31]], ![![18, 17, 19], ![15, 14, 16], ![21, 20, 22]], ![![36, 35, 37], ![33, 32, 34], ![39, 38, 40]]], ![![![9, 8, 10], ![6, 5, 7], ![12, 11, 13]], ![![3, 2, 4], ![1, 0, 1], ![4, 2, 3]], ![![13, 11, 12], ![7, 5, 6], ![10, 8, 9]]], ![![![40, 38, 39], ![34, 32, 33], ![37, 35, 36]], ![![22, 20, 21], ![16, 14, 15], ![19, 17, 18]], ![![31, 29, 30], ![25, 23, 24], ![28, 26, 27]]]], ![![![![27, 28, 26], ![30, 31, 29], ![24, 25, 23]], ![![36, 37, 35], ![39, 40, 38], ![33, 34, 32]], ![![18, 19, 17], ![21, 22, 20], ![15, 16, 14]]], ![![![40, 39, 38], ![37, 36, 35], ![34, 33, 32]], ![![31, 30, 29], ![28, 27, 26], ![25, 24, 23]], ![![22, 21, 20], ![19, 18, 17], ![16, 15, 14]]], ![![![9, 10, 8], ![12, 13, 11], ![6, 7, 5]], ![![13, 12, 11], ![10, 9, 8], ![7, 6, 5]], ![![3, 4, 2], ![4, 3, 2], ![1, 1, 0]]]]]: Fin\left(3\right) \to \left(Fin\left(3\right) \to \left(Fin\left(3\right) \to \left(Fin\left(3\right) \to \left(Fin\left(3\right) \to Fin\left(41\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.classes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233158: 5-row three-state sum exclusion*. URL: <https://oeis.org/A233158>.

*Commentary.*

The table assigns a class to every column according to its equality pattern.

**Definition 1.3 (classify).**

$$\forall r \in Row\left(5\right),\; classify\left(r\right) = classes\left(r\left(0\right), r\left(1\right), r\left(2\right), r\left(3\right), r\left(4\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.classify` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233158: 5-row three-state sum exclusion*. URL: <https://oeis.org/A233158>.

*Commentary.*

The coordinates select one of the 41 equality classes.

**Definition 1.4 (representatives).**

$$representatives = ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 1], ![0, 0, 0, 1, 0], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 2], ![0, 0, 1, 0, 0], ![0, 0, 1, 0, 1], ![0, 0, 1, 0, 2], ![0, 0, 1, 1, 0], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 2], ![0, 0, 1, 2, 0], ![0, 0, 1, 2, 1], ![0, 0, 1, 2, 2], ![0, 1, 0, 0, 0], ![0, 1, 0, 0, 1], ![0, 1, 0, 0, 2], ![0, 1, 0, 1, 0], ![0, 1, 0, 1, 1], ![0, 1, 0, 1, 2], ![0, 1, 0, 2, 0], ![0, 1, 0, 2, 1], ![0, 1, 0, 2, 2], ![0, 1, 1, 0, 0], ![0, 1, 1, 0, 1], ![0, 1, 1, 0, 2], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 1], ![0, 1, 1, 1, 2], ![0, 1, 1, 2, 0], ![0, 1, 1, 2, 1], ![0, 1, 1, 2, 2], ![0, 1, 2, 0, 0], ![0, 1, 2, 0, 1], ![0, 1, 2, 0, 2], ![0, 1, 2, 1, 0], ![0, 1, 2, 1, 1], ![0, 1, 2, 1, 2], ![0, 1, 2, 2, 0], ![0, 1, 2, 2, 1], ![0, 1, 2, 2, 2]]$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.representatives` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233158: 5-row three-state sum exclusion*. URL: <https://oeis.org/A233158>.

*Commentary.*

Each equality pattern has a representative using colors in order of first occurrence.

**Definition 1.5 (quotient).**

$$quotient = ![![2, 2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 0, 0, 0, 2, 2, 0, 2, 2, 0, 0, 0, 0, 2, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1], ![1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1]]$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.quotient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233158: 5-row three-state sum exclusion*. URL: <https://oeis.org/A233158>.

*Commentary.*

An entry counts compatible successor columns in the indicated equality class.

**Definition 1.6 (weights).**

$$weights = ![3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6]$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.weights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233158: 5-row three-state sum exclusion*. URL: <https://oeis.org/A233158>.

*Commentary.*

The weights count all columns in each class, including constant columns.

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
