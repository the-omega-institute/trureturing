# OEIS A233153

## Abstract

The literal 6-column count obeys a recurrence determined by its finite row quotient.

**Definition 1.1 (T6).**

$$\forall n \in \operatorname{Nat},\; T6\left(n\right) = Finset.card\left(Finset.filter\left((\lambda f: Fin\left(n\right) \times Fin\left(6\right) \to Fin\left(3\right) \mapsto (Legal\left(f\right))), \operatorname{Finset.univ}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column.T6` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233153: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233153>.

*Commentary.*

Every labelled function satisfying the two bond conditions is counted.

**Definition 1.2 (classes).**

$$(classes: Fin\left(3\right) \to \left(Fin\left(3\right) \to \left(Fin\left(3\right) \to \left(Fin\left(3\right) \to \left(Fin\left(3\right) \to \left(Fin\left(3\right) \to Fin\left(8\right)\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column.classes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233153: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233153>.

*Commentary.*

The complete nested lookup table on the 6 row coordinates, including its zero entries.

**Definition 1.3 (classify).**

$$\forall r \in Row\left(6\right),\; classify\left(r\right) = classes\left(r\left(0\right), r\left(1\right), r\left(2\right), r\left(3\right), r\left(4\right), r\left(5\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column.classify` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233153: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233153>.

*Commentary.*

The finite decision tree assigns the successor class of a row.

**Definition 1.4 (quotient).**

$$quotient = ![![5, 5, 4, 4, 3, 3, 1, 1], ![3, 3, 3, 3, 3, 3, 2, 2], ![4, 4, 4, 4, 3, 3, 1, 1], ![2, 2, 2, 2, 2, 2, 3, 3], ![3, 3, 3, 3, 3, 3, 1, 1], ![4, 4, 2, 2, 3, 3, 2, 2], ![2, 2, 2, 2, 3, 3, 2, 2], ![1, 1, 1, 1, 1, 1, 3, 3]]$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column.quotient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233153: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233153>.

*Commentary.*

The quotient entry counts legal compatible successors in each class.

**Definition 1.5 (weights).**

$$weights = ![12, 12, 12, 12, 12, 12, 12, 12]$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column.weights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233153: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233153>.

*Commentary.*

The weights count legal rows in each class.

**Theorem 1.6 (finite_certificate).**

$$(\forall r \in Row\left(6\right),\; (rowLegal\left(r\right)) \Rightarrow (\forall s \in Fin\left(8\right),\; \sum_{(c: Row\left(6\right))} \operatorname{if} (rowLegal\left(c\right)) \land ((compatible\left(r, c\right)) \land (classify\left(c\right) = s)) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0 = quotient\left(classify\left(r\right), s\right))) \land ((\forall s \in Fin\left(8\right),\; \sum_{(c: Row\left(6\right))} \operatorname{if} (rowLegal\left(c\right)) \land (classify\left(c\right) = s) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0 = weights\left(s\right)) \land (Matrix.mulVec\left((quotient)^{1 + 3}, (1: Fin\left(8\right) \to \operatorname{Int})\right) = \sum_{(j: Fin\left(3\right))} HSMul.hSMul\left(![81, -90, 25]\left(j\right), Matrix.mulVec\left((quotient)^{1 + Fin.val\left(j\right)}, (1: Fin\left(8\right) \to \operatorname{Int})\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233153: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233153>.

*Commentary.*

The three finite identities give the successor counts, initial class multiplicities and a polynomial relation among quotient powers.

**Theorem 1.7 (result).**

$$\forall n \in \operatorname{Nat},\; (T6\left(n + 4\right): \operatorname{Int}) = 25 \cdot (T6\left(n + 3\right): \operatorname{Int}) - 90 \cdot (T6\left(n + 2\right): \operatorname{Int}) + 81 \cdot (T6\left(n + 1\right): \operatorname{Int})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233153` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233153","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233153: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233153>.

*Commentary.*

The finite relation extends through all further matrix powers. The initial instance supplies the exact starting index.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column.T6`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column.classes`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column.classify`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column.quotient`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233153Column.weights`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer](HardinA233155RowTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
