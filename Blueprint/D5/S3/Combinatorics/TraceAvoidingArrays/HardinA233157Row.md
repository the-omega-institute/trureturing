# OEIS A233157

## Abstract

The number of labelled 4-row arrays obeys the order-3 recurrence from OEIS A233157.

**Definition 1.1 (U4).**

$$\forall n \in \operatorname{Nat},\; U_{4}\left(n\right) = Finset.card\left(Finset.filter\left((\lambda f: (Fin\left(4\right) \times Fin\left(n\right)) \to Fin\left(3\right) \mapsto (Legal\left(f\right))), \operatorname{Finset.univ}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.U4` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233157: 4-row three-state sum exclusion*. URL: <https://oeis.org/A233157>.

*Commentary.*

Every labelled function satisfying horizontal and antidiagonal sum exclusion is counted.

**Theorem 1.2 (finite_certificate).**

$$Matrix.mulVec\left((HardinA233259PairTransferCore.Q)^{4 + 3}, (1: Fin\left(14\right) \to \operatorname{Int})\right) = \sum_{(j: Fin\left(3\right))} HSMul.hSMul\left(![6, -15, 9]\left(j\right), Matrix.mulVec\left((HardinA233259PairTransferCore.Q)^{4 + Fin.val\left(j\right)}, (1: Fin\left(14\right) \to \operatorname{Int})\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233157: 4-row three-state sum exclusion*. URL: <https://oeis.org/A233157>.

*Commentary.*

The four-row proper-colouring matrix HardinA233259PairTransferCore.Q satisfies this relation. HardinA233259PairTransferPowers.powers_table evaluates its fixed powers; no further transfer table is needed.

**Theorem 1.3 (result).**

$$\forall n \in \operatorname{Nat},\; (U_{4}\left(n + 8\right): \operatorname{Int}) = 9 \cdot (U_{4}\left(n + 7\right): \operatorname{Int}) - 15 \cdot (U_{4}\left(n + 6\right): \operatorname{Int}) + 6 \cdot (U_{4}\left(n + 5\right): \operatorname{Int})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233157` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233157","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233157: 4-row three-state sum exclusion*. URL: <https://oeis.org/A233157>.

*Commentary.*

Alternating the labels in successive columns identifies the literal count with HardinA233259PairTransferCore.L. Its Proper predicate agrees after exchanging the row binders. HardinA233259PairTransferCount.count_transfer then supplies the weighted matrix-power count for every width at least two. Multiplication propagates the finite relation to later widths; the first recurrence index follows by evaluating powers three through six.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.U4`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233157Row.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer](HardinA233155ColumnTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore](HardinA233259PairTransferCore.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCount](HardinA233259PairTransferCount.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers](HardinA233259PairTransferPowers.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
