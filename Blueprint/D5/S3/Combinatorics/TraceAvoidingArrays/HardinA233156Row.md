# OEIS A233156

## Abstract

The number of labelled 3-row arrays obeys the order-2 recurrence from OEIS A233156.

**Definition 1.1 (U3).**

$$\forall n \in \operatorname{Nat},\; U_{3}\left(n\right) = Finset.card\left(Finset.filter\left((\lambda f: (Fin\left(3\right) \times Fin\left(n\right)) \to Fin\left(3\right) \mapsto (Legal\left(f\right))), \operatorname{Finset.univ}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233156Row.U3` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233156: 3-row three-state sum exclusion*. URL: <https://oeis.org/A233156>.

*Commentary.*

HardinA233155RowTransfer.T at height three counts every labelled function satisfying horizontal and antidiagonal sum exclusion.

**Theorem 1.2 (result).**

$$\forall n \in \operatorname{Nat},\; (U_{3}\left(n + 5\right): \operatorname{Int}) = 5 \cdot (U_{3}\left(n + 4\right): \operatorname{Int}) - 2 \cdot (U_{3}\left(n + 3\right): \operatorname{Int})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233156Row.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233156` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233156Row.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233156","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233156Row.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233156: 3-row three-state sum exclusion*. URL: <https://oeis.org/A233156>.

*Commentary.*

The alternating permutation preserves every labelled array and identifies its count with HardinA233258PairTransfer.L. Its initial_values give the width-five base identity. Its powers_table identifies Q^2, Q^3 and Q^4 with the corresponding W vectors; the relation W(4) = -2 W(2) + 5 W(3), scalarRelationShift and count_transfer give every larger width.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233156Row.U3`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233156Row.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer](HardinA233155ColumnTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer](HardinA233258PairTransfer.md)
