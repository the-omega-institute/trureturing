# OEIS A233158

## Abstract

The number of labelled 5-row arrays obeys the order-7 recurrence from OEIS A233158.

**Definition 1.1 (U5).**

$$\forall n \in \operatorname{Nat},\; U_{5}\left(n\right) = Finset.card\left(Finset.filter\left((\lambda f: (Fin\left(5\right) \times Fin\left(n\right)) \to Fin\left(3\right) \mapsto (Legal\left(f\right))), \operatorname{Finset.univ}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.U5` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233158: 5-row three-state sum exclusion*. URL: <https://oeis.org/A233158>.

*Commentary.*

Every labelled function satisfying horizontal and antidiagonal sum exclusion is counted.

**Theorem 1.2 (result).**

$$\forall n \in \operatorname{Nat},\; (U_{5}\left(n + 12\right): \operatorname{Int}) = 16 \cdot (U_{5}\left(n + 11\right): \operatorname{Int}) - 64 \cdot (U_{5}\left(n + 10\right): \operatorname{Int}) + 76 \cdot (U_{5}\left(n + 9\right): \operatorname{Int}) + 17 \cdot (U_{5}\left(n + 8\right): \operatorname{Int}) - 84 \cdot (U_{5}\left(n + 7\right): \operatorname{Int}) + 48 \cdot (U_{5}\left(n + 6\right): \operatorname{Int}) - 8 \cdot (U_{5}\left(n + 5\right): \operatorname{Int})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233158` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233158","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233158: 5-row three-state sum exclusion*. URL: <https://oeis.org/A233158>.

*Commentary.*

The alternating permutation preserves every labelled array and identifies its count with HardinA233260Literal.L. The pair_base and pair_tail relations imply the displayed recurrence because the coefficients sum to one, cancelling the added constant six.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.U5`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233158Row.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer](HardinA233155ColumnTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal](HardinA233260Literal.md)
