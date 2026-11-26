# The anchored width-five array count

## Abstract

The literal width-five OEIS A233199 recurrence.

**Definition 1.1 (Literal count).**

$$\forall (n: \operatorname{Nat}), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233199Recurrence}.\operatorname{a}\left(n\right) = \operatorname{Nat}.\operatorname{card}\left(\{f: (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(5\right)) \to \operatorname{Fin}\left(8\right) \mid \operatorname{HardinA233196Strip}.\operatorname{widthLegal}\left(\operatorname{rowLegal}, \operatorname{bonds}, f\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233199Recurrence.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233199: normalized eight-colour arrays of width five*. URL: <https://oeis.org/A233199>.

*Commentary.*

At positive height n, count exactly the functions from Fin n times Fin 5 to Fin 8 with top-left value zero. The endpoints of each contained horizontal, vertical and antidiagonal edge are unequal and their natural labels do not sum to seven. An occurrence of 2, 3, 4, 5 or 6 requires an earlier 1. An occurrence of 3, 4 or 5 requires an earlier 2. An occurrence of 4 requires an earlier 3. Earlier means strictly smaller rank 5 times the row plus the column. Colours may be unused.

**Theorem 1.2 (The ten signed lags at every height at least twelve).**

$$\forall (n: \operatorname{Nat}), 12 \le n \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233199Recurrence}.\operatorname{a}\left(n\right): \operatorname{Int}) = 736 \cdot (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233199Recurrence}.\operatorname{a}\left(n - 1\right): \operatorname{Int}) - 203776 \cdot (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233199Recurrence}.\operatorname{a}\left(n - 2\right): \operatorname{Int}) + 33062912 \cdot (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233199Recurrence}.\operatorname{a}\left(n - 3\right): \operatorname{Int}) - 3665821696 \cdot (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233199Recurrence}.\operatorname{a}\left(n - 4\right): \operatorname{Int}) + 270851375104 \cdot (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233199Recurrence}.\operatorname{a}\left(n - 5\right): \operatorname{Int}) - 10685878632448 \cdot (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233199Recurrence}.\operatorname{a}\left(n - 6\right): \operatorname{Int}) - 116548232544256 \cdot (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233199Recurrence}.\operatorname{a}\left(n - 7\right): \operatorname{Int}) + 35184372088832000 \cdot (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233199Recurrence}.\operatorname{a}\left(n - 8\right): \operatorname{Int}) - 1423137482249076736 \cdot (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233199Recurrence}.\operatorname{a}\left(n - 9\right): \operatorname{Int}) + 18446744073709551616 \cdot (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233199Recurrence}.\operatorname{a}\left(n - 10\right): \operatorname{Int})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233199Recurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233199` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233199Recurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233199","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233199Recurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233199: normalized eight-colour arrays of width five*. URL: <https://oeis.org/A233199>.

*Commentary.*

The width counting bridge reads the original literal rows. The boundary records each column's complementary pair and the first-use stage records which lower representatives have occurred in the full prefix. A relabelling permutes only pairs whose lower representatives have already appeared and preserves each colour's orientation within its pair.

There are twenty-three boundary classes across the three possible post-row stages. The kernel checks the signed row counts in every matrix entry and the initial vector from the literal anchored first row. The terminal vector is one at every state. The checked vector relation starts at the eleventh matrix power and left multiplication propagates it to all higher powers. The literal count at height n uses power n minus one, yielding all ten signed lags with onset twelve. The recurrence interprets the counts and arithmetic in the integers, and its lag indices in the natural numbers.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233199Recurrence.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233199Recurrence.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip](../HardinA233196Strip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](../TransferMatrix.md)
