# From exact source cardinalities to the full recurrence

## Abstract

The all-width recurrence for the literal normalized six-colour five-row array count.

The source count and FullE are those of HardinA233178Literal. The transfer uses the original five rows as five independent base-three digits. Its three-label columns are an auxiliary representation of the source graph. No continuation or source-correspondence hypothesis is assumed.

**Definition 1.1 (columnEquiv).**

$$(\operatorname{HardinA233178Recurrence}.\operatorname{columnEquiv}: \operatorname{Equiv}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{Fin}\left(5\right) \to \operatorname{Fin}\left(3\right)\right)) = \operatorname{Equiv}.\operatorname{symm}\left((\operatorname{finFunctionFinEquiv}: \operatorname{Equiv}\left(\operatorname{Fin}\left(5\right) \to \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3^{5}\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence.columnEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A ternary code is equivalent to a function assigning a label to each of the five rows.

**Theorem 1.2 (count_transfer).**

$$\forall (n: \operatorname{Nat}), (\operatorname{HardinA233178Literal}.\operatorname{chromaticCount}\left(n + 1\right) = \operatorname{dotProduct}\left((1: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int}), \operatorname{HardinA233178Chromatic}.\operatorname{v}\left(n\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence.count_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The base-three equivalence identifies arrays with sequences of column codes. The literal edges impose Bond on consecutive codes. TransferMatrix.cont_matrix counts the continuations from each initial column, and the dot product sums over those columns.

**Theorem 1.3 (chromatic_recurrence).**

$$\forall (n: \operatorname{Nat}), (\operatorname{HardinA233178Literal}.\operatorname{chromaticCount}\left(n + 12\right) = 6 \cdot \operatorname{HardinA233178Literal}.\operatorname{chromaticCount}\left(n + 11\right) + 31 \cdot \operatorname{HardinA233178Literal}.\operatorname{chromaticCount}\left(n + 10\right) - 97 \cdot \operatorname{HardinA233178Literal}.\operatorname{chromaticCount}\left(n + 9\right) - 163 \cdot \operatorname{HardinA233178Literal}.\operatorname{chromaticCount}\left(n + 8\right) + 417 \cdot \operatorname{HardinA233178Literal}.\operatorname{chromaticCount}\left(n + 7\right) + 93 \cdot \operatorname{HardinA233178Literal}.\operatorname{chromaticCount}\left(n + 6\right) - 514 \cdot \operatorname{HardinA233178Literal}.\operatorname{chromaticCount}\left(n + 5\right) + 192 \cdot \operatorname{HardinA233178Literal}.\operatorname{chromaticCount}\left(n + 4\right) + 72 \cdot \operatorname{HardinA233178Literal}.\operatorname{chromaticCount}\left(n + 3\right) - 36 \cdot \operatorname{HardinA233178Literal}.\operatorname{chromaticCount}\left(n + 2\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence.chromatic_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The continuation recurrence applied to the constant-one vector gives the recurrence for the chromatic count.

**Theorem 1.4 (result).**

$$\forall (n: \operatorname{Nat}), (11 < n \Rightarrow (\operatorname{HardinA233178Literal}.\operatorname{a}\left(n\right): \operatorname{Int}) = 192 \cdot (\operatorname{HardinA233178Literal}.\operatorname{a}\left(n - 1\right): \operatorname{Int}) + 31744 \cdot (\operatorname{HardinA233178Literal}.\operatorname{a}\left(n - 2\right): \operatorname{Int}) - 3178496 \cdot (\operatorname{HardinA233178Literal}.\operatorname{a}\left(n - 3\right): \operatorname{Int}) - 170917888 \cdot (\operatorname{HardinA233178Literal}.\operatorname{a}\left(n - 4\right): \operatorname{Int}) + 13992198144 \cdot (\operatorname{HardinA233178Literal}.\operatorname{a}\left(n - 5\right): \operatorname{Int}) + 99857989632 \cdot (\operatorname{HardinA233178Literal}.\operatorname{a}\left(n - 6\right): \operatorname{Int}) - 17660905521152 \cdot (\operatorname{HardinA233178Literal}.\operatorname{a}\left(n - 7\right): \operatorname{Int}) + 211106232532992 \cdot (\operatorname{HardinA233178Literal}.\operatorname{a}\left(n - 8\right): \operatorname{Int}) + 2533274790395904 \cdot (\operatorname{HardinA233178Literal}.\operatorname{a}\left(n - 9\right): \operatorname{Int}) - 40532396646334464 \cdot (\operatorname{HardinA233178Literal}.\operatorname{a}\left(n - 10\right): \operatorname{Int}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233178` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233178","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233178: normalized six-colour five-row arrays*. URL: <https://oeis.org/A233178>.

*Commentary.*

The chromatic coefficients sum to one, so adding six preserves the unscaled recurrence. Substitution of 48*a(n)=32^n*(chromaticCount(n)+6) multiplies the coefficient at lag i by 32^i. All lag widths are at least two when the source width exceeds eleven.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence.chromatic_recurrence`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence.columnEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence.count_transfer`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic](HardinA233178Chromatic.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Literal](HardinA233178Literal.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](../TransferMatrix.md)
