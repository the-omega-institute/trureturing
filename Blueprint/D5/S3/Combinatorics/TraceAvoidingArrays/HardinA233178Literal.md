# Literal arrays and scanner fibres

## Abstract

The exact five-row six-colour source count and a division-free chromatic correspondence.

The domain is Fin 5 times Fin n. Every cell has one of six colours, the top left cell is zero, and first appearances are ordered by the strict rank i*n+j. Colours may be absent. Every horizontal, diagonal and antidiagonal pair across consecutive columns has distinct colours whose sum is not five. Vertical and wraparound pairs have no restriction. All recurrence arithmetic is in the integers.

**Definition 1.1 (The literal function domain).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.Array`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.Array` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Arrays are arbitrary functions on the five rows and n columns into a finite colour set.

**Definition 1.2 (Strict row-major rank).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.rank`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.rank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rank of cell (i,j) is i*n+j.

**Definition 1.3 (Exactly the constrained pairs).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.Edges`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.Edges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An edge goes one column to the right and changes the row by at most one. There is no modular indexing.

**Definition 1.4 (Literal first appearances).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.Normal`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.Normal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every occurrence of two, three or four has an earlier one, and every occurrence of three has an earlier two. Earlier means strictly smaller literal row-major rank.

**Definition 1.5 (The full source predicate).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.Legal`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate conjoins the pinned initial cell, every edge restriction and the first-appearance conditions. It imposes no surjectivity or orbit divisor.

**Definition 1.6 (Literal cardinality).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.a`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The count is the cardinality of the legal function subtype, expressed as a finite filtered set. Only positive widths enter FullE.

**Definition 1.7 (The unchanged event).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.FullE`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.FullE` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n greater than eleven, the literal count satisfies the ten-term integer recurrence, with coefficients in lag order 192, 31744, -3178496, -170917888, 13992198144, 99857989632, -17660905521152, 211106232532992, 2533274790395904, -40532396646334464. There is no upper cutoff, additional onset, generating-function assertion or minimal-order assertion.

**Definition 1.8 (Exact row-major reindexing).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.word`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product-to-Fin equivalence enumerates the cells at their actual rank. It is a bijection and preserves the strict earlier relation used in Normal.

**Definition 1.9 (Proper pair-label arrays).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.Proper`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.Proper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Complementary pairs become the three labels. Properness requires different labels at exactly the literal edges.

**Definition 1.10 (Anchored proper pair labels).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.Anchored`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.Anchored` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial pair label is zero and the array is proper. There is no occurrence requirement on the other labels.

**Theorem 1.11 (Exact scanner pushforward).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.scanner_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.scanner_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Twice the literal source count is the sum of the existing scanner weights over the anchored proper three-label arrays. The factor two comes from exchanging colours zero and five, which leaves the pair labels, scanner permission and scanner state unchanged. The existing scanner_fibres theorem counts the exact individual-colour fibres after the row-major bijection. The scanner starts in (false,false) and reads word(q) in that same row-major order. This statement includes every width.

**Definition 1.12 (Anchored chromatic count).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.pairCount`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.pairCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This integer finite sum counts every proper three-label array with its initial label zero, including arrays missing one label.

**Theorem 1.13 (Exact missing-label correction).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.source_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.source_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least two, sixteen times a(n) equals 32^n times (pairCount(n)+2). Exchanging labels one and two preserves anchored properness. Summing the existing pointwise normalization identity therefore counts both scanner orders. Each missing-label fibre has exactly one member: the alternating column-parity colouring. Its uniqueness follows first down the initial column using a common neighbour, then across every row by induction on the column. An anchored proper array cannot miss both nonzero labels. These facts supply the correction two without a source surjectivity condition or an imposed orbit divisor.

**Definition 1.14 (Unrestricted chromatic cardinality).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.chromaticCount`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.chromaticCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This counts all proper three-label arrays on the literal graph, with every initial label allowed.

**Theorem 1.15 (Division-free literal source bridge).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.chromatic_source_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.chromatic_source_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n at least two, 48*a(n) equals 32^n*(chromaticCount(n)+6). Permuting zero with a specified initial label gives a bijection between the three anchored fibres. The proof multiplies the anchored identity by three; it uses no truncated subtraction or division.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.Anchored`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.Array`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.Edges`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.FullE`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.Normal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.Proper`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.chromaticCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.chromatic_source_count`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.pairCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.rank`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.scanner_count`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.source_count`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal.word`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Normalization](HardinA233178Normalization.md)
