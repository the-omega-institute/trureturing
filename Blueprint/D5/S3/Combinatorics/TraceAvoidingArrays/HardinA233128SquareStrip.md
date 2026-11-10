# One-row certification and all-height recurrence

## Abstract

Hardin's order-fourteen recurrence for seven-column square strips.

All counts use the literal filter in HardinA233128Rows. All names below are full Lean names. Fin.val is the natural value of a finite index. Nat.div denotes natural quotient and Nat.mod its nonnegative remainder; neither occurs in the formulas. At width 7 the generic width_counting_bridge applies with rowLegal, labels, compatible and bonds. The colour_bond_iff theorem identifies each vertical bond with inequality of complementary-pair labels, while widthNormal supplies the row-major precedence conditions.

**Theorem 1.1 (Single-row certificate).**

$$(\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{PairRow}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{Valid}\left(s, p\right)) \implies (\forall (k: \operatorname{Fin}\left(21\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{classCount}\left(s, p, k\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{transfer}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{boundaryClass}\left(s, p\right), k\right)))))) \land (\forall (k: \operatorname{Fin}\left(21\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{firstCount}\left(k\right) = ![32, 0, 32, 32, 32, 16, 32, 32, 32, 32, 16, 32, 32, 16, 32, 16, 32, 16, 32, 16, 16]\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233128: six-colour complementary-pair exclusion on a seven-column square strip*. URL: <https://oeis.org/A233128>.

*Commentary.*

The scanner_fibres theorem reduces 6^7 individual rows to 3^7 label rows. The first_fibres owner fixes the initial zero before summing the six remaining label positions. The 192 proper label rows form 20 relabelling-and-reversal classes after colour 2; the unseen sector gives one additional state with eigenvalue 128.

**Theorem 1.2 (The recurrence at every positive source height).**

$$\forall (n: \operatorname{Nat}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{a}\left((n) + (15)\right): \operatorname{Int}) = ((((((((((((((7168) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{a}\left((n) + (14)\right): \operatorname{Int}))) - ((19070976) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{a}\left((n) + (13)\right): \operatorname{Int})))) + ((26086473728) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{a}\left((n) + (12)\right): \operatorname{Int})))) - ((21081846972416) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{a}\left((n) + (11)\right): \operatorname{Int})))) + ((10809917287956480) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{a}\left((n) + (10)\right): \operatorname{Int})))) - ((3649692508960587776) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{a}\left((n) + (9)\right): \operatorname{Int})))) + ((824336623994081902592) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{a}\left((n) + (8)\right): \operatorname{Int})))) - ((124561639357723747287040) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{a}\left((n) + (7)\right): \operatorname{Int})))) + ((12414326720213201465638912) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{a}\left((n) + (6)\right): \operatorname{Int})))) - ((792885332473813431379558400) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{a}\left((n) + (5)\right): \operatorname{Int})))) + ((31062140009178282014900486144) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{a}\left((n) + (4)\right): \operatorname{Int})))) - ((704387882353381376417601683456) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{a}\left((n) + (3)\right): \operatorname{Int})))) + ((8398185226512019784915658735616) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{a}\left((n) + (2)\right): \operatorname{Int})))) - ((40564819207303340847894502572032) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{a}\left((n) + (1)\right): \operatorname{Int}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233128` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233128","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233128: six-colour complementary-pair exclusion on a seven-column square strip*. URL: <https://oeis.org/A233128>.

*Commentary.*

The exact one-step counts preserve class-constant continuation vectors. Iteration is the finite-class instance of Function.Semiconj.iterate_right. The first distribution has total 528. Its successive products with the 21-by-21 transfer obey the displayed fourteen-term linear identity. That vector identity is stronger than the corresponding scalar identity: multiplying it by the continuation vector at any height proves the recurrence for the literal counts. The index n is any natural number, so the left side covers every height at least 15. Every count is cast to Int before signed arithmetic.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Certificate](HardinA233128Certificate.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows](HardinA233128Rows.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge](HardinA233255LiteralBridge.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer](HardinA233255PairTransfer.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
