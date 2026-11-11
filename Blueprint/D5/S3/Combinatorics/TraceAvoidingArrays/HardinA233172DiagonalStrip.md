# Literal arrays and an eleven-class transfer

## Abstract

Hardin's order-ten recurrence for literal six-column diagonal strips.

Rows have six cells, with colours 0 through 5. The complementary pairs are {0,5}, {1,4}, {2,3}. The horizontal predicate and its decision procedure are HardinA233254TriangleStrip.rowLegal and instDecidableRowLegal. Fin.val converts a finite index or colour to a natural number.

**Definition 1.1 (Both diagonal exclusions).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row}), (\forall (d: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{bonds}\left(c, d\right) = \forall (j: \operatorname{Fin}\left(5\right)), (((c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \ne d\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(d\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right)) \ne 5)) \land ((c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right) \ne d\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(d\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right)) \ne 5)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.bonds` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233172: six-column complementary-pair diagonal strips*. URL: <https://oeis.org/A233172>.

*Commentary.*

Both diagonals connect consecutive rows. There is no vertical or wraparound bond.

**Definition 1.2 (The literal filtered count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(((A: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right)) \to \operatorname{Fin}\left(6\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthLegal}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{rowLegal}, \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{bonds}, A\right))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right)) \to \operatorname{Fin}\left(6\right)\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233172: six-column complementary-pair diagonal strips*. URL: <https://oeis.org/A233172>.

*Commentary.*

The filter ranges over every array function. HardinA233251TriangleStrip.widthLegal requires a zero first cell, rowLegal on each row, and bonds between consecutive rows. Its widthNormal predicate starts with both flags false. In strict row-major order, every 2, 3 or 4 has an earlier 1, and every 3 has an earlier 2. Colours may be absent. At height zero the first-cell existential is false. There is no orbit divisor.

**Theorem 1.3 (The recurrence at every height at least eleven).**

$$\forall (n: \operatorname{Nat}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (11)\right): \operatorname{Int}) = ((((((((((1216) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (10)\right): \operatorname{Int}))) - ((303104) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (9)\right): \operatorname{Int})))) - ((6553600) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (8)\right): \operatorname{Int})))) + ((6056574976) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (7)\right): \operatorname{Int})))) - ((287762808832) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (6)\right): \operatorname{Int})))) - ((18622978195456) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (5)\right): \operatorname{Int})))) + ((1482141674242048) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (4)\right): \operatorname{Int})))) - ((15199648742375424) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (3)\right): \operatorname{Int})))) - ((522417556774977536) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (2)\right): \operatorname{Int})))) + ((5764607523034234880) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (1)\right): \operatorname{Int}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233172` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233172","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233172: six-column complementary-pair diagonal strips*. URL: <https://oeis.org/A233172>.

*Commentary.*

Exact scanner fibres reduce the colour rows to their pair labels, retaining each colour's multiplicity. Proper six-cell boundaries have ten classes under label permutation and reversal. One further class has not yet seen colour 2. In order, the complete-sector classes are indexed by the lexicographically least reversal of the four Boolean tests p(j)=p(j+2), with false before true. Their sizes are 6,12,12,12,12,6,12,6,12,6. The initial distribution is (16,8,16,16,16,16,8,16,8,16,0). The finite transfer certificate identifies all continuation counts with powers of the eleven-class transfer by induction. Multiplying the initial distribution by ten transfer powers gives the displayed integer linear combination of its preceding ten vectors. Pairing this vector identity with any continuation vector proves the recurrence for every natural n. Thus the first applicable sequence index is eleven.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.bonds`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip](HardinA233126SquareStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip](HardinA233254TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge](HardinA233255LiteralBridge.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer](HardinA233255PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry](HardinA233255ShapeSymmetry.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
