# Literal arrays and an eleven-class transfer

## Abstract

Hardin's order-ten recurrence for literal six-column diagonal strips.

Rows have six cells, with colours 0 through 5. The complementary pairs are {0,5}, {1,4}, {2,3}. The horizontal predicate and its decision procedure are HardinA233254TriangleStrip.rowLegal and instDecidableRowLegal. Fin.val converts a finite index or colour to a natural number.

**Definition 1.1 (Valid scanner boundaries).**

$$\forall (s: \operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{Fin}\left(6\right) \to \operatorname{Fin}\left(3\right)), (\operatorname{HardinA233172DiagonalStrip}.\operatorname{Valid}\left(s, p\right) = \left((\operatorname{Prod}.\operatorname{fst}\left(s\right) = \operatorname{true}) \land ((\operatorname{HardinThinGraphTransport}.\operatorname{proper}\left(p\right)) \land ((\operatorname{Prod}.\operatorname{snd}\left(s\right) = \operatorname{false}) \implies (\forall (j: \operatorname{Fin}\left(6\right)), (p\left(j\right) \ne 2))))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233172: six-column complementary-pair diagonal strips*. URL: <https://oeis.org/A233172>.

*Commentary.*

The first seen flag is true, the boundary is proper, and a false second flag excludes label two at every position.

**Definition 1.2 (Eleven boundary classes).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{boundaryClass}: \operatorname{HardinA233175PairStrip}.\operatorname{Seen} \to \left(\left(\operatorname{Fin}\left(6\right) \to \operatorname{Fin}\left(3\right)\right) \to \operatorname{Fin}\left(11\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.boundaryClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233172: six-column complementary-pair diagonal strips*. URL: <https://oeis.org/A233172>.

*Commentary.*

This typed finite table returns zero when the second seen flag is false. Otherwise it indexes the sixteen-entry vector (1,2,3,4,3,5,6,7,2,8,5,9,4,9,7,10) by weights 8,4,2,1 for p(0)=p(2), p(1)=p(3), p(2)=p(4), p(3)=p(5). The finite_certificate theorem pins this classification to successor counts.

**Definition 1.3 (The frozen weighted transfer).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{transfer}: \operatorname{Fin}\left(11\right) \to \left(\operatorname{Fin}\left(11\right) \to \operatorname{Int}\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233172: six-column complementary-pair diagonal strips*. URL: <https://oeis.org/A233172>.

*Commentary.*

The complete eleven by eleven integer table is pinned by finite_certificate to the weighted scanner successor counts; its saturated proper block supplies the width-six HDA defect transfer after division by 64.

**Definition 1.4 (Actual weighted scanner fibres).**

$$\forall (s: \operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{Fin}\left(6\right) \to \operatorname{Fin}\left(3\right)), (\forall (k: \operatorname{Fin}\left(11\right)), (\operatorname{HardinA233172DiagonalStrip}.\operatorname{classCount}\left(s, p, k\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row}} (((\operatorname{if}\left(\right) ((\operatorname{HardinA233254TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\forall (j: \operatorname{Fin}\left(5\right)), ((p\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right)) \land (p\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right)))) \land ((\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right)) \land (\operatorname{HardinA233172DiagonalStrip}.\operatorname{boundaryClass}\left(\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left(s, c\right), ((j: \operatorname{Fin}\left(6\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(j\right)\right)))\right) = k)))) \operatorname{then}\left(\right) (1) \operatorname{else}\left(\right) (0)): \operatorname{Int})))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.classCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233172: six-column complementary-pair diagonal strips*. URL: <https://oeis.org/A233172>.

*Commentary.*

The finite sum counts colour rows satisfying row legality, both cross-diagonal pair-label exclusions, scanner goodness, and the requested final boundary class. Pair labels are written as the public beta map rather than a private alias.

**Theorem 1.5 (Exact pair-label fibre sum).**

$$\forall (s: \operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{Fin}\left(6\right) \to \operatorname{Fin}\left(3\right)), (\forall (k: \operatorname{Fin}\left(11\right)), (\operatorname{HardinA233172DiagonalStrip}.\operatorname{classCount}\left(s, p, k\right) = \sum_{q: \operatorname{Fin}\left(6\right) \to \operatorname{Fin}\left(3\right)} ((\operatorname{HardinA233255LiteralBridge}.\operatorname{rowWeight}\left(s, q\right)) \cdot (((\operatorname{if}\left(\right) ((\forall (j: \operatorname{Fin}\left(5\right)), (q\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \ne q\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right))) \land ((\forall (j: \operatorname{Fin}\left(5\right)), ((p\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \ne q\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)) \land (p\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right) \ne q\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)))) \land (\operatorname{HardinA233172DiagonalStrip}.\operatorname{boundaryClass}\left(\operatorname{HardinA233255LiteralBridge}.\operatorname{rowFinish}\left(s, q\right), q\right) = k))) \operatorname{then}\left(\right) (1) \operatorname{else}\left(\right) (0)): \operatorname{Int}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.class_fibres` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233172: six-column complementary-pair diagonal strips*. URL: <https://oeis.org/A233172>.

*Commentary.*

The scanner fibre identity retains rowWeight and rowFinish. It equates the actual colour-row count to a sum over all three-label boundary rows.

**Theorem 1.6 (The original scanner transfer certificate).**

$$\forall (s: \operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{Fin}\left(6\right) \to \operatorname{Fin}\left(3\right)), ((\operatorname{HardinA233172DiagonalStrip}.\operatorname{Valid}\left(s, p\right)) \implies (\forall (k: \operatorname{Fin}\left(11\right)), (\operatorname{HardinA233172DiagonalStrip}.\operatorname{classCount}\left(s, p, k\right) = \operatorname{HardinA233172DiagonalStrip}.\operatorname{transfer}\left(\operatorname{HardinA233172DiagonalStrip}.\operatorname{boundaryClass}\left(s, p\right), k\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233172: six-column complementary-pair diagonal strips*. URL: <https://oeis.org/A233172>.

*Commentary.*

Every valid seen state and boundary has exactly the classCount prescribed by the frozen eleven-class transfer. At saturated state these fibres furnish the width-six proper-colouring block.

**Definition 1.7 (Both diagonal exclusions).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row}), (\forall (d: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{bonds}\left(c, d\right) = \forall (j: \operatorname{Fin}\left(5\right)), (((c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \ne d\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(d\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right)) \ne 5)) \land ((c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right) \ne d\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(d\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right)) \ne 5)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.bonds` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233172: six-column complementary-pair diagonal strips*. URL: <https://oeis.org/A233172>.

*Commentary.*

Both diagonals connect consecutive rows. There is no vertical or wraparound bond.

**Definition 1.8 (The literal filtered count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(((A: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right)) \to \operatorname{Fin}\left(6\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthLegal}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{rowLegal}, \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{bonds}, A\right))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right)) \to \operatorname{Fin}\left(6\right)\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233172: six-column complementary-pair diagonal strips*. URL: <https://oeis.org/A233172>.

*Commentary.*

The filter ranges over every array function. HardinA233251TriangleStrip.widthLegal requires a zero first cell, rowLegal on each row, and bonds between consecutive rows. Its widthNormal predicate starts with both flags false. In strict row-major order, every 2, 3 or 4 has an earlier 1, and every 3 has an earlier 2. Colours may be absent. At height zero the first-cell existential is false. There is no orbit divisor.

**Theorem 1.9 (The recurrence at every height at least eleven).**

$$\forall (n: \operatorname{Nat}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (11)\right): \operatorname{Int}) = ((((((((((1216) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (10)\right): \operatorname{Int}))) - ((303104) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (9)\right): \operatorname{Int})))) - ((6553600) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (8)\right): \operatorname{Int})))) + ((6056574976) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (7)\right): \operatorname{Int})))) - ((287762808832) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (6)\right): \operatorname{Int})))) - ((18622978195456) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (5)\right): \operatorname{Int})))) + ((1482141674242048) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (4)\right): \operatorname{Int})))) - ((15199648742375424) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (3)\right): \operatorname{Int})))) - ((522417556774977536) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (2)\right): \operatorname{Int})))) + ((5764607523034234880) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233172DiagonalStrip}.\operatorname{a}\left((n) + (1)\right): \operatorname{Int}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233172` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233172","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233172: six-column complementary-pair diagonal strips*. URL: <https://oeis.org/A233172>.

*Commentary.*

Exact scanner fibres reduce the colour rows to their pair labels, retaining each colour's multiplicity. Proper six-cell boundaries have ten classes under label permutation and reversal. One further class has not yet seen colour 2. In order, the complete-sector classes are indexed by the lexicographically least reversal of the four Boolean tests p(j)=p(j+2), with false before true. Their sizes are 6,12,12,12,12,6,12,6,12,6. The initial distribution is (16,8,16,16,16,16,8,16,8,16,0). The finite transfer certificate identifies all continuation counts with powers of the eleven-class transfer by induction. Multiplying the initial distribution by ten transfer powers gives the displayed integer linear combination of its preceding ten vectors. Pairing this vector identity with any continuation vector proves the recurrence for every natural n. Thus the first applicable sequence index is eleven.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.Valid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.bonds`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.boundaryClass`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.classCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.class_fibres`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.transfer`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip](HardinA233126SquareStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip](HardinA233254TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge](HardinA233255LiteralBridge.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer](HardinA233255PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry](HardinA233255ShapeSymmetry.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
