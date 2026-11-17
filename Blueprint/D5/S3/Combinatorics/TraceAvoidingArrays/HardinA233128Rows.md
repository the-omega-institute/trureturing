# Literal counts and boundary classes

## Abstract

Literal seven-column complementary-pair square strips.

OEIS A233128 revision 6 specifies the count. Every displayed name is its full Lean name. Fin.val converts a finite index or colour to Nat. Nat.div is natural quotient division and Nat.mod its nonnegative remainder; neither operation occurs here. The public Row, rowLegal and PairRow are reused from HardinA233255PairTransfer. Horizontal and vertical bonds exclude equal colours and complementary colours; diagonal neighbours are unconstrained.

**Definition 1.1 (Vertical bonds).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{Row}), (\forall (d: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{bonds}\left(c, d\right) = \forall (j: \operatorname{Fin}\left(7\right)), ((c\left(j\right) \ne d\left(j\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left(j\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(d\left(j\right)\right)) \ne 5))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows.bonds` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233128: six-colour complementary-pair exclusion on a seven-column square strip*. URL: <https://oeis.org/A233128>.

*Commentary.*

Only equal columns in consecutive rows are joined.

**Definition 1.2 (Literal filtered finite count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(((A: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(7\right)) \to \operatorname{Fin}\left(6\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthLegal}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{rowLegal}, \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{bonds}, A\right))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(7\right)) \to \operatorname{Fin}\left(6\right)\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233128: six-colour complementary-pair exclusion on a seven-column square strip*. URL: <https://oeis.org/A233128>.

*Commentary.*

The filter uses widthLegal rowLegal bonds directly. Its first-cell condition fixes zero, its widthNormal conjunct enforces that every 2, 3 or 4 has an earlier 1 and every 3 an earlier 2 in row-major order. The initial scanner flags are false. At height zero the first-cell existential is false, so a 0 = 0.

**Definition 1.3 (Complementary-pair labels).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{labels}\left(c\right) = ((j: \operatorname{Fin}\left(7\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(j\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows.labels` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233128: six-colour complementary-pair exclusion on a seven-column square strip*. URL: <https://oeis.org/A233128>.

*Commentary.*

The published beta has fibres {0,5}, {1,4}, {2,3}.

**Definition 1.4 (Vertical label compatibility).**

$$\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{PairRow}), (\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{compatible}\left(p, c\right) = \forall (j: \operatorname{Fin}\left(7\right)), (p\left(j\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(j\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233128: six-colour complementary-pair exclusion on a seven-column square strip*. URL: <https://oeis.org/A233128>.

*Commentary.*

Every column excludes the same label in the next row.

**Definition 1.5 (Reachable boundary condition).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{PairRow}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{Valid}\left(s, p\right) = \left((\operatorname{Prod}.\operatorname{fst}\left(s\right) = \operatorname{Bool}.\operatorname{true}) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{rowProper}\left(p\right)) \land ((\operatorname{Prod}.\operatorname{snd}\left(s\right) = \operatorname{Bool}.\operatorname{false}) \implies (\forall (j: \operatorname{Fin}\left(7\right)), (p\left(j\right) \ne (2: \operatorname{Fin}\left(3\right))))))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233128: six-colour complementary-pair exclusion on a seven-column square strip*. URL: <https://oeis.org/A233128>.

*Commentary.*

Colour 1 has occurred; the row is proper; before colour 2 no label is 2.

**Definition 1.6 (Twenty completed classes and one unseen sector).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{PairRow}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{boundaryClass}\left(s, p\right) = (\operatorname{if} (\operatorname{Prod}.\operatorname{snd}\left(s\right)) \operatorname{then} ((\operatorname{if} (p\left((2: \operatorname{Fin}\left(7\right))\right) = p\left((0: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((3: \operatorname{Fin}\left(7\right))\right) = p\left((1: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((4: \operatorname{Fin}\left(7\right))\right) = p\left((2: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((5: \operatorname{Fin}\left(7\right))\right) = p\left((3: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((6: \operatorname{Fin}\left(7\right))\right) = p\left((4: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((1: \operatorname{Fin}\left(21\right))) \operatorname{else} ((2: \operatorname{Fin}\left(21\right))))) \operatorname{else} ((\operatorname{if} (p\left((6: \operatorname{Fin}\left(7\right))\right) = p\left((4: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((3: \operatorname{Fin}\left(21\right))) \operatorname{else} ((4: \operatorname{Fin}\left(21\right))))))) \operatorname{else} ((\operatorname{if} (p\left((5: \operatorname{Fin}\left(7\right))\right) = p\left((3: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((6: \operatorname{Fin}\left(7\right))\right) = p\left((4: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((5: \operatorname{Fin}\left(21\right))) \operatorname{else} ((6: \operatorname{Fin}\left(21\right))))) \operatorname{else} ((\operatorname{if} (p\left((6: \operatorname{Fin}\left(7\right))\right) = p\left((4: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((7: \operatorname{Fin}\left(21\right))) \operatorname{else} ((8: \operatorname{Fin}\left(21\right))))))))) \operatorname{else} ((\operatorname{if} (p\left((4: \operatorname{Fin}\left(7\right))\right) = p\left((2: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((5: \operatorname{Fin}\left(7\right))\right) = p\left((3: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((6: \operatorname{Fin}\left(7\right))\right) = p\left((4: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((3: \operatorname{Fin}\left(21\right))) \operatorname{else} ((9: \operatorname{Fin}\left(21\right))))) \operatorname{else} ((\operatorname{if} (p\left((6: \operatorname{Fin}\left(7\right))\right) = p\left((4: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((10: \operatorname{Fin}\left(21\right))) \operatorname{else} ((11: \operatorname{Fin}\left(21\right))))))) \operatorname{else} ((\operatorname{if} (p\left((5: \operatorname{Fin}\left(7\right))\right) = p\left((3: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((6: \operatorname{Fin}\left(7\right))\right) = p\left((4: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((7: \operatorname{Fin}\left(21\right))) \operatorname{else} ((12: \operatorname{Fin}\left(21\right))))) \operatorname{else} ((\operatorname{if} (p\left((6: \operatorname{Fin}\left(7\right))\right) = p\left((4: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((13: \operatorname{Fin}\left(21\right))) \operatorname{else} ((14: \operatorname{Fin}\left(21\right))))))))))) \operatorname{else} ((\operatorname{if} (p\left((3: \operatorname{Fin}\left(7\right))\right) = p\left((1: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((4: \operatorname{Fin}\left(7\right))\right) = p\left((2: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((5: \operatorname{Fin}\left(7\right))\right) = p\left((3: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((6: \operatorname{Fin}\left(7\right))\right) = p\left((4: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((2: \operatorname{Fin}\left(21\right))) \operatorname{else} ((15: \operatorname{Fin}\left(21\right))))) \operatorname{else} ((\operatorname{if} (p\left((6: \operatorname{Fin}\left(7\right))\right) = p\left((4: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((9: \operatorname{Fin}\left(21\right))) \operatorname{else} ((16: \operatorname{Fin}\left(21\right))))))) \operatorname{else} ((\operatorname{if} (p\left((5: \operatorname{Fin}\left(7\right))\right) = p\left((3: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((6: \operatorname{Fin}\left(7\right))\right) = p\left((4: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((6: \operatorname{Fin}\left(21\right))) \operatorname{else} ((17: \operatorname{Fin}\left(21\right))))) \operatorname{else} ((\operatorname{if} (p\left((6: \operatorname{Fin}\left(7\right))\right) = p\left((4: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((12: \operatorname{Fin}\left(21\right))) \operatorname{else} ((18: \operatorname{Fin}\left(21\right))))))))) \operatorname{else} ((\operatorname{if} (p\left((4: \operatorname{Fin}\left(7\right))\right) = p\left((2: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((5: \operatorname{Fin}\left(7\right))\right) = p\left((3: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((6: \operatorname{Fin}\left(7\right))\right) = p\left((4: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((4: \operatorname{Fin}\left(21\right))) \operatorname{else} ((16: \operatorname{Fin}\left(21\right))))) \operatorname{else} ((\operatorname{if} (p\left((6: \operatorname{Fin}\left(7\right))\right) = p\left((4: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((11: \operatorname{Fin}\left(21\right))) \operatorname{else} ((19: \operatorname{Fin}\left(21\right))))))) \operatorname{else} ((\operatorname{if} (p\left((5: \operatorname{Fin}\left(7\right))\right) = p\left((3: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((6: \operatorname{Fin}\left(7\right))\right) = p\left((4: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((8: \operatorname{Fin}\left(21\right))) \operatorname{else} ((18: \operatorname{Fin}\left(21\right))))) \operatorname{else} ((\operatorname{if} (p\left((6: \operatorname{Fin}\left(7\right))\right) = p\left((4: \operatorname{Fin}\left(7\right))\right)) \operatorname{then} ((14: \operatorname{Fin}\left(21\right))) \operatorname{else} ((20: \operatorname{Fin}\left(21\right))))))))))))) \operatorname{else} ((0: \operatorname{Fin}\left(21\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows.boundaryClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233128: six-colour complementary-pair exclusion on a seven-column square strip*. URL: <https://oeis.org/A233128>.

*Commentary.*

Class 0 precedes colour 2 and has 128 continuations within that sector. For a proper boundary, record the five bits indicating whether each label differs from the label two positions earlier. Relabelling leaves these bits fixed; reversal reverses them. The 32 bit words have 20 reversal orbits. Their representatives, in class order, are 0101010, 0101012, 0101020, 0101021, 0101212, 0101210, 0101202, 0101201, 0102021, 0102010, 0102012, 0102120, 0102101, 0102102, 0121210, 0120201, 0121012, 0120102, 0120210, 0120120. The class sizes in the same order are 6,12,12,12,6,12,12,12,12,6,12,12,6,12,6,12,6,12,6,6.

**Definition 1.7 (Exact class transitions).**

$$\forall (i: \operatorname{Fin}\left(21\right)), (\forall (k: \operatorname{Fin}\left(21\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{transfer}\left(i, k\right) = ![![128, 128, 256, 256, 128, 128, 256, 128, 0, 128, 128, 128, 128, 0, 0, 128, 0, 128, 0, 64, 0], ![0, 384, 512, 512, 256, 256, 512, 256, 0, 256, 256, 256, 256, 0, 0, 256, 0, 256, 0, 128, 0], ![0, 256, 384, 512, 256, 128, 256, 128, 128, 256, 256, 256, 256, 0, 0, 128, 256, 128, 128, 0, 0], ![0, 256, 512, 384, 128, 256, 512, 256, 0, 256, 128, 256, 256, 128, 0, 256, 0, 256, 0, 128, 0], ![0, 128, 256, 128, 256, 128, 256, 256, 128, 256, 0, 128, 128, 128, 128, 128, 128, 128, 128, 128, 0], ![0, 256, 256, 512, 256, 256, 256, 256, 256, 256, 256, 256, 256, 0, 0, 0, 256, 0, 256, 0, 0], ![0, 256, 256, 512, 256, 128, 384, 128, 0, 256, 256, 256, 256, 0, 0, 128, 0, 128, 128, 128, 0], ![0, 128, 128, 256, 256, 128, 128, 384, 256, 256, 128, 128, 256, 128, 128, 0, 256, 0, 256, 0, 0], ![0, 0, 128, 0, 128, 128, 0, 256, 384, 128, 0, 128, 0, 128, 256, 0, 256, 0, 128, 0, 128], ![0, 128, 256, 256, 256, 128, 256, 256, 128, 384, 128, 128, 128, 128, 128, 128, 256, 128, 128, 0, 0], ![0, 256, 512, 256, 0, 256, 512, 256, 0, 256, 256, 256, 256, 0, 0, 256, 0, 256, 0, 128, 0], ![0, 128, 256, 256, 128, 128, 256, 128, 128, 128, 128, 256, 256, 0, 0, 128, 128, 128, 128, 128, 0], ![0, 128, 256, 256, 128, 128, 256, 256, 0, 128, 128, 256, 384, 128, 0, 128, 0, 128, 128, 128, 0], ![0, 0, 0, 256, 256, 0, 0, 256, 256, 256, 0, 0, 256, 256, 256, 0, 256, 0, 256, 0, 0], ![0, 0, 0, 0, 128, 0, 0, 128, 256, 128, 0, 0, 0, 128, 384, 0, 256, 0, 128, 0, 128], ![0, 256, 256, 512, 256, 0, 256, 0, 0, 256, 256, 256, 256, 0, 0, 256, 0, 0, 256, 128, 0], ![0, 0, 256, 0, 128, 128, 0, 256, 256, 256, 0, 128, 0, 128, 256, 0, 384, 128, 0, 0, 128], ![0, 256, 256, 512, 256, 0, 256, 0, 0, 256, 256, 256, 256, 0, 0, 0, 256, 256, 0, 0, 0], ![0, 0, 128, 0, 128, 128, 128, 256, 128, 128, 0, 128, 128, 128, 128, 128, 0, 0, 256, 128, 0], ![0, 128, 0, 256, 256, 0, 256, 0, 0, 0, 128, 256, 256, 0, 0, 128, 0, 0, 256, 256, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 256, 0, 0, 0, 0, 0, 256, 0, 256, 0, 0, 0, 256]]\left(i, k\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233128: six-colour complementary-pair exclusion on a seven-column square strip*. URL: <https://oeis.org/A233128>.

*Commentary.*

The source class indexes rows and the destination class indexes columns. The entries include individual-colour scanner multiplicities.

**Definition 1.8 (Single-row counts).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{PairRow}), (\forall (k: \operatorname{Fin}\left(21\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{classCount}\left(s, p, k\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{Row}} (((\operatorname{if} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{compatible}\left(p, c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{boundaryClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left(s, c\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{labels}\left(c\right)\right) = k)))) \operatorname{then} (1) \operatorname{else} (0)): \operatorname{Int})))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows.classCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233128: six-colour complementary-pair exclusion on a seven-column square strip*. URL: <https://oeis.org/A233128>.

*Commentary.*

The sum is over the owner's individual-colour Row type.

**Definition 1.9 (Anchored first-row distribution).**

$$\forall (k: \operatorname{Fin}\left(21\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{firstCount}\left(k\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{Row}} (((\operatorname{if} ((c\left((0: \operatorname{Fin}\left(7\right))\right) = (0: \operatorname{Fin}\left(6\right))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{boundaryClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), c\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233128SquareStrip}.\operatorname{labels}\left(c\right)\right) = k)))) \operatorname{then} (1) \operatorname{else} (0)): \operatorname{Int})))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows.firstCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233128: six-colour complementary-pair exclusion on a seven-column square strip*. URL: <https://oeis.org/A233128>.

*Commentary.*

The first colour is zero and both initial flags are false.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows.Valid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows.bonds`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows.boundaryClass`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows.classCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows.firstCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows.labels`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows.transfer`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer](HardinA233255PairTransfer.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
