# Literal arrays and boundary classes

## Abstract

Literal six-column complementary-pair square-strip definitions.

OEIS A233127 revision 6 defines the count and records Hardin’s empirical recurrence. All declaration names below are fully qualified Lean names. val explicitly converts a finite index or colour to Nat. Nat.div denotes natural quotient and Nat.mod its nonnegative remainder; neither operation occurs in these definitions. The six-column Row type and horizontal predicate rowLegal are reused from HardinA233254TriangleStrip. Boundary is reused from HardinA233255PairTransfer. A valid boundary records that colour 1 has occurred, adjacent labels differ, and before colour 2 occurs neither member of its complementary pair occurs.

**Definition 1.1 (Vertical bonds).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row}), (\forall (d: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{bonds}\left(c, d\right) = \forall (j: \operatorname{Fin}\left(6\right)), ((c\left(j\right) \ne d\left(j\right)) \land ((\operatorname{val}\left(c\left(j\right)\right)) + (\operatorname{val}\left(d\left(j\right)\right)) \ne 5))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows.bonds` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233127: six-colour complementary-pair exclusion on a six-column square strip*. URL: <https://oeis.org/A233127>.

*Commentary.*

Only equal columns in consecutive rows are joined. Diagonals are free.

**Definition 1.2 (The literal filtered finite count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(((A: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right)) \to \operatorname{Fin}\left(6\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthLegal}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{rowLegal}, \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{bonds}, A\right))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right)) \to \operatorname{Fin}\left(6\right)\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233127: six-colour complementary-pair exclusion on a six-column square strip*. URL: <https://oeis.org/A233127>.

*Commentary.*

The filter uses the owner predicate widthLegal directly. It fixes the upper-left cell to zero, applies rowLegal to every row and bonds between successive rows, and applies the owner's widthNormal with initial flags (false,false). Thus every 2, 3 or 4 has an earlier 1, and every 3 has an earlier 2, in row-major order. The first-cell existential is false at height zero, so a 0 = 0.

**Definition 1.3 (Complementary-pair labels).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{labels}\left(c\right) = ((j: \operatorname{Fin}\left(6\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(j\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows.labels` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233127: six-colour complementary-pair exclusion on a six-column square strip*. URL: <https://oeis.org/A233127>.

*Commentary.*

The label map is the published beta, applied separately to each cell.

**Definition 1.4 (Vertical label compatibility).**

$$\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{Boundary}), (\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{compatible}\left(p, c\right) = \forall (j: \operatorname{Fin}\left(6\right)), (p\left(j\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(j\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233127: six-colour complementary-pair exclusion on a six-column square strip*. URL: <https://oeis.org/A233127>.

*Commentary.*

Every preceding label excludes the same label in the following row.

**Definition 1.5 (Valid scanner boundaries).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{Boundary}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{Valid}\left(s, p\right) = \left((\operatorname{Prod}.\operatorname{fst}\left(s\right) = \operatorname{Bool}.\operatorname{true}) \land ((\forall (j: \operatorname{Fin}\left(5\right)), (p\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \ne p\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right))) \land ((\operatorname{Prod}.\operatorname{snd}\left(s\right) = \operatorname{Bool}.\operatorname{false}) \implies (\forall (j: \operatorname{Fin}\left(6\right)), (p\left(j\right) \ne (2: \operatorname{Fin}\left(3\right))))))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233127: six-colour complementary-pair exclusion on a six-column square strip*. URL: <https://oeis.org/A233127>.

*Commentary.*

The first flag is true; the second flag excludes label 2 when false.

**Definition 1.6 (Boundary classes).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{Boundary}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{boundaryClass}\left(s, p\right) = (\operatorname{if} (\operatorname{Prod}.\operatorname{snd}\left(s\right)) \operatorname{then} ((\operatorname{if} (p\left((2: \operatorname{Fin}\left(6\right))\right) = p\left((0: \operatorname{Fin}\left(6\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((3: \operatorname{Fin}\left(6\right))\right) = p\left((1: \operatorname{Fin}\left(6\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((4: \operatorname{Fin}\left(6\right))\right) = p\left((2: \operatorname{Fin}\left(6\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((5: \operatorname{Fin}\left(6\right))\right) = p\left((3: \operatorname{Fin}\left(6\right))\right)) \operatorname{then} ((1: \operatorname{Fin}\left(11\right))) \operatorname{else} ((2: \operatorname{Fin}\left(11\right))))) \operatorname{else} ((\operatorname{if} (p\left((5: \operatorname{Fin}\left(6\right))\right) = p\left((3: \operatorname{Fin}\left(6\right))\right)) \operatorname{then} ((4: \operatorname{Fin}\left(11\right))) \operatorname{else} ((3: \operatorname{Fin}\left(11\right))))))) \operatorname{else} ((\operatorname{if} (p\left((4: \operatorname{Fin}\left(6\right))\right) = p\left((2: \operatorname{Fin}\left(6\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((5: \operatorname{Fin}\left(6\right))\right) = p\left((3: \operatorname{Fin}\left(6\right))\right)) \operatorname{then} ((4: \operatorname{Fin}\left(11\right))) \operatorname{else} ((5: \operatorname{Fin}\left(11\right))))) \operatorname{else} ((\operatorname{if} (p\left((5: \operatorname{Fin}\left(6\right))\right) = p\left((3: \operatorname{Fin}\left(6\right))\right)) \operatorname{then} ((7: \operatorname{Fin}\left(11\right))) \operatorname{else} ((6: \operatorname{Fin}\left(11\right))))))))) \operatorname{else} ((\operatorname{if} (p\left((3: \operatorname{Fin}\left(6\right))\right) = p\left((1: \operatorname{Fin}\left(6\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((4: \operatorname{Fin}\left(6\right))\right) = p\left((2: \operatorname{Fin}\left(6\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((5: \operatorname{Fin}\left(6\right))\right) = p\left((3: \operatorname{Fin}\left(6\right))\right)) \operatorname{then} ((2: \operatorname{Fin}\left(11\right))) \operatorname{else} ((10: \operatorname{Fin}\left(11\right))))) \operatorname{else} ((\operatorname{if} (p\left((5: \operatorname{Fin}\left(6\right))\right) = p\left((3: \operatorname{Fin}\left(6\right))\right)) \operatorname{then} ((5: \operatorname{Fin}\left(11\right))) \operatorname{else} ((9: \operatorname{Fin}\left(11\right))))))) \operatorname{else} ((\operatorname{if} (p\left((4: \operatorname{Fin}\left(6\right))\right) = p\left((2: \operatorname{Fin}\left(6\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((5: \operatorname{Fin}\left(6\right))\right) = p\left((3: \operatorname{Fin}\left(6\right))\right)) \operatorname{then} ((3: \operatorname{Fin}\left(11\right))) \operatorname{else} ((9: \operatorname{Fin}\left(11\right))))) \operatorname{else} ((\operatorname{if} (p\left((5: \operatorname{Fin}\left(6\right))\right) = p\left((3: \operatorname{Fin}\left(6\right))\right)) \operatorname{then} ((6: \operatorname{Fin}\left(11\right))) \operatorname{else} ((8: \operatorname{Fin}\left(11\right))))))))))) \operatorname{else} ((0: \operatorname{Fin}\left(11\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows.boundaryClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233127: six-colour complementary-pair exclusion on a six-column square strip*. URL: <https://oeis.org/A233127>.

*Commentary.*

Class 0 precedes colour 2. The ten completed classes are represented by 010101, 010102, 010120, 010121, 010201, 010210, 010212, 012012, 012021 and 012120. Their orbit sizes under label permutation and reversal are 6,12,12,12,12,12,6,6,12,6.

**Definition 1.7 (Class transition matrix).**

$$\forall (i: \operatorname{Fin}\left(11\right)), (\forall (k: \operatorname{Fin}\left(11\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{transfer}\left(i, k\right) = ![![64, 64, 128, 64, 128, 128, 0, 32, 0, 64, 32], ![0, 192, 256, 128, 256, 256, 0, 64, 0, 128, 64], ![0, 128, 256, 64, 192, 192, 64, 64, 0, 128, 64], ![0, 64, 64, 192, 128, 64, 128, 64, 64, 64, 64], ![0, 128, 192, 128, 256, 192, 64, 64, 0, 128, 64], ![0, 128, 192, 64, 192, 256, 0, 64, 0, 128, 64], ![0, 0, 64, 128, 64, 0, 192, 64, 64, 64, 64], ![0, 64, 128, 128, 128, 128, 128, 128, 0, 128, 64], ![0, 0, 0, 128, 0, 0, 128, 0, 128, 0, 64], ![0, 64, 128, 64, 128, 128, 64, 64, 0, 192, 0], ![0, 64, 128, 128, 128, 128, 128, 64, 64, 0, 128]]\left(i, k\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233127: six-colour complementary-pair exclusion on a six-column square strip*. URL: <https://oeis.org/A233127>.

*Commentary.*

Rows are source classes and columns are destination classes.

**Definition 1.8 (Single-row continuation counts).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{Boundary}), (\forall (k: \operatorname{Fin}\left(11\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{classCount}\left(s, p, k\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row}} (((\operatorname{if} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{compatible}\left(p, c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{boundaryClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left(s, c\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{labels}\left(c\right)\right) = k)))) \operatorname{then} (1) \operatorname{else} (0)): \operatorname{Int})))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows.classCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233127: six-colour complementary-pair exclusion on a six-column square strip*. URL: <https://oeis.org/A233127>.

*Commentary.*

The sum is over all 6^6 individual colour rows with the original scanner.

**Definition 1.9 (First-row class distribution).**

$$\forall (k: \operatorname{Fin}\left(11\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{firstCount}\left(k\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row}} (((\operatorname{if} ((c\left((0: \operatorname{Fin}\left(6\right))\right) = (0: \operatorname{Fin}\left(6\right))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{boundaryClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), c\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{labels}\left(c\right)\right) = k)))) \operatorname{then} (1) \operatorname{else} (0)): \operatorname{Int})))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows.firstCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233127: six-colour complementary-pair exclusion on a six-column square strip*. URL: <https://oeis.org/A233127>.

*Commentary.*

The first colour is fixed to zero and both initial scanner flags are false.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows.Valid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows.bonds`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows.boundaryClass`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows.classCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows.firstCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows.labels`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows.transfer`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip](HardinA233254TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer](HardinA233255PairTransfer.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
