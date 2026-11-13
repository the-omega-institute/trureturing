# Literal arrays and boundary classes

## Abstract

Hardin’s recurrence for normalized five-column complementary-pair square strips.

OEIS A233126 revision 6 defines the count and records Hardin’s empirical recurrence. All declaration names below are fully qualified Lean names. Fin.val explicitly converts a finite index or colour to Nat. Nat.div denotes natural quotient and Nat.mod its nonnegative remainder; neither operation occurs in these definitions. The five-column Row type and horizontal predicate rowLegal are reused from HardinA233253TriangleStrip. Boundary and Valid are reused from HardinA233254TriangleStrip. A valid boundary records that colour 1 has occurred, adjacent labels differ, and before colour 2 occurs neither member of its complementary pair occurs.

**Definition 1.1 (Vertical bonds).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}), (\forall (d: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{bonds}\left(c, d\right) = \forall (j: \operatorname{Fin}\left(5\right)), ((c\left(j\right) \ne d\left(j\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left(j\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(d\left(j\right)\right)) \ne 5))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.bonds` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233126: six-colour complementary-pair exclusion on a five-column square strip*. URL: <https://oeis.org/A233126>.

*Commentary.*

Only equal columns in consecutive rows are joined. Diagonals are free.

**Definition 1.2 (The literal filtered finite count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(((A: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(5\right)) \to \operatorname{Fin}\left(6\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthLegal}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rowLegal}, \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{bonds}, A\right))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(5\right)) \to \operatorname{Fin}\left(6\right)\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233126: six-colour complementary-pair exclusion on a five-column square strip*. URL: <https://oeis.org/A233126>.

*Commentary.*

The filter uses the owner predicate widthLegal directly. It fixes the upper-left cell to zero, applies rowLegal to every row and bonds between successive rows, and applies the owner's widthNormal with initial flags (false,false). Thus every 2, 3 or 4 has an earlier 1, and every 3 has an earlier 2, in row-major order. The first-cell existential is false at height zero, so a 0 = 0.

**Definition 1.3 (Complementary-pair labels).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{labels}\left(c\right) = ((j: \operatorname{Fin}\left(5\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(j\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.labels` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233126: six-colour complementary-pair exclusion on a five-column square strip*. URL: <https://oeis.org/A233126>.

*Commentary.*

The label map is the published beta, applied separately to each cell.

**Definition 1.4 (Vertical label compatibility).**

$$\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Boundary}), (\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{compatible}\left(p, c\right) = \forall (j: \operatorname{Fin}\left(5\right)), (p\left(j\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(j\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233126: six-colour complementary-pair exclusion on a five-column square strip*. URL: <https://oeis.org/A233126>.

*Commentary.*

Every preceding label excludes the same label in the following row.

**Definition 1.5 (Boundary classes).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Boundary}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{boundaryClass}\left(s, p\right) = (\operatorname{if} (\operatorname{Prod}.\operatorname{snd}\left(s\right)) \operatorname{then} ((\operatorname{if} ((p\left((0: \operatorname{Fin}\left(5\right))\right) = p\left((2: \operatorname{Fin}\left(5\right))\right)) \land (p\left((2: \operatorname{Fin}\left(5\right))\right) = p\left((4: \operatorname{Fin}\left(5\right))\right))) \operatorname{then} ((\operatorname{if} (p\left((1: \operatorname{Fin}\left(5\right))\right) = p\left((3: \operatorname{Fin}\left(5\right))\right)) \operatorname{then} ((1: \operatorname{Fin}\left(7\right))) \operatorname{else} ((3: \operatorname{Fin}\left(7\right))))) \operatorname{else} ((\operatorname{if} (p\left((1: \operatorname{Fin}\left(5\right))\right) = p\left((3: \operatorname{Fin}\left(5\right))\right)) \operatorname{then} ((\operatorname{if} (p\left((0: \operatorname{Fin}\left(5\right))\right) = p\left((4: \operatorname{Fin}\left(5\right))\right)) \operatorname{then} ((6: \operatorname{Fin}\left(7\right))) \operatorname{else} ((2: \operatorname{Fin}\left(7\right))))) \operatorname{else} ((\operatorname{if} ((p\left((0: \operatorname{Fin}\left(5\right))\right) = p\left((3: \operatorname{Fin}\left(5\right))\right)) \land (p\left((1: \operatorname{Fin}\left(5\right))\right) = p\left((4: \operatorname{Fin}\left(5\right))\right))) \operatorname{then} ((5: \operatorname{Fin}\left(7\right))) \operatorname{else} ((4: \operatorname{Fin}\left(7\right))))))))) \operatorname{else} ((0: \operatorname{Fin}\left(7\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.boundaryClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233126: six-colour complementary-pair exclusion on a five-column square strip*. URL: <https://oeis.org/A233126>.

*Commentary.*

Class 0 precedes colour 2. Classes 1 through 6 are the label-permutation and reversal orbits represented by 01010, 01012, 01020, 01021, 01201 and 01210, respectively. Their sizes are 6,12,6,12,6,6.

**Definition 1.6 (Class transition matrix).**

$$\forall (i: \operatorname{Fin}\left(7\right)), (\forall (k: \operatorname{Fin}\left(7\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{transfer}\left(i, k\right) = ![![32, 32, 64, 32, 32, 0, 32], ![0, 96, 128, 64, 64, 0, 64], ![0, 64, 96, 64, 64, 32, 32], ![0, 64, 128, 64, 64, 0, 64], ![0, 32, 64, 32, 96, 32, 32], ![0, 0, 64, 0, 64, 64, 0], ![0, 64, 64, 64, 64, 0, 64]]\left(i, k\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233126: six-colour complementary-pair exclusion on a five-column square strip*. URL: <https://oeis.org/A233126>.

*Commentary.*

Rows are source classes and columns are destination classes.

**Definition 1.7 (Single-row continuation counts).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Boundary}), (\forall (k: \operatorname{Fin}\left(7\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{classCount}\left(s, p, k\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}} (((\operatorname{if} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{compatible}\left(p, c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{boundaryClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left(s, c\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{labels}\left(c\right)\right) = k)))) \operatorname{then} (1) \operatorname{else} (0)): \operatorname{Int})))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.classCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233126: six-colour complementary-pair exclusion on a five-column square strip*. URL: <https://oeis.org/A233126>.

*Commentary.*

The sum is over all 6^5 individual colour rows with the original scanner.

**Definition 1.8 (First-row class distribution).**

$$\forall (k: \operatorname{Fin}\left(7\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{firstCount}\left(k\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}} (((\operatorname{if} ((c\left((0: \operatorname{Fin}\left(5\right))\right) = (0: \operatorname{Fin}\left(6\right))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{boundaryClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), c\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{labels}\left(c\right)\right) = k)))) \operatorname{then} (1) \operatorname{else} (0)): \operatorname{Int})))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.firstCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233126: six-colour complementary-pair exclusion on a five-column square strip*. URL: <https://oeis.org/A233126>.

*Commentary.*

The first colour is fixed to zero and both initial scanner flags are false.

**Theorem 1.9 (Expanding the label sum).**

$$\forall (g: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Boundary} \to \operatorname{Int}), (\sum_{q: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Boundary}} (g\left(q\right)) = \sum_{a: \operatorname{Fin}\left(3\right)} (\sum_{b: \operatorname{Fin}\left(3\right)} (\sum_{c: \operatorname{Fin}\left(3\right)} (\sum_{d: \operatorname{Fin}\left(3\right)} (\sum_{e: \operatorname{Fin}\left(3\right)} (g\left(![a, b, c, d, e]\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.label_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233126: six-colour complementary-pair exclusion on a five-column square strip*. URL: <https://oeis.org/A233126>.

*Commentary.*

The function-space sum expands into five independent label sums.

**Theorem 1.10 (Compatibility-free row validity).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}), ((\operatorname{Prod}.\operatorname{fst}\left(s\right) = \operatorname{Bool}.\operatorname{true}) \implies ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \implies ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right)) \implies (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Valid}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left(s, c\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{labels}\left(c\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.row_valid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233126: six-colour complementary-pair exclusion on a five-column square strip*. URL: <https://oeis.org/A233126>.

*Commentary.*

Horizontal legality and the scanner preserve validity once colour one has occurred, independently of inter-row bonds.

**Theorem 1.11 (First-row validity).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}), (((c\left((0: \operatorname{Fin}\left(5\right))\right) = 0) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), c\right)))) \implies (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Valid}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), c\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{labels}\left(c\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.initial_valid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233126: six-colour complementary-pair exclusion on a five-column square strip*. URL: <https://oeis.org/A233126>.

*Commentary.*

A legal normalized first row determines a valid scanner boundary.

**Theorem 1.12 (Single-row certificate).**

$$(\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Boundary}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Valid}\left(s, p\right)) \implies (\forall (k: \operatorname{Fin}\left(7\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{classCount}\left(s, p, k\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{transfer}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{boundaryClass}\left(s, p\right), k\right)))))) \land (\forall (k: \operatorname{Fin}\left(7\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{firstCount}\left(k\right) = ![8, 0, 8, 4, 8, 4, 4]\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233126: six-colour complementary-pair exclusion on a five-column square strip*. URL: <https://oeis.org/A233126>.

*Commentary.*

Exact scanner fibres reduce the transition counts to 3^5 label rows. The single-row certificate supplies the numerical premises of the all-height induction.

**Theorem 1.13 (The recurrence at every height).**

$$\forall (n: \operatorname{Nat}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{a}\left((n) + (7)\right): \operatorname{Int}) = ((((((544) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{a}\left((n) + (6)\right): \operatorname{Int}))) - ((82944) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{a}\left((n) + (5)\right): \operatorname{Int})))) + ((5144576) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{a}\left((n) + (4)\right): \operatorname{Int})))) - ((146800640) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{a}\left((n) + (3)\right): \operatorname{Int})))) + ((1879048192) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{a}\left((n) + (2)\right): \operatorname{Int})))) - ((8589934592) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{a}\left((n) + (1)\right): \operatorname{Int}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233126` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233126","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233126: six-colour complementary-pair exclusion on a five-column square strip*. URL: <https://oeis.org/A233126>.

*Commentary.*

The complementary-pair labels are the fibres {0,5}, {1,4}, {2,3} of D5.S3.Observer.Separation.BooleanRankThreeK4.beta. Exact scanner fibres retain the original order restrictions and colour multiplicities. The first-row distribution is (8,0,8,4,8,4,4). The displayed matrix gives continuation counts from every valid boundary. The class reduction at all heights is the linear semiconjugacy iteration: a class-constant continuation remains class-constant after one row, hence after every number of rows. The unseen sector has eigenvalue 32. The six-class seen sector has characteristic polynomial (x+32) times (x^5-512x^4+66560x^3-3014656x^2+50331648x-268435456). The initial row distribution annihilates the -32 mode. Multiplying this quintic by x-32 gives precisely the six coefficients in the recurrence. The integer calculation therefore applies to the literal filtered count for every n+7, with n a natural number.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.bonds`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.boundaryClass`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.classCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.firstCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.initial_valid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.label_sum`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.labels`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.row_valid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.transfer`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip](HardinA233253TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip](HardinA233254TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge](HardinA233255LiteralBridge.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
