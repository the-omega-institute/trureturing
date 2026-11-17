# Literal arrays and boundary classes

## Abstract

The generating function for normalized four-column complementary-pair square strips.

OEIS A233125 revision 10 defines the count. The generating function is attributed there to R. J. Mathar. All declaration names below are fully qualified Lean names. Fin.val explicitly converts a finite index or colour to Nat. Nat.div denotes natural quotient and Nat.mod its nonnegative remainder; neither operation occurs in these definitions.

**Definition 1.1 (Rows).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{Row} = \left(\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(6\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; R. J. Mathar; OEIS Foundation Inc. (2013). *OEIS A233125: six-colour complementary-pair exclusion on a four-column square strip*. URL: <https://oeis.org/A233125>.

*Commentary.*

A row contains four individual colours.

**Definition 1.2 (Horizontal bonds).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{rowLegal}\left(c\right) = \forall (j: \operatorname{Fin}\left(3\right)), ((c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \ne c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right)) \ne 5)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.rowLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; R. J. Mathar; OEIS Foundation Inc. (2013). *OEIS A233125: six-colour complementary-pair exclusion on a four-column square strip*. URL: <https://oeis.org/A233125>.

*Commentary.*

Fin.castSucc and Fin.succ select consecutive columns.

**Definition 1.3 (Deciding horizontal bonds).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{Row}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{decidableRowLegal}\left(c\right): \operatorname{Decidable}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{rowLegal}\left(c\right))\right)) = \operatorname{inferInstanceAs}\left((\operatorname{Decidable}\left((\forall (j: \operatorname{Fin}\left(3\right)), ((c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \ne c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right)) \ne 5)))\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.decidableRowLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; R. J. Mathar; OEIS Foundation Inc. (2013). *OEIS A233125: six-colour complementary-pair exclusion on a four-column square strip*. URL: <https://oeis.org/A233125>.

*Commentary.*

The defining expression is inferInstanceAs for the displayed universally quantified conjunction.

**Definition 1.4 (Vertical bonds).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{Row}), (\forall (d: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{bonds}\left(c, d\right) = \forall (j: \operatorname{Fin}\left(4\right)), ((c\left(j\right) \ne d\left(j\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left(j\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(d\left(j\right)\right)) \ne 5))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.bonds` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; R. J. Mathar; OEIS Foundation Inc. (2013). *OEIS A233125: six-colour complementary-pair exclusion on a four-column square strip*. URL: <https://oeis.org/A233125>.

*Commentary.*

Only equal columns in consecutive rows are joined. Diagonals are free.

**Definition 1.5 (The literal filtered finite count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(((A: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)) \to \operatorname{Fin}\left(6\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthLegal}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{rowLegal}, \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{bonds}, A\right))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)) \to \operatorname{Fin}\left(6\right)\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.a` (`✓ std3`).

*Citation.* R. H. Hardin; R. J. Mathar; OEIS Foundation Inc. (2013). *OEIS A233125: six-colour complementary-pair exclusion on a four-column square strip*. URL: <https://oeis.org/A233125>.

*Commentary.*

The filter uses the owner predicate widthLegal directly. It fixes the upper-left cell to zero, applies rowLegal to every row and bonds between successive rows, and applies the owner's widthNormal with initial flags (false,false). Thus every 2, 3 or 4 has an earlier 1, and every 3 has an earlier 2, in row-major order. The first-cell existential is false at height zero, so a 0 = 0.

**Definition 1.6 (Complementary-pair labels).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{labels}\left(c\right) = ((j: \operatorname{Fin}\left(4\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(j\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.labels` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; R. J. Mathar; OEIS Foundation Inc. (2013). *OEIS A233125: six-colour complementary-pair exclusion on a four-column square strip*. URL: <https://oeis.org/A233125>.

*Commentary.*

The label map is the published beta, applied separately to each cell.

**Definition 1.7 (Vertical label compatibility).**

$$\forall (p: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right)), (\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{compatible}\left(p, c\right) = \forall (j: \operatorname{Fin}\left(4\right)), (p\left(j\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(j\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; R. J. Mathar; OEIS Foundation Inc. (2013). *OEIS A233125: six-colour complementary-pair exclusion on a four-column square strip*. URL: <https://oeis.org/A233125>.

*Commentary.*

Every preceding label excludes the same label in the following row.

**Definition 1.8 (Reachable boundaries).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{Valid}\left(s, p\right) = \left((\operatorname{Prod}.\operatorname{fst}\left(s\right) = \operatorname{Bool}.\operatorname{true}) \land ((\forall (j: \operatorname{Fin}\left(3\right)), (p\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \ne p\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right))) \land ((\operatorname{Prod}.\operatorname{snd}\left(s\right) = \operatorname{Bool}.\operatorname{false}) \implies (\forall (j: \operatorname{Fin}\left(4\right)), (p\left(j\right) \ne (2: \operatorname{Fin}\left(3\right))))))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; R. J. Mathar; OEIS Foundation Inc. (2013). *OEIS A233125: six-colour complementary-pair exclusion on a four-column square strip*. URL: <https://oeis.org/A233125>.

*Commentary.*

Colour 1 has occurred. Adjacent labels differ. Before colour 2 occurs, neither member of its complementary pair occurs.

**Definition 1.9 (Boundary classes).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{boundaryClass}\left(s, p\right) = (\operatorname{if} (\operatorname{Prod}.\operatorname{snd}\left(s\right)) \operatorname{then} ((\operatorname{if} ((p\left((0: \operatorname{Fin}\left(4\right))\right) = p\left((2: \operatorname{Fin}\left(4\right))\right)) \land (p\left((1: \operatorname{Fin}\left(4\right))\right) = p\left((3: \operatorname{Fin}\left(4\right))\right))) \operatorname{then} ((1: \operatorname{Fin}\left(4\right))) \operatorname{else} ((\operatorname{if} (p\left((0: \operatorname{Fin}\left(4\right))\right) = p\left((3: \operatorname{Fin}\left(4\right))\right)) \operatorname{then} ((3: \operatorname{Fin}\left(4\right))) \operatorname{else} ((2: \operatorname{Fin}\left(4\right))))))) \operatorname{else} ((0: \operatorname{Fin}\left(4\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.boundaryClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; R. J. Mathar; OEIS Foundation Inc. (2013). *OEIS A233125: six-colour complementary-pair exclusion on a four-column square strip*. URL: <https://oeis.org/A233125>.

*Commentary.*

Class 0 is the unseen sector. Classes 1, 2, 3 are alternating, unequal endpoints without alternation, and equal endpoints.

**Definition 1.10 (Class transition matrix).**

$$\forall (i: \operatorname{Fin}\left(4\right)), (\forall (k: \operatorname{Fin}\left(4\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{transfer}\left(i, k\right) = ![![16, 16, 32, 8], ![0, 48, 64, 16], ![0, 32, 64, 16], ![0, 16, 32, 32]]\left(i, k\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; R. J. Mathar; OEIS Foundation Inc. (2013). *OEIS A233125: six-colour complementary-pair exclusion on a four-column square strip*. URL: <https://oeis.org/A233125>.

*Commentary.*

Rows are source classes and columns are destination classes.

**Definition 1.11 (Single-row continuation counts).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right)), (\forall (k: \operatorname{Fin}\left(4\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{classCount}\left(s, p, k\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{Row}} (((\operatorname{if} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{compatible}\left(p, c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{boundaryClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left(s, c\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{labels}\left(c\right)\right) = k)))) \operatorname{then} (1) \operatorname{else} (0)): \operatorname{Int})))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.classCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; R. J. Mathar; OEIS Foundation Inc. (2013). *OEIS A233125: six-colour complementary-pair exclusion on a four-column square strip*. URL: <https://oeis.org/A233125>.

*Commentary.*

The sum is over all 6^4 individual colour rows with the original scanner.

**Definition 1.12 (First-row class distribution).**

$$\forall (k: \operatorname{Fin}\left(4\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{firstCount}\left(k\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{Row}} (((\operatorname{if} ((c\left((0: \operatorname{Fin}\left(4\right))\right) = (0: \operatorname{Fin}\left(6\right))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{boundaryClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), c\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{labels}\left(c\right)\right) = k)))) \operatorname{then} (1) \operatorname{else} (0)): \operatorname{Int})))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.firstCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; R. J. Mathar; OEIS Foundation Inc. (2013). *OEIS A233125: six-colour complementary-pair exclusion on a four-column square strip*. URL: <https://oeis.org/A233125>.

*Commentary.*

The first colour is fixed to zero and both initial scanner flags are false.

**Theorem 1.13 (Summing over label rows).**

$$\forall (g: (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right)) \to \operatorname{Int}), (\sum_{q: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right)} (g\left(q\right)) = \sum_{a: \operatorname{Fin}\left(3\right)} (\sum_{b: \operatorname{Fin}\left(3\right)} (\sum_{c: \operatorname{Fin}\left(3\right)} (\sum_{d: \operatorname{Fin}\left(3\right)} (g\left((![a, b, c, d])\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.label_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; R. J. Mathar; OEIS Foundation Inc. (2013). *OEIS A233125: six-colour complementary-pair exclusion on a four-column square strip*. URL: <https://oeis.org/A233125>.

*Commentary.*

The sum over all four-column label rows equals four nested sums over the three labels, for every integer-valued function.

**Theorem 1.14 (Single-row certificate).**

$$(\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{Valid}\left(s, p\right)) \implies (\forall (k: \operatorname{Fin}\left(4\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{classCount}\left(s, p, k\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{transfer}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{boundaryClass}\left(s, p\right), k\right)))))) \land (\forall (k: \operatorname{Fin}\left(4\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{firstCount}\left(k\right) = ![4, 0, 4, 2]\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; R. J. Mathar; OEIS Foundation Inc. (2013). *OEIS A233125: six-colour complementary-pair exclusion on a four-column square strip*. URL: <https://oeis.org/A233125>.

*Commentary.*

Exact scanner fibres reduce the transition counts to 3^4 label rows. The single-row certificate supplies the numerical premises of the all-height induction.

**Theorem 1.15 (The power-series identity).**

$$(((1) - ((16) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))))) \cdot ((((1) - ((144) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))))) + ((3840) \cdot (((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right)))^{2}))) - ((24576) \cdot (((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right)))^{3})))) \cdot (\operatorname{PowerSeries}.\operatorname{mk}\left(((n: \operatorname{Nat}) \mapsto ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{a}\left(n\right): \operatorname{Int})))\right)) = ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) \cdot ((((10) - ((704) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))))) + ((14336) \cdot (((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right)))^{2}))) - ((81920) \cdot (((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right)))^{3})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233125` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233125","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; R. J. Mathar; OEIS Foundation Inc. (2013). *OEIS A233125: six-colour complementary-pair exclusion on a four-column square strip*. URL: <https://oeis.org/A233125>.

*Commentary.*

The complementary-pair labels are the fibres {0,5}, {1,4}, {2,3} of BooleanRankThreeK4.beta. The original scanner and its exact weighted pushforward are reused. Before colour 2 occurs there is one boundary class. Afterwards the proper label rows split into alternating rows, the two reversal-related types, and rows with equal endpoints. In this order the transfer rows are (16,16,32,8), (0,48,64,16), (0,32,64,16), (0,16,32,32), and the first-row distribution is (4,0,4,2). Induction proves that these classes suffice at every height. The first sector has factor 1-16X; the remaining three classes have factor 1-144X+3840X²-24576X³. This proves the displayed identity for the literal count, with no empirical recurrence assumed.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.Row`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.Valid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.bonds`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.boundaryClass`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.classCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.decidableRowLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.firstCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.label_sum`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.labels`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.rowLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.transfer`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge](HardinA233255LiteralBridge.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
