# Horizontal and vertical complementary-pair exclusion

## Abstract

Barker's generating function for normalized six-colour square strips.

OEIS A233124, revision 7, counts arrays on n rows and three columns. Horizontal and vertical neighbours are unequal and do not sum to five; diagonals are unconstrained. The first colour is zero. In row-major order every 2, 3 or 4 has an earlier 1, and every 3 has an earlier 2. The coefficient a 0 is zero. All names in the formulas are their full Lean names. Fin.val is the explicit embedding into Nat; numeric Fin indices have their displayed finite type. Nat.div is natural quotient division and Nat.mod is the nonnegative remainder, with the Lean zero-divisor conventions n / 0 = 0 and n % 0 = n; neither operation is used in these definitions.

**Definition 1.1 (Vertical neighbours).**

$$\forall c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{Row}, (\forall d: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{Row}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{bonds}\left(c, d\right) = \forall j: \operatorname{Fin}\left(3\right), ((c\left(j\right) \neq d\left(j\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left(j\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(d\left(j\right)\right)) \neq 5))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.bonds` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233124: six-colour complementary-pair exclusion on a square strip*. URL: <https://oeis.org/A233124>.

*Commentary.*

The three bonds connect equal column indices in consecutive rows.

**Definition 1.2 (The literal array predicate).**

$$\forall n: \operatorname{Nat}, (\forall A: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(3\right))) \to \operatorname{Fin}\left(6\right), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{Legal}\left(A\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthLegal}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{rowLegal}, \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{bonds}, A\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{Legal}\left(A\right) = ((\exists i: \operatorname{Fin}\left(n\right), ((\operatorname{Fin}.\operatorname{val}\left(i\right) = 0) \land (A\left((i, (0: \operatorname{Fin}\left(3\right)))\right) = (0: \operatorname{Fin}\left(6\right))))) \land ((\forall i: \operatorname{Fin}\left(n\right), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{rowLegal}\left(\lambda j: \operatorname{Fin}\left(3\right) \mapsto (A\left((i, j)\right))\right))) \land ((\forall i: \operatorname{Fin}\left(n\right), (\forall h: (\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1) < n, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{bonds}\left(\lambda j: \operatorname{Fin}\left(3\right) \mapsto (A\left((i, j)\right)), \lambda j: \operatorname{Fin}\left(3\right) \mapsto (A\left(((\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1), h\right): \operatorname{Fin}\left(n\right)), j)\right))\right)))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthNormal}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), \lambda i: \operatorname{Fin}\left(n\right) \mapsto (\lambda j: \operatorname{Fin}\left(3\right) \mapsto (A\left((i, j)\right)))\right))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233124: six-colour complementary-pair exclusion on a square strip*. URL: <https://oeis.org/A233124>.

*Commentary.*

The owner predicate widthLegal is specialized to width three, rowLegal and the vertical predicate bonds. Its widthNormal imposes the stated row-major normalization. The filtered count keeps every array in scope.

**Definition 1.3 (The literal filtered count).**

$$\forall n: \operatorname{Nat}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(\lambda A: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(3\right))) \to \operatorname{Fin}\left(6\right) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{Legal}\left(A\right)), \operatorname{Finset}.\operatorname{univ}\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233124: six-colour complementary-pair exclusion on a square strip*. URL: <https://oeis.org/A233124>.

*Commentary.*

The filter ranges over every function on Fin n times Fin 3. The first-cell existential is false when n is zero.

**Definition 1.4 (Vertical label compatibility).**

$$\forall p: (\operatorname{Fin}\left(3\right)) \to \operatorname{Fin}\left(3\right), (\forall c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{Row}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{compatible}\left(p, c\right) = \forall j: \operatorname{Fin}\left(3\right), (p\left(j\right) \neq \operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(j\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233124: six-colour complementary-pair exclusion on a square strip*. URL: <https://oeis.org/A233124>.

*Commentary.*

Each new label differs from the preceding label in the same column.

**Definition 1.5 (Reachable boundaries).**

$$\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: (\operatorname{Fin}\left(3\right)) \to \operatorname{Fin}\left(3\right), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{Valid}\left(s, p\right) = ((\operatorname{Prod}.\operatorname{fst}\left(s\right) = \operatorname{Bool}.\operatorname{true}) \land ((p\left((0: \operatorname{Fin}\left(3\right))\right) \neq p\left((1: \operatorname{Fin}\left(3\right))\right)) \land ((p\left((1: \operatorname{Fin}\left(3\right))\right) \neq p\left((2: \operatorname{Fin}\left(3\right))\right)) \land ((\operatorname{Prod}.\operatorname{snd}\left(s\right) = \operatorname{Bool}.\operatorname{false}) \implies (\forall j: \operatorname{Fin}\left(3\right), (p\left(j\right) \neq (2: \operatorname{Fin}\left(3\right))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233124: six-colour complementary-pair exclusion on a square strip*. URL: <https://oeis.org/A233124>.

*Commentary.*

Colour one has occurred, adjacent boundary labels differ, and before colour two occurs every label differs from two.

**Definition 1.6 (Deciding reachable boundaries).**

$$\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: (\operatorname{Fin}\left(3\right)) \to \operatorname{Fin}\left(3\right), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{instDecidableValid}\left(s, p\right): \operatorname{Decidable}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{Valid}\left(s, p\right))\right)) = \operatorname{inferInstanceAs}\left((\operatorname{Decidable}\left(((\operatorname{Prod}.\operatorname{fst}\left(s\right) = \operatorname{Bool}.\operatorname{true}) \land ((p\left((0: \operatorname{Fin}\left(3\right))\right) \neq p\left((1: \operatorname{Fin}\left(3\right))\right)) \land ((p\left((1: \operatorname{Fin}\left(3\right))\right) \neq p\left((2: \operatorname{Fin}\left(3\right))\right)) \land ((\operatorname{Prod}.\operatorname{snd}\left(s\right) = \operatorname{Bool}.\operatorname{false}) \implies (\forall j: \operatorname{Fin}\left(3\right), (p\left(j\right) \neq (2: \operatorname{Fin}\left(3\right))))))))\right))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.instDecidableValid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233124: six-colour complementary-pair exclusion on a square strip*. URL: <https://oeis.org/A233124>.

*Commentary.*

The defining expression infers decidability for the conjunction defining Valid.

**Definition 1.7 (The three boundary classes).**

$$\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: (\operatorname{Fin}\left(3\right)) \to \operatorname{Fin}\left(3\right), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{boundaryClass}\left(s, p\right) = (\operatorname{if} (\operatorname{Prod}.\operatorname{snd}\left(s\right)) \operatorname{then} (\operatorname{if} (p\left((0: \operatorname{Fin}\left(3\right))\right) = p\left((2: \operatorname{Fin}\left(3\right))\right)) \operatorname{then} (1: \operatorname{Fin}\left(3\right)) \operatorname{else} (2: \operatorname{Fin}\left(3\right))) \operatorname{else} (0: \operatorname{Fin}\left(3\right)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.boundaryClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233124: six-colour complementary-pair exclusion on a square strip*. URL: <https://oeis.org/A233124>.

*Commentary.*

Class zero has not seen colour two. Classes one and two have seen it; their endpoint labels are respectively equal and different.

**Definition 1.8 (The row transfer matrix).**

$$\forall i: \operatorname{Fin}\left(3\right), (\forall k: \operatorname{Fin}\left(3\right), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{transfer}\left(i, k\right) = ![![(8: \operatorname{Int}), (8: \operatorname{Int}), (8: \operatorname{Int})], ![(0: \operatorname{Int}), (24: \operatorname{Int}), (16: \operatorname{Int})], ![(0: \operatorname{Int}), (16: \operatorname{Int}), (16: \operatorname{Int})]]\left(i, k\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233124: six-colour complementary-pair exclusion on a square strip*. URL: <https://oeis.org/A233124>.

*Commentary.*

The matrix rows and columns have the boundaryClass order zero, one, two.

**Definition 1.9 (One-row transitions).**

$$\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: (\operatorname{Fin}\left(3\right)) \to \operatorname{Fin}\left(3\right), (\forall k: \operatorname{Fin}\left(3\right), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{classCount}\left(s, p, k\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{Row}} ((\operatorname{if} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{compatible}\left(p, c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{boundaryClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left(s, c\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{pairs}\left(c\right)\right) = k)))) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.classCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233124: six-colour complementary-pair exclusion on a square strip*. URL: <https://oeis.org/A233124>.

*Commentary.*

The shared scanner good and finish checks and updates normalization within the three cells of the new row.

**Definition 1.10 (The first-row distribution).**

$$\forall k: \operatorname{Fin}\left(3\right), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{firstCount}\left(k\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{Row}} ((\operatorname{if} ((c\left((0: \operatorname{Fin}\left(3\right))\right) = (0: \operatorname{Fin}\left(6\right))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{boundaryClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), c\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{pairs}\left(c\right)\right) = k)))) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.firstCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233124: six-colour complementary-pair exclusion on a square strip*. URL: <https://oeis.org/A233124>.

*Commentary.*

The initial scanner flags are false and the first colour is zero.

**Theorem 1.11 (The class counts).**

$$(\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: (\operatorname{Fin}\left(3\right)) \to \operatorname{Fin}\left(3\right), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{Valid}\left(s, p\right)) \implies (\forall k: \operatorname{Fin}\left(3\right), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{classCount}\left(s, p, k\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{transfer}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{boundaryClass}\left(s, p\right), k\right)))))) \land (\forall k: \operatorname{Fin}\left(3\right), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{firstCount}\left(k\right) = ![(2: \operatorname{Int}), (0: \operatorname{Int}), (1: \operatorname{Int})]\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233124: six-colour complementary-pair exclusion on a square strip*. URL: <https://oeis.org/A233124>.

*Commentary.*

For each valid boundary the three counts are the corresponding row of the transfer matrix. The first-row distribution is [2,0,1].

**Theorem 1.12 (Barker's generating-function identity).**

$$(((1) - ((8) \cdot (\operatorname{PowerSeries}.\operatorname{X}))) \cdot (((1) - ((40) \cdot (\operatorname{PowerSeries}.\operatorname{X}))) + ((128) \cdot ((\operatorname{PowerSeries}.\operatorname{X})^{2})))) \cdot (\operatorname{PowerSeries}.\operatorname{mk}\left(\lambda n: \operatorname{Nat} \mapsto ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{a}\left(n\right): \operatorname{Int}))\right)) = (\operatorname{PowerSeries}.\operatorname{X}) \cdot (((3) - ((64) \cdot (\operatorname{PowerSeries}.\operatorname{X}))) + ((192) \cdot ((\operatorname{PowerSeries}.\operatorname{X})^{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233124` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233124","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233124: six-colour complementary-pair exclusion on a square strip*. URL: <https://oeis.org/A233124>.

*Commentary.*

Let B(k), E(k), D(k) be the continuation counts for the three classes. All equal one at k=0. The matrix gives B(k+1)=8B(k)+8E(k)+8D(k), E(k+1)=24E(k)+16D(k), D(k+1)=16E(k)+16D(k). Decomposing an array into its first row and tail gives a(k+1)=2B(k)+D(k). Hence a(n+4)=48a(n+3)-448a(n+2)+1024a(n+1) for every natural n. The initial values are a(0)=0, a(1)=3, a(2)=80, a(3)=2688. Coefficient comparison in PowerSeries Int gives the displayed identity. This is an identity of formal series; it needs no analytic convergence assumption.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.Valid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.bonds`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.boundaryClass`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.classCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.firstCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.instDecidableValid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.transfer`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder](HardinA233176Ladder.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
