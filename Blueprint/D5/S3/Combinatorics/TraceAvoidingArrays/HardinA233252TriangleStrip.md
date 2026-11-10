# Six-colour horizontal and antidiagonal exclusion

## Abstract

Barker's recurrence, generating function, and closed form for the literal normalized four-column strip.

OEIS A233252 revision 8 defines n by 4 arrays with horizontal and antidiagonal exclusions. The first cell is zero. In row-major order, each 2, 3 or 4 has an earlier 1, and each 3 an earlier 2. The coefficient at index zero is zero. The three complementary-pair labels are the fibres of the existing BooleanRankThreeK4.beta.

**Definition 1.1 (Rows).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{Row} = \left(\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(6\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

A row contains four colours.

**Definition 1.2 (Horizontal exclusions).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{rowLegal}\left(c\right) = \forall (j: \operatorname{Fin}\left(3\right)), ((c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \ne c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right)) \ne 5)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.rowLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

Consecutive colours in a row are unequal and are not complementary.

**Definition 1.3 (Antidiagonal exclusions).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{Row}), (\forall (d: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{bonds}\left(c, d\right) = \forall (j: \operatorname{Fin}\left(3\right)), ((c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right) \ne d\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(d\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right)) \ne 5))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.bonds` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

The upper-right cell of one row is bonded to the lower-left cell of the next.

**Definition 1.4 (The literal finite count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(((A: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)) \to \operatorname{Fin}\left(6\right)) \mapsto ((\exists (i: \operatorname{Fin}\left(n\right)), ((\operatorname{Fin}.\operatorname{val}\left(i\right) = 0) \land (A\left((i, (0: \operatorname{Fin}\left(4\right)))\right) = (0: \operatorname{Fin}\left(6\right))))) \land ((\forall (i: \operatorname{Fin}\left(n\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{rowLegal}\left(((j: \operatorname{Fin}\left(4\right)) \mapsto (A\left((i, j)\right)))\right))) \land ((\forall (i: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1) < n), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{bonds}\left(((j: \operatorname{Fin}\left(4\right)) \mapsto (A\left((i, j)\right))), ((j: \operatorname{Fin}\left(4\right)) \mapsto (A\left((\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1), h\right), j)\right)))\right)))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthNormal}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), ((i: \operatorname{Fin}\left(n\right)) \mapsto (((j: \operatorname{Fin}\left(4\right)) \mapsto (A\left((i, j)\right)))))\right)))))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)) \to \operatorname{Fin}\left(6\right)\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

The owner widthLegal predicate combines the first-cell, horizontal, antidiagonal, and row-major scanner clauses. The empty-height filter is empty.

**Definition 1.5 (Boundary pair labels).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{pairs}\left(c\right) = ((j: \operatorname{Fin}\left(3\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.pairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

The boundary records the labels at columns one, two, and three.

**Definition 1.6 (Antidiagonal label compatibility).**

$$\forall (p: \operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(3\right)), (\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{compatible}\left(p, c\right) = \forall (j: \operatorname{Fin}\left(3\right)), (p\left(j\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

Each preceding boundary label excludes the corresponding next-row colour label.

**Definition 1.7 (Reachable boundary states).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{Valid}\left(s, p\right) = \left((\operatorname{Prod}.\operatorname{fst}\left(s\right) = \operatorname{Bool}.\operatorname{true}) \land ((\forall (j: \operatorname{Fin}\left(2\right)), (p\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \ne p\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right))) \land ((\operatorname{Prod}.\operatorname{snd}\left(s\right) = \operatorname{Bool}.\operatorname{false}) \implies (\forall (j: \operatorname{Fin}\left(3\right)), (p\left(j\right) \ne (2: \operatorname{Fin}\left(3\right))))))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

The first scanner flag has been seen; boundary labels are adjacent-distinct; before colour two is seen, its pair label is absent.

**Definition 1.8 (Three boundary classes).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{boundaryClass}\left(s, p\right) = (\operatorname{if} (\operatorname{Prod}.\operatorname{snd}\left(s\right)) \operatorname{then} ((1: \operatorname{Fin}\left(3\right))) \operatorname{else} ((\operatorname{if} (p\left((0: \operatorname{Fin}\left(3\right))\right) = p\left((2: \operatorname{Fin}\left(3\right))\right)) \operatorname{then} ((1: \operatorname{Fin}\left(3\right))) \operatorname{else} ((2: \operatorname{Fin}\left(3\right))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.boundaryClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

Class zero is the unseen-colour-two sector. Classes one and two distinguish equal and unequal endpoints after colour two has appeared.

**Definition 1.9 (Class transition matrix).**

$$\forall (i: \operatorname{Fin}\left(3\right)), (\forall (k: \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{transfer}\left(i, k\right) = ![![16, 32, 40], ![0, 80, 80], ![0, 64, 64]]\left(i, k\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

Rows are source classes and columns are destination classes.

**Definition 1.10 (One-row class counts).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(3\right)), (\forall (k: \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{classCount}\left(s, p, k\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{Row}} (((\operatorname{if} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{compatible}\left(p, c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{boundaryClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left(s, c\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{pairs}\left(c\right)\right) = k)))) \operatorname{then} (1) \operatorname{else} (0)): \operatorname{Int})))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.classCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

The integer sum counts legal rows by their destination boundary class.

**Definition 1.11 (First-row class counts).**

$$\forall (k: \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{firstCount}\left(k\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{Row}} (((\operatorname{if} ((c\left((0: \operatorname{Fin}\left(4\right))\right) = (0: \operatorname{Fin}\left(6\right))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{boundaryClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), c\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{pairs}\left(c\right)\right) = k)))) \operatorname{then} (1) \operatorname{else} (0)): \operatorname{Int})))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.firstCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

The first cell is fixed to zero and both scanner flags start false.

**Theorem 1.12 (Finite certificate).**

$$(\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(3\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{Valid}\left(s, p\right)) \implies (\forall (k: \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{classCount}\left(s, p, k\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{transfer}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{boundaryClass}\left(s, p\right), k\right)))))) \land (\forall (k: \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{firstCount}\left(k\right) = ![4, 2, 4]\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

The exact scanner-fibre calculation gives the displayed transition matrix and first-row vector.

**Theorem 1.13 (Barker's three identities).**

$$(\forall (n: \operatorname{Nat}), ((1 \le n) \implies ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{a}\left((n) + (2)\right): \operatorname{Int}) = ((160) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{a}\left((n) + (1)\right): \operatorname{Int}))) - ((2304) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{a}\left(n\right): \operatorname{Int})))))) \land (((((1) - ((16) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))))) \cdot ((1) - ((144) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right)))))) \cdot (\operatorname{PowerSeries}.\operatorname{mk}\left(((n: \operatorname{Nat}) \mapsto ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{a}\left(n\right): \operatorname{Int})))\right)) = ((2) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right)))) \cdot ((5) - ((208) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right)))))) \land (\forall (n: \operatorname{Nat}), ((9) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{a}\left((n) + (1)\right): \operatorname{Int})) = (((2: \operatorname{Int}))^{(((4) \cdot (n)) + (1))}) \cdot (((4) \cdot (((9: \operatorname{Int}))^{((n) + (1))})) + (9)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

The finite certificate and the width-generic counting bridge reduce every height to the three-state transfer. Its spectrum has factors 1-16X and 1-144X, yielding the recurrence and exact integer power-series identity. The same transfer induction gives Barker's closed form.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.Row`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.Valid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.bonds`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.boundaryClass`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.classCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.firstCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.pairs`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.rowLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.transfer`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge](HardinA233255LiteralBridge.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
