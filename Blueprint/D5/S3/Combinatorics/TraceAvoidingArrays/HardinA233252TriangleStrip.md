# Six-colour horizontal and antidiagonal exclusion

## Abstract

Barker's recurrence, generating function, and closed form for the literal normalized four-column strip.

OEIS A233252 revision 8 defines n by 4 arrays with horizontal and antidiagonal exclusions. The first cell is zero. In row-major order, each 2, 3 or 4 has an earlier 1, and each 3 an earlier 2. The coefficient at index zero is zero. The three complementary-pair labels are the fibres of the existing BooleanRankThreeK4.beta.

Rows and horizontal exclusions use HardinA233125SquareStrip.Row and HardinA233125SquareStrip.rowLegal. A row contains four colours; consecutive colours are unequal and are not complementary.

Reachable boundary states use HardinA233124SquareStrip.Valid: the first scanner flag is true, adjacent boundary labels are distinct, and label two is absent before colour two is seen. HardinA233124SquareStrip.boundaryClass assigns class zero before colour two appears; after it appears, classes one and two distinguish equal and unequal endpoints.

**Definition 1.1 (Boundary label type).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{Boundary} = \left(\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(3\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.Boundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

The antidiagonal boundary carries three complementary-pair labels.

**Definition 1.2 (The literal finite count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(((A: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)) \to \operatorname{Fin}\left(6\right)) \mapsto ((\exists (i: \operatorname{Fin}\left(n\right)), ((\operatorname{Fin}.\operatorname{val}\left(i\right) = 0) \land (A\left((i, (0: \operatorname{Fin}\left(4\right)))\right) = (0: \operatorname{Fin}\left(6\right))))) \land ((\forall (i: \operatorname{Fin}\left(n\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{rowLegal}\left(((j: \operatorname{Fin}\left(4\right)) \mapsto (A\left((i, j)\right)))\right))) \land ((\forall (i: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1) < n), (\forall (j: \operatorname{Fin}\left(3\right)), ((A\left((i, \operatorname{Fin}.\operatorname{succ}\left(j\right))\right) \ne A\left((\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1), h\right), \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(A\left((i, \operatorname{Fin}.\operatorname{succ}\left(j\right))\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(A\left((\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1), h\right), \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right)\right)) \ne 5))))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthNormal}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), ((i: \operatorname{Fin}\left(n\right)) \mapsto (((j: \operatorname{Fin}\left(4\right)) \mapsto (A\left((i, j)\right)))))\right)))))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)) \to \operatorname{Fin}\left(6\right)\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

The owner widthLegal predicate combines the first-cell, horizontal, antidiagonal, and row-major scanner clauses. The empty-height filter is empty.

**Definition 1.3 (Boundary pair labels).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{pairs}\left(c\right) = ((j: \operatorname{Fin}\left(3\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.pairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

The boundary records the labels at columns one, two, and three.

**Definition 1.4 (Antidiagonal label compatibility).**

$$\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{Boundary}), (\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{compatible}\left(p, c\right) = \forall (j: \operatorname{Fin}\left(3\right)), (p\left(j\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

Each preceding boundary label excludes the corresponding next-row colour label.

**Definition 1.5 (Class transition matrix).**

$$\forall (i: \operatorname{Fin}\left(3\right)), (\forall (k: \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{transfer}\left(i, k\right) = ![![16, 32, 40], ![0, 80, 80], ![0, 64, 64]]\left(i, k\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

Rows are source classes and columns are destination classes.

**Definition 1.6 (One-row class counts).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{Boundary}), (\forall (k: \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{classCount}\left(s, p, k\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{Row}} (((\operatorname{if} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{compatible}\left(p, c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{boundaryClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left(s, c\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{pairs}\left(c\right)\right) = k)))) \operatorname{then} (1) \operatorname{else} (0)): \operatorname{Int})))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.classCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

The integer sum counts legal rows by their destination boundary class.

**Definition 1.7 (First-row class counts).**

$$\forall (k: \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{firstCount}\left(k\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{Row}} (((\operatorname{if} ((c\left((0: \operatorname{Fin}\left(4\right))\right) = (0: \operatorname{Fin}\left(6\right))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233125SquareStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{boundaryClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), c\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{pairs}\left(c\right)\right) = k)))) \operatorname{then} (1) \operatorname{else} (0)): \operatorname{Int})))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.firstCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

The first cell is fixed to zero and both scanner flags start false.

**Theorem 1.8 (Finite certificate).**

$$(\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{Boundary}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{Valid}\left(s, p\right)) \implies (\forall (k: \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{classCount}\left(s, p, k\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{transfer}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233124SquareStrip}.\operatorname{boundaryClass}\left(s, p\right), k\right)))))) \land (\forall (k: \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{firstCount}\left(k\right) = ![4, 2, 4]\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

The exact scanner-fibre calculation gives the displayed transition matrix and first-row vector. HardinA233125SquareStrip.label_sum reindexes the four-label sum as four successive sums over Fin 3.

**Theorem 1.9 (Barker's three identities).**

$$(\forall (n: \operatorname{Nat}), ((1 \le n) \implies ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{a}\left((n) + (2)\right): \operatorname{Int}) = ((160) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{a}\left((n) + (1)\right): \operatorname{Int}))) - ((2304) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{a}\left(n\right): \operatorname{Int})))))) \land (((((1) - ((16) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))))) \cdot ((1) - ((144) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right)))))) \cdot (\operatorname{PowerSeries}.\operatorname{mk}\left(((n: \operatorname{Nat}) \mapsto ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{a}\left(n\right): \operatorname{Int})))\right)) = ((2) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right)))) \cdot ((5) - ((208) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right)))))) \land (\forall (n: \operatorname{Nat}), ((9) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233252TriangleStrip}.\operatorname{a}\left((n) + (1)\right): \operatorname{Int})) = (((2: \operatorname{Int}))^{(((4) \cdot (n)) + (1))}) \cdot (((4) \cdot (((9: \operatorname{Int}))^{((n) + (1))})) + (9)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233252` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233252","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233252: six-colour complementary-pair exclusion on a four-column strip*. URL: <https://oeis.org/A233252>.

*Commentary.*

The finite certificate and the width-generic counting bridge reduce every height to the three-state transfer. Its spectrum has factors 1-16X and 1-144X, yielding the recurrence and exact integer power-series identity. The same transfer induction gives Barker's closed form.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.Boundary`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.classCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.firstCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.pairs`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.transfer`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip](HardinA233124SquareStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip](HardinA233125SquareStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge](HardinA233255LiteralBridge.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
