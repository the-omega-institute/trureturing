# A two-class transfer for complementary-pair exclusion

## Abstract

Barker's generating function for normalized six-colour two-column square strips.

OEIS A233123, revision 7, counts n by 2 arrays over Fin 6. Horizontal and vertical neighbours are unequal and do not sum to five. Diagonal neighbours are unconstrained. The upper-left colour is zero. In row-major order every 2, 3 or 4 has an earlier 1, and every 3 has an earlier 2. The coefficient at index zero is zero. All declaration names below retain their full Lean namespaces. Fin.val maps a finite index or colour to its natural value. Typed numerals specify their Fin domains. Nat.div is natural quotient division and Nat.mod is the nonnegative remainder; neither enters these definitions. HardinA233175PairStrip.Col is literally Fin 2 to Fin 6. All sums range over the displayed finite type.

**Definition 1.1 (The horizontal bond).**

$$\forall c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Col}, ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233123SquareStrip}.\operatorname{rowLegal}\left(c\right)) = ((c\left((0: \operatorname{Fin}\left(2\right))\right) \neq c\left((1: \operatorname{Fin}\left(2\right))\right)) \land (\operatorname{Fin}.\operatorname{val}\left(c\left((0: \operatorname{Fin}\left(2\right))\right)\right) + \operatorname{Fin}.\operatorname{val}\left(c\left((1: \operatorname{Fin}\left(2\right))\right)\right) \neq 5)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.rowLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233123: six-colour complementary-pair exclusion on a two-column square strip*. URL: <https://oeis.org/A233123>.

*Commentary.*

There is exactly one horizontal bond in a two-column row.

**Definition 1.2 (Deciding the horizontal bond).**

$$\forall c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Col}, (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233123SquareStrip}.\operatorname{instDecidableRowLegal}\left(c\right): \operatorname{Decidable}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233123SquareStrip}.\operatorname{rowLegal}\left(c\right))\right))) = (\operatorname{inferInstanceAs}\left((\operatorname{Decidable}\left(((c\left((0: \operatorname{Fin}\left(2\right))\right) \neq c\left((1: \operatorname{Fin}\left(2\right))\right)) \land (\operatorname{Fin}.\operatorname{val}\left(c\left((0: \operatorname{Fin}\left(2\right))\right)\right) + \operatorname{Fin}.\operatorname{val}\left(c\left((1: \operatorname{Fin}\left(2\right))\right)\right) \neq 5))\right))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.instDecidableRowLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233123: six-colour complementary-pair exclusion on a two-column square strip*. URL: <https://oeis.org/A233123>.

*Commentary.*

The defining expression is inferInstanceAs for the displayed conjunction.

**Definition 1.3 (The two vertical bonds).**

$$\forall c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Col}, (\forall d: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Col}, ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233123SquareStrip}.\operatorname{bonds}\left(c, d\right)) = (\forall j: \operatorname{Fin}\left(2\right), ((c\left(j\right) \neq d\left(j\right)) \land (\operatorname{Fin}.\operatorname{val}\left(c\left(j\right)\right) + \operatorname{Fin}.\operatorname{val}\left(d\left(j\right)\right) \neq 5)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.bonds` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233123: six-colour complementary-pair exclusion on a two-column square strip*. URL: <https://oeis.org/A233123>.

*Commentary.*

The same column index is used in both consecutive rows.

**Definition 1.4 (The literal filtered count).**

$$\forall n: \operatorname{Nat}, ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233123SquareStrip}.\operatorname{a}\left(n\right)) = (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(\lambda A: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right))) \to \operatorname{Fin}\left(6\right) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthLegal}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233123SquareStrip}.\operatorname{rowLegal}, \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233123SquareStrip}.\operatorname{bonds}, A\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right))) \to \operatorname{Fin}\left(6\right)\right))\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233123: six-colour complementary-pair exclusion on a two-column square strip*. URL: <https://oeis.org/A233123>.

*Commentary.*

Every function from Fin n times Fin 2 to Fin 6 occurs in Finset.univ. Filtering by the owner widthLegal predicate, specialized to rowLegal and bonds, and taking its cardinality is the sequence definition. The shared widthNormal definition says that, at cell (i,j), each required predecessor is at (r,t) with r<i or r=i and t<j; the initial seen flags are both false. Thus a 0 = 0 by the first-cell condition.

**Definition 1.5 (Boundary compatibility).**

$$\forall p: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right)), (\forall c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Col}, ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233123SquareStrip}.\operatorname{compatible}\left(p, c\right)) = ((\operatorname{Prod}.\operatorname{fst}\left(p\right) \neq \operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left((0: \operatorname{Fin}\left(2\right))\right)\right)) \land (\operatorname{Prod}.\operatorname{snd}\left(p\right) \neq \operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left((1: \operatorname{Fin}\left(2\right))\right)\right)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233123: six-colour complementary-pair exclusion on a two-column square strip*. URL: <https://oeis.org/A233123>.

*Commentary.*

BooleanRankThreeK4.beta has fibres {0,5}, {1,4}, {2,3}. Its value for each preceding colour must differ from the next colour's value in that column. HardinA233175PairStrip.pairs c is literally (beta (c 0), beta (c 1)).

**Definition 1.6 (One-row class counts).**

$$\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right)), (\forall b: \operatorname{Bool}, ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233123SquareStrip}.\operatorname{classCount}\left(s, p, b\right)) = (\sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Col}} ((\operatorname{if} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233123SquareStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233123SquareStrip}.\operatorname{compatible}\left(p, c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right)) \land ((\operatorname{Prod}.\operatorname{snd}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left(s, c\right)\right)) = (b))))) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int})))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.classCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233123: six-colour complementary-pair exclusion on a two-column square strip*. URL: <https://oeis.org/A233123>.

*Commentary.*

HardinA233251TriangleStrip.Valid s p says that 1 has been seen, the boundary labels differ, and before 2 is seen neither label is 2. Seen is Bool times Bool, tracking occurrences of colours 1 and 2. The shared good predicate checks the row in column order using allowed and advance. The shared finish function returns its final seen flags.

**Definition 1.7 (First-row class counts).**

$$\forall b: \operatorname{Bool}, ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233123SquareStrip}.\operatorname{firstCount}\left(b\right)) = (\sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Col}} ((\operatorname{if} (((c\left((0: \operatorname{Fin}\left(2\right))\right)) = ((0: \operatorname{Fin}\left(6\right)))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233123SquareStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), c\right)) \land ((\operatorname{Prod}.\operatorname{snd}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), c\right)\right)) = (b))))) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int})))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.firstCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233123: six-colour complementary-pair exclusion on a two-column square strip*. URL: <https://oeis.org/A233123>.

*Commentary.*

The first colour is zero and both initial seen flags are false.

**Theorem 1.8 (The finite transfer certificate).**

$$(\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{Valid}\left(s, p\right)) \implies (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233123SquareStrip}.\operatorname{classCount}\left(s, p, \operatorname{Bool}.\operatorname{true}\right)) = ((\operatorname{if} (\operatorname{Prod}.\operatorname{snd}\left(s\right)) \operatorname{then} (12: \operatorname{Int}) \operatorname{else} (4: \operatorname{Int})))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233123SquareStrip}.\operatorname{classCount}\left(s, p, \operatorname{Bool}.\operatorname{false}\right)) = ((\operatorname{if} (\operatorname{Prod}.\operatorname{snd}\left(s\right)) \operatorname{then} (0: \operatorname{Int}) \operatorname{else} (4: \operatorname{Int})))))))) \land (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233123SquareStrip}.\operatorname{firstCount}\left(\operatorname{Bool}.\operatorname{true}\right)) = ((0: \operatorname{Int}))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233123SquareStrip}.\operatorname{firstCount}\left(\operatorname{Bool}.\operatorname{false}\right)) = ((1: \operatorname{Int}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233123: six-colour complementary-pair exclusion on a two-column square strip*. URL: <https://oeis.org/A233123>.

*Commentary.*

From a boundary with 2 unseen, four rows keep 2 unseen and four see it. From a boundary with 2 seen, twelve rows keep it seen and none forget it. The unique first row is (0,1); it leaves 2 unseen. These are counts of single rows, each drawn from the 36 functions Fin 2 to Fin 6.

**Theorem 1.9 (Barker's generating-function identity).**

$$((\left(1 - 4 \cdot \operatorname{PowerSeries}.\operatorname{X}\right) \cdot \left(1 - 12 \cdot \operatorname{PowerSeries}.\operatorname{X}\right) \cdot \operatorname{PowerSeries}.\operatorname{mk}\left(\lambda n: \operatorname{Nat} \mapsto ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233123SquareStrip}.\operatorname{a}\left(n\right): \operatorname{Int}))\right): \operatorname{PowerSeries}\left(\operatorname{Int}\right))) = (\operatorname{PowerSeries}.\operatorname{X} \cdot \left(1 - 8 \cdot \operatorname{PowerSeries}.\operatorname{X}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233123` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233123","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233123: six-colour complementary-pair exclusion on a two-column square strip*. URL: <https://oeis.org/A233123>.

*Commentary.*

Let U(k) count continuations after 2 has been seen, and V(k) those before 2 has been seen, under the invariant Valid. The finite certificate gives U(0)=V(0)=1, U(k+1)=12U(k), and V(k+1)=4V(k)+4U(k). The width-generic width_counting_bridge of HardinA233251TriangleStrip applies with the vertical relation bonds and boundary map HardinA233175PairStrip.pairs. It identifies the literal count a(k+1) with V(k). Hence a(n+3)=16a(n+2)-48a(n+1), with a(1)=1 and a(2)=8. Comparing every coefficient gives the identity in PowerSeries Int, including index zero. The first values are 1, 8, 80, 896, 10496 and 124928. The statement concerns formal power series and does not assume analytic convergence.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.bonds`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.classCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.firstCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.instDecidableRowLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.rowLegal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
