# Five-column complementary-pair exclusion

## Abstract

Barker's generating function for the literal normalized five-column strip.

The coefficient at zero is zero. Only horizontal and antidiagonal bonds are constrained. Vertical and main-diagonal neighbours are unconstrained. The first cell is zero. In row-major order, each 2, 3 or 4 has an earlier 1, and each 3 an earlier 2. Fin.val is the coercion to natural numbers; Fin.mk constructs a bounded index with the displayed proof. Nat.div is natural quotient division and Nat.mod its nonnegative remainder. Neither operation occurs in these definitions.

**Definition 1.1 (A row).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row} = (\operatorname{Fin}\left(5\right)) \to (\operatorname{Fin}\left(6\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233253: six-colour complementary-pair exclusion on a five-column strip*. URL: <https://oeis.org/A233253>.

*Commentary.*

Rows are functions on five ordered column indices.

**Definition 1.2 (A boundary).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Boundary} = (\operatorname{Fin}\left(4\right)) \to (\operatorname{Fin}\left(3\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.Boundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233253: six-colour complementary-pair exclusion on a five-column strip*. URL: <https://oeis.org/A233253>.

*Commentary.*

The four labels record complementary pairs at column indices 1 through 4.

**Definition 1.3 (Horizontal exclusions).**

$$\forall c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rowLegal}\left(c\right) = \forall j: \operatorname{Fin}\left(4\right), ((c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \neq c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)) \land (\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right) + \operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right) \neq 5)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.rowLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233253: six-colour complementary-pair exclusion on a five-column strip*. URL: <https://oeis.org/A233253>.

*Commentary.*

The conjunction excludes equality and a natural-number sum of five.

**Definition 1.4 (Deciding horizontal exclusions).**

$$\forall c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}, ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{instDecidableRowLegal}\left(c\right): \operatorname{Decidable}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rowLegal}\left(c\right))\right)) = \operatorname{inferInstanceAs}\left((\operatorname{Decidable}\left((\forall j: \operatorname{Fin}\left(4\right), ((c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \neq c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)) \land (\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right) + \operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right) \neq 5)))\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.instDecidableRowLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233253: six-colour complementary-pair exclusion on a five-column strip*. URL: <https://oeis.org/A233253>.

*Commentary.*

The horizontal predicate has a finite decision procedure.

**Definition 1.5 (Boundary labels).**

$$\forall c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{pairs}\left(c\right) = \lambda j: \operatorname{Fin}\left(4\right) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.pairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233253: six-colour complementary-pair exclusion on a five-column strip*. URL: <https://oeis.org/A233253>.

*Commentary.*

The lambda retains the ordered four-column boundary.

**Definition 1.6 (Antidiagonal exclusions).**

$$\forall p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Boundary}, (\forall c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{compatible}\left(p, c\right) = \forall j: \operatorname{Fin}\left(4\right), (p\left(j\right) \neq \operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233253: six-colour complementary-pair exclusion on a five-column strip*. URL: <https://oeis.org/A233253>.

*Commentary.*

Each old boundary label excludes the corresponding next-row label.

**Definition 1.7 (The literal finite count).**

$$\forall n: \operatorname{Nat}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(\lambda A: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(5\right))) \to (\operatorname{Fin}\left(6\right)) \mapsto ((\exists i: \operatorname{Fin}\left(n\right), ((\operatorname{Fin}.\operatorname{val}\left(i\right) = 0) \land (A\left((i, (0: \operatorname{Fin}\left(5\right)))\right) = (0: \operatorname{Fin}\left(6\right))))) \land ((\forall i: \operatorname{Fin}\left(n\right), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rowLegal}\left(\lambda j: \operatorname{Fin}\left(5\right) \mapsto (A\left((i, j)\right))\right))) \land ((\forall i: \operatorname{Fin}\left(n\right), (\forall h: \operatorname{Fin}.\operatorname{val}\left(i\right) + 1 < n, (\forall j: \operatorname{Fin}\left(4\right), ((A\left((i, \operatorname{Fin}.\operatorname{succ}\left(j\right))\right) \neq A\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + 1, h\right), \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right)) \land (\operatorname{Fin}.\operatorname{val}\left(A\left((i, \operatorname{Fin}.\operatorname{succ}\left(j\right))\right)\right) + \operatorname{Fin}.\operatorname{val}\left(A\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + 1, h\right), \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right)\right) \neq 5))))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthNormal}\left((false, false), \lambda i: \operatorname{Fin}\left(n\right) \mapsto (\lambda j: \operatorname{Fin}\left(5\right) \mapsto (A\left((i, j)\right)))\right))))), \operatorname{Finset}.\operatorname{univ}\left(\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233253: six-colour complementary-pair exclusion on a five-column strip*. URL: <https://oeis.org/A233253>.

*Commentary.*

The filter ranges over every array function. The existential first-cell condition is false when n is zero. The final predicate is the original row-major scanner predicate at both false flags.

**Definition 1.8 (Reachable boundaries).**

$$\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Boundary}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Valid}\left(s, p\right) = ((\operatorname{Prod}.\operatorname{fst}\left(s\right) = true) \land ((\forall j: \operatorname{Fin}\left(3\right), (p\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \neq p\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right))) \land ((\operatorname{Prod}.\operatorname{snd}\left(s\right) = false) \implies (\forall j: \operatorname{Fin}\left(4\right), (p\left(j\right) \neq (2: \operatorname{Fin}\left(3\right)))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233253: six-colour complementary-pair exclusion on a five-column strip*. URL: <https://oeis.org/A233253>.

*Commentary.*

The first flag is true. Adjacent boundary labels differ. If colour two has not occurred, none of the boundary labels is its pair label two.

**Definition 1.9 (A boundary statistic).**

$$\forall p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Boundary}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rank}\left(p\right) = (\operatorname{if} (p\left((0: \operatorname{Fin}\left(4\right))\right) = p\left((2: \operatorname{Fin}\left(4\right))\right)) \operatorname{then} (\operatorname{if} (p\left((1: \operatorname{Fin}\left(4\right))\right) = p\left((3: \operatorname{Fin}\left(4\right))\right)) \operatorname{then} (3: \operatorname{Int}) \operatorname{else} (2: \operatorname{Int})) \operatorname{else} (\operatorname{if} (p\left((1: \operatorname{Fin}\left(4\right))\right) = p\left((3: \operatorname{Fin}\left(4\right))\right)) \operatorname{then} (2: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.rank` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233253: six-colour complementary-pair exclusion on a five-column strip*. URL: <https://oeis.org/A233253>.

*Commentary.*

The shapes ABAB, ABAC, ABCA and ABCB have ranks 3, 2, 0 and 2.

**Definition 1.10 (Unweighted row counts).**

$$\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Boundary}, (\forall b: \operatorname{Bool}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{classCount}\left(s, p, b\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}} ((\operatorname{if} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{compatible}\left(p, c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right)) \land (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left(s, c\right)\right) = b)))) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.classCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233253: six-colour complementary-pair exclusion on a five-column strip*. URL: <https://oeis.org/A233253>.

*Commentary.*

The final second flag distinguishes the two seen-colour sectors.

**Definition 1.11 (Weighted row counts).**

$$\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Boundary}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rankCount}\left(s, p\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}} ((\operatorname{if} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{compatible}\left(p, c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right)) \land (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left(s, c\right)\right) = true)))) \operatorname{then} \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rank}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{pairs}\left(c\right)\right) \operatorname{else} (0: \operatorname{Int})))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.rankCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233253: six-colour complementary-pair exclusion on a five-column strip*. URL: <https://oeis.org/A233253>.

*Commentary.*

The weight is the rank of the new boundary in the fully seen sector.

**Definition 1.12 (First-row counts).**

$$\forall b: \operatorname{Bool}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{firstCount}\left(b\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}} ((\operatorname{if} ((c\left((0: \operatorname{Fin}\left(5\right))\right) = (0: \operatorname{Fin}\left(6\right))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left((false, false), c\right)) \land (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left((false, false), c\right)\right) = b)))) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.firstCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233253: six-colour complementary-pair exclusion on a five-column strip*. URL: <https://oeis.org/A233253>.

*Commentary.*

The scanner starts with both flags false and the first colour fixed to zero.

**Definition 1.13 (First-row weighted count).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{firstRank} = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}} ((\operatorname{if} ((c\left((0: \operatorname{Fin}\left(5\right))\right) = (0: \operatorname{Fin}\left(6\right))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left((false, false), c\right)) \land (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left((false, false), c\right)\right) = true)))) \operatorname{then} \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rank}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{pairs}\left(c\right)\right) \operatorname{else} (0: \operatorname{Int})))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.firstRank` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233253: six-colour complementary-pair exclusion on a five-column strip*. URL: <https://oeis.org/A233253>.

*Commentary.*

Only fully seen first rows contribute their boundary rank.

**Theorem 1.14 (One-row transfer counts).**

$$(\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Boundary}, ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Valid}\left(s, p\right)) \implies ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{classCount}\left(s, p, true\right) = (\operatorname{if} (\operatorname{Prod}.\operatorname{snd}\left(s\right)) \operatorname{then} (320: \operatorname{Int}) + (64: \operatorname{Int}) \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rank}\left(p\right) \operatorname{else} (240: \operatorname{Int}))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{classCount}\left(s, p, false\right) = (\operatorname{if} (\operatorname{Prod}.\operatorname{snd}\left(s\right)) \operatorname{then} (0: \operatorname{Int}) \operatorname{else} (32: \operatorname{Int}))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rankCount}\left(s, p\right) = (\operatorname{if} (\operatorname{Prod}.\operatorname{snd}\left(s\right)) \operatorname{then} (512: \operatorname{Int}) + (160: \operatorname{Int}) \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rank}\left(p\right) \operatorname{else} (448: \operatorname{Int})))))))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{firstCount}\left(true\right) = (28: \operatorname{Int})) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{firstCount}\left(false\right) = (8: \operatorname{Int})) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{firstRank} = (44: \operatorname{Int}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233253: six-colour complementary-pair exclusion on a five-column strip*. URL: <https://oeis.org/A233253>.

*Commentary.*

At a fully seen boundary of rank r, the row count is 320+64r and the rank sum is 512+160r. From the other sector, 32 rows stay there, 240 enter the fully seen sector and their rank sum is 448. The initial counts are eight and 28, with fully seen rank sum 44.

**Theorem 1.15 (Barker's identity).**

$$(\left(1 - 32 \cdot \operatorname{PowerSeries}.\operatorname{X}\right) \cdot \left(1 - 480 \cdot \operatorname{PowerSeries}.\operatorname{X} + 18432 \cdot (\operatorname{PowerSeries}.\operatorname{X})^{2}\right) \cdot \operatorname{PowerSeries}.\operatorname{mk}\left(\lambda n: \operatorname{Nat} \mapsto ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{a}\left(n\right): \operatorname{Int}))\right): \operatorname{PowerSeries}\left(\operatorname{Int}\right)) = 4 \cdot \operatorname{PowerSeries}.\operatorname{X} \cdot \left(9 - 1120 \cdot \operatorname{PowerSeries}.\operatorname{X} + 30720 \cdot (\operatorname{PowerSeries}.\operatorname{X})^{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233253` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233253","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233253: six-colour complementary-pair exclusion on a five-column strip*. URL: <https://oeis.org/A233253>.

*Commentary.*

The continuations from length zero have form F without colour two, and U+rZ in the fully seen sector. At length zero, F=U=1 and Z=0. The one-row identities give F'=32F+240U+448Z, U'=320U+512Z and Z'=64U+160Z. The shared strip counting theorem gives a(n+1)=8F(n)+28U(n)+44Z(n). Consequently a(n+4)=512a(n+3)-33792a(n+2)+589824a(n+1), and a(1), a(2), a(3) are 36, 13952, 6049792. Comparing coefficients in integer power series proves the displayed identity.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.Boundary`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.Row`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.Valid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.classCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.firstCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.firstRank`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.instDecidableRowLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.pairs`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.rank`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.rankCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.rowLegal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
