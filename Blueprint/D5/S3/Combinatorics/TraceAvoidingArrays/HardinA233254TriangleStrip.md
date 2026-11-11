# Six-column complementary-pair exclusion

## Abstract

Barker's generating function for the literal normalized six-column strip.

The coefficient at zero is zero. Only horizontal and antidiagonal bonds are constrained. Vertical and main-diagonal neighbours are unconstrained. The first cell is zero. In row-major order, each 2, 3 or 4 has an earlier 1, and each 3 an earlier 2. Fin.val is the coercion to natural numbers; Fin.mk constructs a bounded index with the displayed proof. Nat.div is natural quotient division and Nat.mod its nonnegative remainder. Neither operation occurs in these definitions.

**Definition 1.1 (A row).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row} = (\operatorname{Fin}\left(6\right)) \to (\operatorname{Fin}\left(6\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233254: six-colour complementary-pair exclusion on a six-column strip*. URL: <https://oeis.org/A233254>.

*Commentary.*

Rows are functions on six ordered column indices.

**Definition 1.2 (A boundary).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Boundary} = (\operatorname{Fin}\left(5\right)) \to (\operatorname{Fin}\left(3\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.Boundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233254: six-colour complementary-pair exclusion on a six-column strip*. URL: <https://oeis.org/A233254>.

*Commentary.*

The five labels record complementary pairs at column indices 1 through 5.

**Definition 1.3 (Horizontal exclusions).**

$$\forall c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{rowLegal}\left(c\right) = \forall j: \operatorname{Fin}\left(5\right), ((c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \neq c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)) \land (\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right) + \operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right) \neq 5)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.rowLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233254: six-colour complementary-pair exclusion on a six-column strip*. URL: <https://oeis.org/A233254>.

*Commentary.*

The conjunction excludes equality and a natural-number sum of five.

**Definition 1.4 (Deciding horizontal exclusions).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{instDecidableRowLegal}: \operatorname{DecidablePred}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{rowLegal}\right)) = (\lambda c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row} \mapsto (\operatorname{inferInstanceAs}\left((\operatorname{Decidable}\left((\forall j: \operatorname{Fin}\left(5\right), ((c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \neq c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)) \land (\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right) + \operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right) \neq 5)))\right))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.instDecidableRowLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233254: six-colour complementary-pair exclusion on a six-column strip*. URL: <https://oeis.org/A233254>.

*Commentary.*

The defining lambda uses inferInstanceAs for the finite conjunction of the two horizontal exclusions.

**Definition 1.5 (Boundary labels).**

$$\forall c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{pairs}\left(c\right) = \lambda j: \operatorname{Fin}\left(5\right) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.pairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233254: six-colour complementary-pair exclusion on a six-column strip*. URL: <https://oeis.org/A233254>.

*Commentary.*

The lambda retains the ordered five-column boundary.

**Definition 1.6 (Antidiagonal exclusions).**

$$\forall p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Boundary}, (\forall c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{compatible}\left(p, c\right) = \forall j: \operatorname{Fin}\left(5\right), (p\left(j\right) \neq \operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233254: six-colour complementary-pair exclusion on a six-column strip*. URL: <https://oeis.org/A233254>.

*Commentary.*

Each old boundary label excludes the corresponding next-row label.

**Definition 1.7 (The literal finite count).**

$$\forall n: \operatorname{Nat}, ((\forall A: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right))) \to (\operatorname{Fin}\left(6\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthLegal}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{rowLegal}, \lambda c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row} \mapsto (\lambda d: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row} \mapsto (\forall j: \operatorname{Fin}\left(5\right), ((c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right) \neq d\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)) \land (\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right) + \operatorname{Fin}.\operatorname{val}\left(d\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right) \neq 5)))), A\right) = ((\exists i: \operatorname{Fin}\left(n\right), ((\operatorname{Fin}.\operatorname{val}\left(i\right) = 0) \land (A\left((i, (0: \operatorname{Fin}\left(6\right)))\right) = (0: \operatorname{Fin}\left(6\right))))) \land ((\forall i: \operatorname{Fin}\left(n\right), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{rowLegal}\left(\lambda j: \operatorname{Fin}\left(6\right) \mapsto (A\left((i, j)\right))\right))) \land ((\forall i: \operatorname{Fin}\left(n\right), (\forall h: \operatorname{Fin}.\operatorname{val}\left(i\right) + 1 < n, (\forall j: \operatorname{Fin}\left(5\right), ((A\left((i, \operatorname{Fin}.\operatorname{succ}\left(j\right))\right) \neq A\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + 1, h\right), \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right)) \land (\operatorname{Fin}.\operatorname{val}\left(A\left((i, \operatorname{Fin}.\operatorname{succ}\left(j\right))\right)\right) + \operatorname{Fin}.\operatorname{val}\left(A\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + 1, h\right), \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right)\right) \neq 5))))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthNormal}\left((false, false), \lambda i: \operatorname{Fin}\left(n\right) \mapsto (\lambda j: \operatorname{Fin}\left(6\right) \mapsto (A\left((i, j)\right)))\right))))))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(\lambda A: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right))) \to (\operatorname{Fin}\left(6\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthLegal}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{rowLegal}, \lambda c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row} \mapsto (\lambda d: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row} \mapsto (\forall j: \operatorname{Fin}\left(5\right), ((c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right) \neq d\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)) \land (\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right) + \operatorname{Fin}.\operatorname{val}\left(d\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right) \neq 5)))), A\right)), \operatorname{Finset}.\operatorname{univ}\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233254: six-colour complementary-pair exclusion on a six-column strip*. URL: <https://oeis.org/A233254>.

*Commentary.*

The filter ranges over every array function and directly uses HardinA233251TriangleStrip.widthLegal at width six, with rowLegal and the displayed antidiagonal row relation. The displayed equality expands that owner predicate. Its published decidability instances and the published pair-strip allowed-colour instance supply the decisions. The existential first-cell condition is false when n is zero. The final predicate is the original row-major scanner predicate at both false flags.

**Definition 1.8 (Reachable boundaries).**

$$\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Boundary}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Valid}\left(s, p\right) = ((\operatorname{Prod}.\operatorname{fst}\left(s\right) = true) \land ((\forall j: \operatorname{Fin}\left(4\right), (p\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \neq p\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right))) \land ((\operatorname{Prod}.\operatorname{snd}\left(s\right) = false) \implies (\forall j: \operatorname{Fin}\left(5\right), (p\left(j\right) \neq (2: \operatorname{Fin}\left(3\right)))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233254: six-colour complementary-pair exclusion on a six-column strip*. URL: <https://oeis.org/A233254>.

*Commentary.*

The first flag is true. Adjacent boundary labels differ. If colour two has not occurred, none of the boundary labels is its pair label two.

**Definition 1.9 (Boundary equality shapes).**

$$\forall p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Boundary}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{shape}\left(p\right) = (\operatorname{if} (p\left((2: \operatorname{Fin}\left(5\right))\right) = p\left((0: \operatorname{Fin}\left(5\right))\right)) \operatorname{then} (\operatorname{if} (p\left((3: \operatorname{Fin}\left(5\right))\right) = p\left((1: \operatorname{Fin}\left(5\right))\right)) \operatorname{then} (\operatorname{if} (p\left((4: \operatorname{Fin}\left(5\right))\right) = p\left((0: \operatorname{Fin}\left(5\right))\right)) \operatorname{then} (0: \operatorname{Fin}\left(8\right)) \operatorname{else} (1: \operatorname{Fin}\left(8\right))) \operatorname{else} (\operatorname{if} (p\left((4: \operatorname{Fin}\left(5\right))\right) = p\left((0: \operatorname{Fin}\left(5\right))\right)) \operatorname{then} (2: \operatorname{Fin}\left(8\right)) \operatorname{else} (3: \operatorname{Fin}\left(8\right)))) \operatorname{else} (\operatorname{if} (p\left((3: \operatorname{Fin}\left(5\right))\right) = p\left((0: \operatorname{Fin}\left(5\right))\right)) \operatorname{then} (\operatorname{if} (p\left((4: \operatorname{Fin}\left(5\right))\right) = p\left((1: \operatorname{Fin}\left(5\right))\right)) \operatorname{then} (4: \operatorname{Fin}\left(8\right)) \operatorname{else} (5: \operatorname{Fin}\left(8\right))) \operatorname{else} (\operatorname{if} (p\left((4: \operatorname{Fin}\left(5\right))\right) = p\left((0: \operatorname{Fin}\left(5\right))\right)) \operatorname{then} (6: \operatorname{Fin}\left(8\right)) \operatorname{else} (7: \operatorname{Fin}\left(8\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.shape` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233254: six-colour complementary-pair exclusion on a six-column strip*. URL: <https://oeis.org/A233254>.

*Commentary.*

The labels A, B, C in the shapes are distinct. In order the shapes are ABABA, ABABC, ABACA, ABACB, ABCAB, ABCAC, ABCBA and ABCBC.

**Definition 1.10 (Boundary transfer moments).**

$$\forall p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Boundary}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{moment}\left(p\right) = \operatorname{Matrix}.\operatorname{vecCons}\left((1: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left(\operatorname{Matrix}.\operatorname{vecCons}\left((26: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((22: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((24: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((18: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((12: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((18: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((20: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((22: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right)\right)\right)\right)\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{shape}\left(p\right)\right), \operatorname{Matrix}.\operatorname{vecCons}\left(\operatorname{Matrix}.\operatorname{vecCons}\left((564: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((456: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((516: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((354: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((222: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((366: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((426: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((462: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right)\right)\right)\right)\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{shape}\left(p\right)\right), \operatorname{Matrix}.\operatorname{vecCons}\left(\operatorname{Matrix}.\operatorname{vecCons}\left((11832: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((9510: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((10812: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((7320: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((4542: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((7620: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((8922: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((9660: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right)\right)\right)\right)\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{shape}\left(p\right)\right), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.moment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233254: six-colour complementary-pair exclusion on a six-column strip*. URL: <https://oeis.org/A233254>.

*Commentary.*

The four entries are the constant one and the first three moments of the label transfer. The published HardinA233255ShapeSymmetry.full_row, used with HardinA233255LiteralBridge.scanner_fibres, gives 64 colour lifts at width six when both scanner flags are true. More generally each column has a factor of zero, one or two: pair zero has two choices; pair one has one choice before the first one, then two; pair two is forbidden before one, has one choice before the first two, then two. Multiplying these factors along the label row reproduces the original colour scanner.

**Definition 1.11 (Unweighted row counts).**

$$\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Boundary}, (\forall b: \operatorname{Bool}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{classCount}\left(s, p, b\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row}} ((\operatorname{if} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{compatible}\left(p, c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right)) \land (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left(s, c\right)\right) = b)))) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.classCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233254: six-colour complementary-pair exclusion on a six-column strip*. URL: <https://oeis.org/A233254>.

*Commentary.*

The final second flag distinguishes the two seen-colour sectors.

**Definition 1.12 (Weighted row counts).**

$$\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Boundary}, (\forall i: \operatorname{Fin}\left(4\right), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{momentCount}\left(s, p, i\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row}} ((\operatorname{if} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{compatible}\left(p, c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right)) \land (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left(s, c\right)\right) = true)))) \operatorname{then} \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{moment}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{pairs}\left(c\right), i\right) \operatorname{else} (0: \operatorname{Int}))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.momentCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233254: six-colour complementary-pair exclusion on a six-column strip*. URL: <https://oeis.org/A233254>.

*Commentary.*

The weight is a moment of the new boundary in the fully seen sector.

**Definition 1.13 (First-row counts).**

$$\forall b: \operatorname{Bool}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{firstCount}\left(b\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row}} ((\operatorname{if} ((c\left((0: \operatorname{Fin}\left(6\right))\right) = (0: \operatorname{Fin}\left(6\right))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left((false, false), c\right)) \land (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left((false, false), c\right)\right) = b)))) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.firstCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233254: six-colour complementary-pair exclusion on a six-column strip*. URL: <https://oeis.org/A233254>.

*Commentary.*

The scanner starts with both flags false and the first colour fixed to zero.

**Definition 1.14 (First-row weighted count).**

$$\forall i: \operatorname{Fin}\left(4\right), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{firstMoment}\left(i\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Row}} ((\operatorname{if} ((c\left((0: \operatorname{Fin}\left(6\right))\right) = (0: \operatorname{Fin}\left(6\right))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left((false, false), c\right)) \land (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left((false, false), c\right)\right) = true)))) \operatorname{then} \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{moment}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{pairs}\left(c\right), i\right) \operatorname{else} (0: \operatorname{Int}))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.firstMoment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233254: six-colour complementary-pair exclusion on a six-column strip*. URL: <https://oeis.org/A233254>.

*Commentary.*

Only fully seen first rows contribute the chosen boundary moment.

**Theorem 1.15 (Summing six-cell functions).**

$$\forall m: \operatorname{Nat}, (\forall f: ((\operatorname{Fin}\left(6\right)) \to (\operatorname{Fin}\left(m\right))) \to (\operatorname{Int}), (\sum_{c: (\operatorname{Fin}\left(6\right)) \to (\operatorname{Fin}\left(m\right))} (f\left(c\right)) = \sum_{a: \operatorname{Fin}\left(m\right)} (\sum_{b: \operatorname{Fin}\left(m\right)} (\sum_{c: \operatorname{Fin}\left(m\right)} (\sum_{d: \operatorname{Fin}\left(m\right)} (\sum_{e: \operatorname{Fin}\left(m\right)} (\sum_{g: \operatorname{Fin}\left(m\right)} (f\left(\operatorname{Matrix}.\operatorname{vecCons}\left(a, \operatorname{Matrix}.\operatorname{vecCons}\left(b, \operatorname{Matrix}.\operatorname{vecCons}\left(c, \operatorname{Matrix}.\operatorname{vecCons}\left(d, \operatorname{Matrix}.\operatorname{vecCons}\left(e, \operatorname{Matrix}.\operatorname{vecCons}\left(g, \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right)\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.sum_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233254: six-colour complementary-pair exclusion on a six-column strip*. URL: <https://oeis.org/A233254>.

*Commentary.*

The sum over functions equals the six iterated sums of their coordinates.

**Theorem 1.16 (One-row transfer counts).**

$$(\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Boundary}, ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Valid}\left(s, p\right)) \implies ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{classCount}\left(s, p, true\right) = (\operatorname{if} (\operatorname{Prod}.\operatorname{snd}\left(s\right)) \operatorname{then} (64: \operatorname{Int}) \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{moment}\left(p, (1: \operatorname{Fin}\left(4\right))\right) \operatorname{else} (800: \operatorname{Int}))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{classCount}\left(s, p, false\right) = (\operatorname{if} (\operatorname{Prod}.\operatorname{snd}\left(s\right)) \operatorname{then} (0: \operatorname{Int}) \operatorname{else} (64: \operatorname{Int}))) \land (\forall i: \operatorname{Fin}\left(3\right), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{momentCount}\left(s, p, \operatorname{Fin}.\operatorname{succ}\left(i\right)\right) = (\operatorname{if} (\operatorname{Prod}.\operatorname{snd}\left(s\right)) \operatorname{then} (64: \operatorname{Int}) \cdot \operatorname{Matrix}.\operatorname{vecCons}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{moment}\left(p, (2: \operatorname{Fin}\left(4\right))\right), \operatorname{Matrix}.\operatorname{vecCons}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{moment}\left(p, (3: \operatorname{Fin}\left(4\right))\right), \operatorname{Matrix}.\operatorname{vecCons}\left((81: \operatorname{Int}) \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{moment}\left(p, (1: \operatorname{Fin}\left(4\right))\right) - (90: \operatorname{Int}) \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{moment}\left(p, (2: \operatorname{Fin}\left(4\right))\right) + (25: \operatorname{Int}) \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{moment}\left(p, (3: \operatorname{Fin}\left(4\right))\right), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\left(i\right) \operatorname{else} \operatorname{Matrix}.\operatorname{vecCons}\left((17216: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((360576: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((7530048: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\left(i\right))))))))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{firstCount}\left(true\right) = (120: \operatorname{Int})) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{firstCount}\left(false\right) = (16: \operatorname{Int})) \land (\forall i: \operatorname{Fin}\left(3\right), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{firstMoment}\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right) = \operatorname{Matrix}.\operatorname{vecCons}\left((2384: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((49344: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((1028832: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\left(i\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233254: six-colour complementary-pair exclusion on a six-column strip*. URL: <https://oeis.org/A233254>.

*Commentary.*

Write r, t, u for moments one, two and three. A fully seen boundary has 64r continuations, with moment sums 64t, 64u and 64(81r-90t+25u). Before colour two has appeared, 64 continuations stay in that sector and 800 enter the fully seen sector. Their moment sums are 17216, 360576 and 7530048. Initially the two counts are 16 and 120, with moment sums 2384, 49344 and 1028832.

**Theorem 1.17 (Barker's identity).**

$$(\left(1 - 64 \cdot \operatorname{PowerSeries}.\operatorname{X}\right) \cdot \left(1 - 1600 \cdot \operatorname{PowerSeries}.\operatorname{X} + 368640 \cdot (\operatorname{PowerSeries}.\operatorname{X})^{2} - 21233664 \cdot (\operatorname{PowerSeries}.\operatorname{X})^{3}\right) \cdot \operatorname{PowerSeries}.\operatorname{mk}\left(\lambda n: \operatorname{Nat} \mapsto ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{a}\left(n\right): \operatorname{Int}))\right): \operatorname{PowerSeries}\left(\operatorname{Int}\right)) = 8 \cdot \operatorname{PowerSeries}.\operatorname{X} \cdot \left(17 - 7488 \cdot \operatorname{PowerSeries}.\operatorname{X} + 974848 \cdot (\operatorname{PowerSeries}.\operatorname{X})^{2} - 40108032 \cdot (\operatorname{PowerSeries}.\operatorname{X})^{3}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233254` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233254","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233254: six-colour complementary-pair exclusion on a six-column strip*. URL: <https://oeis.org/A233254>.

*Commentary.*

After one continuation row the fully seen count has form rU+tZ+uW. Initially (F,U,Z,W)=(864,64,0,0), where F is the other sector. The one-row formulas give F'=64F+17216U+360576Z+7530048W, U'=5184W, Z'=64U-5760W and W'=64Z+1600W. The three latter coordinates have characteristic polynomial z^3-1600z^2+368640z-21233664. The shared literal counting bridge gives a(n+2)=16F(n)+2384U(n)+49344Z(n)+1028832W(n). The initial count a(1)=136 is 16+120. Thus a(n+6)=1664a(n+5)-471040a(n+4) +44826624a(n+3)-1358954496a(n+2). The first terms are 136, 166400, 220626944, 294517735424 and 393427728465920. Coefficient comparison in integer power series proves the identity, including the zero-index convention. The initial constant function can have a zero-eigenvalue part; taking one row first gives the three-dimensional nonzero part.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.Boundary`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.Row`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.Valid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.classCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.firstCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.firstMoment`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.instDecidableRowLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.moment`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.momentCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.pairs`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.rowLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.shape`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.sum_rows`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge](HardinA233255LiteralBridge.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry](HardinA233255ShapeSymmetry.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
