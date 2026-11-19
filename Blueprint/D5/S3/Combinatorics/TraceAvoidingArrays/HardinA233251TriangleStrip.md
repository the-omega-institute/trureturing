# Six-colour horizontal and antidiagonal exclusion

## Abstract

Barker's generating function for normalized six-colour three-column arrays.

OEIS A233251, revision 9, defines arrays on n rows and three columns. Horizontal and antidiagonal bonds exclude equal colours and colours summing to five. Vertical and main-diagonal neighbours are unconstrained. The upper-left colour is zero. Every 2, 3 and 4 has an earlier 1, and every 3 an earlier 2, in row-major order. The coefficient at index zero is zero. Seen, good and finish are the existing width-independent scanning definitions in HardinA233175PairStrip; beta is BooleanRankThreeK4.beta, with fibres {0,5}, {1,4}, {2,3}.

**Definition 1.1 (A row).**

$$Row = (\operatorname{Fin}\left(3\right)) \to \operatorname{Fin}\left(6\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

A row is an ordered triple of colours.

**Definition 1.2 (Horizontal bonds).**

$$\forall c: Row, ((\operatorname{rowLegal}\left(c\right)) \iff (\forall j: \operatorname{Fin}\left(2\right), ((c\left(\operatorname{Fin.castSucc}\left(j\right)\right) \neq c\left(\operatorname{Fin.succ}\left(j\right)\right)) \land (\operatorname{val}\left(c\left(\operatorname{Fin.castSucc}\left(j\right)\right)\right) + \operatorname{val}\left(c\left(\operatorname{Fin.succ}\left(j\right)\right)\right) \neq 5))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.rowLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

The two bonds lie between columns zero and one, and one and two.

**Definition 1.3 (The boundary pair labels).**

$$\forall c: Row, (\operatorname{pairs}\left(c\right) = (\operatorname{beta}\left(c\left(1\right)\right), \operatorname{beta}\left(c\left(2\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.pairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

Only the pair labels of columns one and two constrain the following row.

**Definition 1.4 (Antidiagonal bonds).**

$$\forall p: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right)), (\forall c: Row, ((\operatorname{compatible}\left(p, c\right)) \iff ((\operatorname{Prod.fst}\left(p\right) \neq \operatorname{beta}\left(c\left(0\right)\right)) \land (\operatorname{Prod.snd}\left(p\right) \neq \operatorname{beta}\left(c\left(1\right)\right)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

The preceding column-one label excludes the next column-zero label, and the preceding column-two label excludes the next column-one label.

**Definition 1.5 (Reachable boundary classes).**

$$\forall s: Seen, (\forall p: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right)), ((\operatorname{Valid}\left(s, p\right)) \iff ((\operatorname{Prod.fst}\left(s\right) = true) \land ((\operatorname{Prod.fst}\left(p\right) \neq \operatorname{Prod.snd}\left(p\right)) \land ((\operatorname{Prod.snd}\left(s\right) = false) \implies ((\operatorname{Prod.fst}\left(p\right) \neq 2) \land (\operatorname{Prod.snd}\left(p\right) \neq 2)))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

Colour one has occurred, the boundary labels differ, and before colour two occurs neither label is two.

**Definition 1.6 (The literal filtered array count).**

$$\forall n: Nat, (\operatorname{a}\left(n\right) = \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda A: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(3\right))) \to \operatorname{Fin}\left(6\right) \mapsto ((\exists i: \operatorname{Fin}\left(n\right), ((\operatorname{val}\left(i\right) = 0) \land (A\left((i, 0)\right) = 0))) \land ((\forall i: \operatorname{Fin}\left(n\right), (\operatorname{rowLegal}\left(\lambda j: \operatorname{Fin}\left(3\right) \mapsto A\left((i, j)\right)\right))) \land ((\forall i: \operatorname{Fin}\left(n\right), (\forall h: \operatorname{val}\left(i\right) + 1 < n, (\forall j: \operatorname{Fin}\left(2\right), ((A\left((i, \operatorname{Fin.succ}\left(j\right))\right) \neq A\left((\operatorname{Fin.mk}\left(\operatorname{val}\left(i\right) + 1, h\right), \operatorname{Fin.castSucc}\left(j\right))\right)) \land (\operatorname{val}\left(A\left((i, \operatorname{Fin.succ}\left(j\right))\right)\right) + \operatorname{val}\left(A\left((\operatorname{Fin.mk}\left(\operatorname{val}\left(i\right) + 1, h\right), \operatorname{Fin.castSucc}\left(j\right))\right)\right) \neq 5))))) \land (\forall i: \operatorname{Fin}\left(n\right), (\forall j: \operatorname{Fin}\left(3\right), ((((A\left((i, j)\right) = 2) \lor ((A\left((i, j)\right) = 3) \lor (A\left((i, j)\right) = 4))) \implies (\exists r: \operatorname{Fin}\left(n\right), (\exists k: \operatorname{Fin}\left(3\right), (((r < i) \lor ((r = i) \land (k < j))) \land (A\left((r, k)\right) = 1))))) \land ((A\left((i, j)\right) = 3) \implies (\exists r: \operatorname{Fin}\left(n\right), (\exists k: \operatorname{Fin}\left(3\right), (((r < i) \lor ((r = i) \land (k < j))) \land (A\left((r, k)\right) = 2))))))))))), \operatorname{Finset.univ}\left(\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

The filter ranges over every function on Fin n times Fin 3. The strict lexicographic order on cell indices is the row-major order. The first-cell existential is false for the empty array.

**Definition 1.7 (Counting one row by its final flag).**

$$\forall s: Seen, (\forall p: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right)), (\forall b: Bool, (\operatorname{classCount}\left(s, p, b\right) = \sum_{c: Row} ((\operatorname{if} ((\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{compatible}\left(p, c\right)) \land ((\operatorname{good}\left(s, c\right)) \land (\operatorname{Prod.snd}\left(\operatorname{finish}\left(s, c\right)\right) = b)))) \operatorname{then} (1: Int) \operatorname{else} (0: Int))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.classCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

This integer sum counts exactly the legal normalized rows with the specified final second flag.

**Definition 1.8 (Counting first rows by their final flag).**

$$\forall b: Bool, (\operatorname{firstCount}\left(b\right) = \sum_{c: Row} ((\operatorname{if} ((c\left(0\right) = 0) \land ((\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{good}\left((false, false), c\right)) \land (\operatorname{Prod.snd}\left(\operatorname{finish}\left((false, false), c\right)\right) = b)))) \operatorname{then} (1: Int) \operatorname{else} (0: Int))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.firstCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

This integer sum fixes the first colour to zero and starts the shared scanner with both flags false.

**Theorem 1.9 (The one-row class counts).**

$$(\forall s: Seen, (\forall p: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right)), ((\operatorname{Valid}\left(s, p\right)) \implies ((\operatorname{classCount}\left(s, p, true\right) = (\operatorname{if} (\operatorname{Prod.snd}\left(s\right)) \operatorname{then} (48: Int) \operatorname{else} (20: Int))) \land (\operatorname{classCount}\left(s, p, false\right) = (\operatorname{if} (\operatorname{Prod.snd}\left(s\right)) \operatorname{then} (0: Int) \operatorname{else} (8: Int))))))) \land ((\operatorname{firstCount}\left(true\right) = (1: Int)) \land (\operatorname{firstCount}\left(false\right) = (2: Int)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

The eight reachable boundary classes split according to the second seen flag. A fully seen boundary has 48 continuations. A boundary with only colour one seen has 20 continuations entering the fully seen class and eight staying in its class. The first row gives one fully seen array and two arrays with only colour one seen.

**Definition 1.10 (Row-major normalization at any width).**

$$\forall k: \operatorname{Nat}, (\forall n: \operatorname{Nat}, (\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall f: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthNormal}\left(s, f\right) = \forall i: \operatorname{Fin}\left(n\right), (\forall j: \operatorname{Fin}\left(k\right), ((((f\left(i\right)\left(j\right) = (2: \operatorname{Fin}\left(6\right))) \lor ((f\left(i\right)\left(j\right) = (3: \operatorname{Fin}\left(6\right))) \lor (f\left(i\right)\left(j\right) = (4: \operatorname{Fin}\left(6\right))))) \implies ((\operatorname{Prod}.\operatorname{fst}\left(s\right) = true) \lor (\exists r: \operatorname{Fin}\left(n\right), (\exists t: \operatorname{Fin}\left(k\right), (((r < i) \lor ((r = i) \land (t < j))) \land (f\left(r\right)\left(t\right) = (1: \operatorname{Fin}\left(6\right)))))))) \land ((f\left(i\right)\left(j\right) = (3: \operatorname{Fin}\left(6\right))) \implies ((\operatorname{Prod}.\operatorname{snd}\left(s\right) = true) \lor (\exists r: \operatorname{Fin}\left(n\right), (\exists t: \operatorname{Fin}\left(k\right), (((r < i) \lor ((r = i) \land (t < j))) \land (f\left(r\right)\left(t\right) = (2: \operatorname{Fin}\left(6\right))))))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthNormal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

For every row and column index, earlier means strict lexicographic order. The two initial flags account for colours already seen before these rows.

**Definition 1.11 (A row transfer at any width).**

$$\forall k: \operatorname{Nat}, (\forall B: \operatorname{Type}, (\forall R: ((\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)) \to \operatorname{Prop}, (\forall P: ((\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)) \to B, (\forall C: (B) \to ((\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)) \to \operatorname{Prop}, ([\operatorname{DecidablePred}\left(R\right)] [\operatorname{DecidableRel}\left(C\right)] \forall w: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}) \to (B) \to \operatorname{Int}, (\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: B, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthStep}\left(R, P, C, w, s, p\right) = \sum_{c: (\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)} ((\operatorname{if} ((R\left(c\right)) \land ((C\left(p, c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right)))) \operatorname{then} w\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left(s, c\right), P\left(c\right)\right) \operatorname{else} (0: Int)))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

R is the row predicate, P extracts the boundary, and C tests the next row. All predicates carry their Lean deciding instances.

**Definition 1.12 (Continuation counts at any width).**

$$\forall k: \operatorname{Nat}, (\forall B: \operatorname{Type}, (\forall R: ((\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)) \to \operatorname{Prop}, (\forall P: ((\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)) \to B, (\forall C: (B) \to ((\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)) \to \operatorname{Prop}, ([\operatorname{DecidablePred}\left(R\right)] [\operatorname{DecidableRel}\left(C\right)] (\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: B, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthV}\left(R, P, C, 0\right)\left(s, p\right) = (1: Int)))) \land (\forall n: \operatorname{Nat}, (\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall p: B, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthV}\left(R, P, C, n + 1\right)\left(s, p\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthStep}\left(R, P, C, \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthV}\left(R, P, C, n\right), s, p\right))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthV` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

The empty continuation has weight one. Each further row applies the transfer.

**Definition 1.13 (First-row aggregation at any width).**

$$\forall k: \operatorname{Nat}, ([\operatorname{NeZero}\left(k\right)] \forall B: \operatorname{Type}, (\forall R: ((\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)) \to \operatorname{Prop}, (\forall P: ((\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)) \to B, ([\operatorname{DecidablePred}\left(R\right)] \forall w: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}) \to (B) \to \operatorname{Int}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthTotal}\left(R, P, w\right) = \sum_{c: (\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)} ((\operatorname{if} ((c\left((0: \operatorname{Fin}\left(k\right))\right) = (0: \operatorname{Fin}\left(6\right))) \land ((R\left(c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left((false, false), c\right)))) \operatorname{then} w\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left((false, false), c\right), P\left(c\right)\right) \operatorname{else} (0: Int))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthTotal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

A positive width provides the column-zero index. The initial flags are false.

**Theorem 1.14 (The literal count equals transfer).**

$$\forall k: \operatorname{Nat}, ([\operatorname{NeZero}\left(k\right)] \forall B: \operatorname{Type}, (\forall R: ((\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)) \to \operatorname{Prop}, (\forall P: ((\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)) \to B, (\forall C: (B) \to ((\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)) \to \operatorname{Prop}, ([\operatorname{DecidablePred}\left(R\right)] [\operatorname{DecidableRel}\left(C\right)] \forall E: ((\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)) \to ((\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)) \to \operatorname{Prop}, ([\operatorname{DecidableRel}\left(E\right)] (\forall c: (\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right), (\forall d: (\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right), ((E\left(c, d\right)) \iff (C\left(P\left(c\right), d\right))))) \implies (\forall n: \operatorname{Nat}, ((\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(\lambda A: ((\operatorname{Fin}\left(n + 1\right)) \times (\operatorname{Fin}\left(k\right))) \to \operatorname{Fin}\left(6\right) \mapsto ((\exists i: \operatorname{Fin}\left(n + 1\right), ((\operatorname{Fin}.\operatorname{val}\left(i\right) = 0) \land (A\left((i, (0: \operatorname{Fin}\left(k\right)))\right) = (0: \operatorname{Fin}\left(6\right))))) \land ((\forall i: \operatorname{Fin}\left(n + 1\right), (R\left(\lambda j: \operatorname{Fin}\left(k\right) \mapsto (A\left((i, j)\right))\right))) \land ((\forall i: \operatorname{Fin}\left(n + 1\right), (\forall h: \operatorname{Fin}.\operatorname{val}\left(i\right) + 1 < n + 1, (E\left(\lambda j: \operatorname{Fin}\left(k\right) \mapsto (A\left((i, j)\right)), \lambda j: \operatorname{Fin}\left(k\right) \mapsto (A\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + 1, h\right), j)\right))\right)))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthNormal}\left((false, false), \lambda i: \operatorname{Fin}\left(n + 1\right) \mapsto (\lambda j: \operatorname{Fin}\left(k\right) \mapsto (A\left((i, j)\right)))\right))))), \operatorname{Finset}.\operatorname{univ}\left(\right)\right)\right): Int) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthTotal}\left(R, P, \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthV}\left(R, P, C, n\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.width_counting_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

Assume a positive width k and a boundary type B. The bond predicate E must be equivalent to C after applying P to the preceding row. The displayed filter is the literal array count on n+1 rows. R, C and E have deciding instances. Decomposing an array into its first row and tail gives the identity. Nat.div denotes natural quotient division and Nat.mod its nonnegative remainder; neither operation enters these formulas.

**Theorem 1.15 (A bond depends only on pair labels).**

$$\forall x: \operatorname{Fin}\left(6\right), (\forall y: \operatorname{Fin}\left(6\right), (((x \neq y) \land (\operatorname{Fin}.\operatorname{val}\left(x\right) + \operatorname{Fin}.\operatorname{val}\left(y\right) \neq 5)) \iff (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(x\right) \neq \operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(y\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.colour_bond_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

The fibres of beta are the complementary pairs. Distinct fibres are exactly the pairs of colours that are unequal and do not sum to five.

**Theorem 1.16 (Barker's generating function).**

$$\left(1 - 8 \cdot X\right) \cdot \left(1 - 48 \cdot X\right) \cdot \operatorname{PowerSeries.mk}\left(\lambda n: Nat \mapsto (\operatorname{a}\left(n\right): Int)\right) = X \cdot \left(3 - 64 \cdot X\right) \operatorname{in} \operatorname{PowerSeries}\left(Int\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233251` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233251","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

Let U(k) and V(k) be the continuation counts with and without colour two already seen. Then U(0)=V(0)=1, U(k+1)=48U(k), and V(k+1)=8V(k)+20U(k). Decomposing the literal arrays into their first row and tail gives a(k+1)=U(k)+2V(k). Consequently a(n+3)=56a(n+2)-384a(n+1), with a(1)=3 and a(2)=104. Coefficient comparison proves the displayed identity in integer power series; every natural count is cast to an integer before forming the series.

**Definition 1.17 (The literal legality predicate at any width).**

$$\forall k: \operatorname{Nat}, ([\operatorname{NeZero}\left(k\right)] \forall R: ((\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)) \to \operatorname{Prop}, (\forall E: ((\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)) \to ((\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)) \to \operatorname{Prop}, (\forall n: \operatorname{Nat}, (\forall A: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(k\right))) \to \operatorname{Fin}\left(6\right), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthLegal}\left(R, E, A\right) = ((\exists i: \operatorname{Fin}\left(n\right), ((\operatorname{Fin}.\operatorname{val}\left(i\right) = 0) \land (A\left((i, (0: \operatorname{Fin}\left(k\right)))\right) = (0: \operatorname{Fin}\left(6\right))))) \land ((\forall i: \operatorname{Fin}\left(n\right), (R\left(\lambda j: \operatorname{Fin}\left(k\right) \mapsto (A\left((i, j)\right))\right))) \land ((\forall i: \operatorname{Fin}\left(n\right), (\forall h: \operatorname{Fin}.\operatorname{val}\left(i\right) + 1 < n, (E\left(\lambda j: \operatorname{Fin}\left(k\right) \mapsto (A\left((i, j)\right)), \lambda j: \operatorname{Fin}\left(k\right) \mapsto (A\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + 1, h\right), j)\right))\right)))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthNormal}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), \lambda i: \operatorname{Fin}\left(n\right) \mapsto (\lambda j: \operatorname{Fin}\left(k\right) \mapsto (A\left((i, j)\right)))\right))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

The first cell is zero, each row satisfies R, consecutive rows satisfy E, and the shared scanner imposes row-major normalization. The Fin.val projections and typed finite zeroes are explicit.

**Definition 1.18 (Deciding row-major normalization).**

$$\forall k: \operatorname{Nat}, (\forall n: \operatorname{Nat}, (\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall f: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthInstDecidableNormal}\left(s, f\right): \operatorname{Decidable}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthNormal}\left(s, f\right))\right)) = \operatorname{inferInstanceAs}\left((\operatorname{Decidable}\left((\forall i: \operatorname{Fin}\left(n\right), (\forall j: \operatorname{Fin}\left(k\right), ((((f\left(i\right)\left(j\right) = (2: \operatorname{Fin}\left(6\right))) \lor ((f\left(i\right)\left(j\right) = (3: \operatorname{Fin}\left(6\right))) \lor (f\left(i\right)\left(j\right) = (4: \operatorname{Fin}\left(6\right))))) \implies ((\operatorname{Prod}.\operatorname{fst}\left(s\right) = \operatorname{Bool}.\operatorname{true}) \lor (\exists r: \operatorname{Fin}\left(n\right), (\exists t: \operatorname{Fin}\left(k\right), (((r < i) \lor ((r = i) \land (t < j))) \land (f\left(r\right)\left(t\right) = (1: \operatorname{Fin}\left(6\right)))))))) \land ((f\left(i\right)\left(j\right) = (3: \operatorname{Fin}\left(6\right))) \implies ((\operatorname{Prod}.\operatorname{snd}\left(s\right) = \operatorname{Bool}.\operatorname{true}) \lor (\exists r: \operatorname{Fin}\left(n\right), (\exists t: \operatorname{Fin}\left(k\right), (((r < i) \lor ((r = i) \land (t < j))) \land (f\left(r\right)\left(t\right) = (2: \operatorname{Fin}\left(6\right)))))))))))\right))\right)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthInstDecidableNormal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

The defining expression is inferInstanceAs for the displayed finite universal quantification and its two implications.

**Definition 1.19 (Deciding a row scan at any width).**

$$\begin{aligned}\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall c: (\operatorname{Fin}\left(0\right)) \to \operatorname{Fin}\left(6\right), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthInstDecidableGood}\left(s, c\right): \operatorname{Decidable}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right))\right)) = \operatorname{Decidable}.\operatorname{isTrue}\left(\operatorname{True}.\operatorname{intro}\right)))\\\forall k: \operatorname{Nat}, (\forall s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}, (\forall c: (\operatorname{Fin}\left(k + 1\right)) \to \operatorname{Fin}\left(6\right), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthInstDecidableGood}\left(s, c\right): \operatorname{Decidable}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right))\right)) = \operatorname{instDecidableAnd}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{instDecidableAllowed}\left(s, c\left((0: \operatorname{Fin}\left(k + 1\right))\right)\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthInstDecidableGood}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{advance}\left(s, c\left((0: \operatorname{Fin}\left(k + 1\right))\right)\right), \operatorname{Fin}.\operatorname{tail}\left(c\right)\right)\right))))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthInstDecidableGood` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

These are the zero and successor equations of the defining induction on k. The successor uses the original allowed decision and the recursive tail decision with the advanced flags; no positive-width instance is required.

**Definition 1.20 (Deciding the literal legality predicate).**

$$\forall k: \operatorname{Nat}, ([\operatorname{NeZero}\left(k\right)] \forall R: ((\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)) \to \operatorname{Prop}, (\forall E: ((\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)) \to ((\operatorname{Fin}\left(k\right)) \to \operatorname{Fin}\left(6\right)) \to \operatorname{Prop}, ([\operatorname{DecidablePred}\left(R\right)] [\operatorname{DecidableRel}\left(E\right)] \forall n: \operatorname{Nat}, (\forall A: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(k\right))) \to \operatorname{Fin}\left(6\right), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthInstDecidableLegal}\left(R, E, A\right): \operatorname{Decidable}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthLegal}\left(R, E, A\right))\right)) = \operatorname{inferInstanceAs}\left((\operatorname{Decidable}\left(((\exists i: \operatorname{Fin}\left(n\right), ((\operatorname{Fin}.\operatorname{val}\left(i\right) = 0) \land (A\left((i, (0: \operatorname{Fin}\left(k\right)))\right) = (0: \operatorname{Fin}\left(6\right))))) \land ((\forall i: \operatorname{Fin}\left(n\right), (R\left(\lambda j: \operatorname{Fin}\left(k\right) \mapsto (A\left((i, j)\right))\right))) \land ((\forall i: \operatorname{Fin}\left(n\right), (\forall h: \operatorname{Fin}.\operatorname{val}\left(i\right) + 1 < n, (E\left(\lambda j: \operatorname{Fin}\left(k\right) \mapsto (A\left((i, j)\right)), \lambda j: \operatorname{Fin}\left(k\right) \mapsto (A\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + 1, h\right), j)\right))\right)))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthNormal}\left((\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false}), \lambda i: \operatorname{Fin}\left(n\right) \mapsto (\lambda j: \operatorname{Fin}\left(k\right) \mapsto (A\left((i, j)\right)))\right)))))\right))\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthInstDecidableLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

The defining expression is inferInstanceAs for the four displayed conjuncts, using the deciding instances for R and E.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.Row`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.Valid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.classCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.colour_bond_iff`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.firstCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.pairs`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.rowLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthInstDecidableGood`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthInstDecidableLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthInstDecidableNormal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthNormal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthStep`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthTotal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthV`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.width_counting_bridge`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
