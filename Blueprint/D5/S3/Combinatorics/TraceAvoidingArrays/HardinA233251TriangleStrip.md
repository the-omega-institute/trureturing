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

**Theorem 1.10 (Barker's generating function).**

$$\left(1 - 8 \cdot X\right) \cdot \left(1 - 48 \cdot X\right) \cdot \operatorname{PowerSeries.mk}\left(\lambda n: Nat \mapsto (\operatorname{a}\left(n\right): Int)\right) = X \cdot \left(3 - 64 \cdot X\right) \operatorname{in} \operatorname{PowerSeries}\left(Int\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233251: six-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233251>.

*Commentary.*

Let U(k) and V(k) be the continuation counts with and without colour two already seen. Then U(0)=V(0)=1, U(k+1)=48U(k), and V(k+1)=8V(k)+20U(k). Decomposing the literal arrays into their first row and tail gives a(k+1)=U(k)+2V(k). Consequently a(n+3)=56a(n+2)-384a(n+1), with a(1)=3 and a(2)=104. Coefficient comparison proves the displayed identity in integer power series; every natural count is cast to an integer before forming the series.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.Row`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.Valid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.classCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.firstCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.pairs`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.rowLegal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
