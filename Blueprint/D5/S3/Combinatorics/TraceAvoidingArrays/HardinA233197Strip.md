# The literal complementary-pair strip

## Abstract

Barker's generating function for eight-colour three-column arrays.

OEIS A233197, revision 8, specifies horizontal, vertical and antidiagonal bonds, with the main diagonal unconstrained. A bond forbids equal colours and colours summing to seven. The first colour is zero. Before any 2,3,4,5,6 there is a 1; before any 3,4,5 there is a 2; before any 4 there is a 3. Earlier means strict row-major order. The imported scanner uses exactly these restrictions. Fin.val is the natural value of a Fin index; all indices start at zero. Nat.sub is truncated subtraction. Nat.div is natural quotient division; Nat.mod is its nonnegative remainder. The imported beta uses Fin.ofNat 4, hence reduction modulo four, on min(c.val,7-c.val). No quotient occurs in the displayed identity.

**Definition 1.1 (A three-column row).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{Row} = \left((\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(8\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233197: eight-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233197>.

*Commentary.*

Rows are functions, with the three distinct column indices 0,1,2.

**Definition 1.2 (Horizontal bonds).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{rowLegal}\left(c\right) = \left(((c\left((0: \operatorname{Fin}\left(3\right))\right) \ne c\left((1: \operatorname{Fin}\left(3\right))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left((0: \operatorname{Fin}\left(3\right))\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(c\left((1: \operatorname{Fin}\left(3\right))\right)\right)) \ne 7)) \land ((c\left((1: \operatorname{Fin}\left(3\right))\right) \ne c\left((2: \operatorname{Fin}\left(3\right))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left((1: \operatorname{Fin}\left(3\right))\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(c\left((2: \operatorname{Fin}\left(3\right))\right)\right)) \ne 7))\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.rowLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233197: eight-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233197>.

*Commentary.*

The horizontal bonds are 0--1 and 1--2.

**Definition 1.3 (Bonds between consecutive rows).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{Row}), (\forall (d: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{bonds}\left(c, d\right) = \left((\forall (j: \operatorname{Fin}\left(3\right)), ((c\left(j\right) \ne d\left(j\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left(j\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(d\left(j\right)\right)) \ne 7))) \land (((c\left((1: \operatorname{Fin}\left(3\right))\right) \ne d\left((0: \operatorname{Fin}\left(3\right))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left((1: \operatorname{Fin}\left(3\right))\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(d\left((0: \operatorname{Fin}\left(3\right))\right)\right)) \ne 7)) \land ((c\left((2: \operatorname{Fin}\left(3\right))\right) \ne d\left((1: \operatorname{Fin}\left(3\right))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left((2: \operatorname{Fin}\left(3\right))\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(d\left((1: \operatorname{Fin}\left(3\right))\right)\right)) \ne 7)))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.bonds` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233197: eight-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233197>.

*Commentary.*

There are three vertical and two antidiagonal bonds.

**Definition 1.4 (The literal filtered finite count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(((A: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(3\right))) \to (\operatorname{Fin}\left(8\right))) \mapsto (\exists (i: \operatorname{Fin}\left(n\right)), ((\operatorname{Fin}.\operatorname{val}\left(i\right) = 0) \land (A\left((i, (0: \operatorname{Fin}\left(3\right)))\right) = (0: \operatorname{Fin}\left(8\right))))) \land ((\forall (i: \operatorname{Fin}\left(n\right)), (((A\left((i, (0: \operatorname{Fin}\left(3\right)))\right) \ne A\left((i, (1: \operatorname{Fin}\left(3\right)))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(A\left((i, (0: \operatorname{Fin}\left(3\right)))\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(A\left((i, (1: \operatorname{Fin}\left(3\right)))\right)\right)) \ne 7)) \land ((A\left((i, (1: \operatorname{Fin}\left(3\right)))\right) \ne A\left((i, (2: \operatorname{Fin}\left(3\right)))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(A\left((i, (1: \operatorname{Fin}\left(3\right)))\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(A\left((i, (2: \operatorname{Fin}\left(3\right)))\right)\right)) \ne 7)))) \land ((\forall (i: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1) < n), ((\forall (j: \operatorname{Fin}\left(3\right)), ((A\left((i, j)\right) \ne A\left(((\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1), h\right): \operatorname{Fin}\left(n\right)), j)\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(A\left((i, j)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(A\left(((\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1), h\right): \operatorname{Fin}\left(n\right)), j)\right)\right)) \ne 7))) \land (((A\left((i, (1: \operatorname{Fin}\left(3\right)))\right) \ne A\left(((\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1), h\right): \operatorname{Fin}\left(n\right)), (0: \operatorname{Fin}\left(3\right)))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(A\left((i, (1: \operatorname{Fin}\left(3\right)))\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(A\left(((\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1), h\right): \operatorname{Fin}\left(n\right)), (0: \operatorname{Fin}\left(3\right)))\right)\right)) \ne 7)) \land ((A\left((i, (2: \operatorname{Fin}\left(3\right)))\right) \ne A\left(((\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1), h\right): \operatorname{Fin}\left(n\right)), (1: \operatorname{Fin}\left(3\right)))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(A\left((i, (2: \operatorname{Fin}\left(3\right)))\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(A\left(((\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1), h\right): \operatorname{Fin}\left(n\right)), (1: \operatorname{Fin}\left(3\right)))\right)\right)) \ne 7)))))) \land (\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left(3\right)), ((((A\left((i, j)\right) = (2: \operatorname{Fin}\left(8\right))) \lor ((A\left((i, j)\right) = (3: \operatorname{Fin}\left(8\right))) \lor ((A\left((i, j)\right) = (4: \operatorname{Fin}\left(8\right))) \lor ((A\left((i, j)\right) = (5: \operatorname{Fin}\left(8\right))) \lor (A\left((i, j)\right) = (6: \operatorname{Fin}\left(8\right))))))) \Rightarrow (\exists (r: \operatorname{Fin}\left(n\right)), (\exists (k: \operatorname{Fin}\left(3\right)), (((r < i) \lor ((r = i) \land (k < j))) \land (A\left((r, k)\right) = (1: \operatorname{Fin}\left(8\right))))))) \land ((((A\left((i, j)\right) = (3: \operatorname{Fin}\left(8\right))) \lor ((A\left((i, j)\right) = (4: \operatorname{Fin}\left(8\right))) \lor (A\left((i, j)\right) = (5: \operatorname{Fin}\left(8\right))))) \Rightarrow (\exists (r: \operatorname{Fin}\left(n\right)), (\exists (k: \operatorname{Fin}\left(3\right)), (((r < i) \lor ((r = i) \land (k < j))) \land (A\left((r, k)\right) = (2: \operatorname{Fin}\left(8\right))))))) \land ((A\left((i, j)\right) = (4: \operatorname{Fin}\left(8\right))) \Rightarrow (\exists (r: \operatorname{Fin}\left(n\right)), (\exists (k: \operatorname{Fin}\left(3\right)), (((r < i) \lor ((r = i) \land (k < j))) \land (A\left((r, k)\right) = (3: \operatorname{Fin}\left(8\right)))))))))))))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(3\right))) \to (\operatorname{Fin}\left(8\right))\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233197: eight-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233197>.

*Commentary.*

The filter uses HardinA233196Strip.widthLegal rowLegal bonds directly, with the owner's widthInstDecidableLegal instance. The displayed predicate unfolds its row, bond and initial widthNormal conditions; the initial seen-colour flags are all false. The first-cell existential fails at height zero, so a(0)=0.

**Definition 1.5 (The preceding row's pair labels).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{pairs}\left(c\right) = ((j: \operatorname{Fin}\left(3\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{beta}\left(c\left(j\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.pairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233197: eight-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233197>.

*Commentary.*

All three column labels are retained, with fibres {0,7},{1,6},{2,5},{3,4}.

**Definition 1.6 (Pair-label bond constraints).**

$$\forall (p: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(4\right))), (\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{compatible}\left(p, c\right) = \left((\forall (j: \operatorname{Fin}\left(3\right)), (p\left(j\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{beta}\left(c\left(j\right)\right))) \land ((p\left((1: \operatorname{Fin}\left(3\right))\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{beta}\left(c\left((0: \operatorname{Fin}\left(3\right))\right)\right)) \land (p\left((2: \operatorname{Fin}\left(3\right))\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{beta}\left(c\left((1: \operatorname{Fin}\left(3\right))\right)\right)))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233197: eight-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233197>.

*Commentary.*

The same three vertical and two antidiagonal inequalities are imposed.

**Definition 1.7 (Reachable boundary invariant).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (p: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(4\right))), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{Valid}\left(s, p\right) = \left((\operatorname{Prod}.\operatorname{fst}\left(s\right) = \operatorname{Bool}.\operatorname{true}) \land ((p\left((0: \operatorname{Fin}\left(3\right))\right) \ne p\left((1: \operatorname{Fin}\left(3\right))\right)) \land ((p\left((1: \operatorname{Fin}\left(3\right))\right) \ne p\left((2: \operatorname{Fin}\left(3\right))\right)) \land (((\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{Bool}.\operatorname{false}) \Rightarrow (\forall (j: \operatorname{Fin}\left(3\right)), (\operatorname{Fin}.\operatorname{val}\left(p\left(j\right)\right) < 2))) \land (((\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{Bool}.\operatorname{false}) \Rightarrow (\forall (j: \operatorname{Fin}\left(3\right)), (\operatorname{Fin}.\operatorname{val}\left(p\left(j\right)\right) < 3))) \land ((\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{Bool}.\operatorname{true}) \Rightarrow (\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{Bool}.\operatorname{true}))))))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233197: eight-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233197>.

*Commentary.*

The invariant includes legal horizontal labels and prefix-ordered flags.

**Definition 1.8 (Five boundary classes).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (p: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(4\right))), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{seenClass}\left(s, p\right) = (\operatorname{if} (\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right)) \operatorname{then} (\operatorname{if} (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right)) \operatorname{then} (\operatorname{if} (p\left((0: \operatorname{Fin}\left(3\right))\right) = p\left((2: \operatorname{Fin}\left(3\right))\right)) \operatorname{then} (3: \operatorname{Fin}\left(5\right)) \operatorname{else} (4: \operatorname{Fin}\left(5\right))) \operatorname{else} (\operatorname{if} (p\left((0: \operatorname{Fin}\left(3\right))\right) = p\left((2: \operatorname{Fin}\left(3\right))\right)) \operatorname{then} (1: \operatorname{Fin}\left(5\right)) \operatorname{else} (2: \operatorname{Fin}\left(5\right)))) \operatorname{else} (0: \operatorname{Fin}\left(5\right)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.seenClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233197: eight-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233197>.

*Commentary.*

Class 0 has not seen colour 2. Classes 1 and 2 have seen 2 but not 3, and distinguish equal and unequal outer labels. Classes 3 and 4 have seen 3 and make the same outer-label distinction. Class 1 is included in the invariant although the initial vector never reaches it.

**Definition 1.9 (The finite transfer matrix).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{T} = \operatorname{Matrix}.\operatorname{vecCons}\left(\operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((2: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((2: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right), \operatorname{Matrix}.\operatorname{vecCons}\left(\operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((8: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((8: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right), \operatorname{Matrix}.\operatorname{vecCons}\left(\operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((8: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((4: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((16: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right), \operatorname{Matrix}.\operatorname{vecCons}\left(\operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((16: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((16: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right), \operatorname{Matrix}.\operatorname{vecCons}\left(\operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((8: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((40: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233197: eight-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233197>.

*Commentary.*

Both indices have type Fin 5. The fully seen block is [[16,16],[8,40]], with characteristic polynomial t^2-56t+512. The not-yet-fully-seen sector has eigenvalue 8 and transient zero eigenvalues.

**Definition 1.10 (Single-row class counts).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (p: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(4\right))), (\forall (b: \operatorname{Fin}\left(5\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{classCount}\left(s, p, b\right) = \sum_{(c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{Row})} ((\operatorname{if} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{compatible}\left(p, c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{good}\left(s, c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{seenClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{finish}\left(s, c\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{pairs}\left(c\right)\right) = b)))) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.classCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233197: eight-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233197>.

*Commentary.*

The sum tests all 512 colour rows and their terminal boundary class.

**Definition 1.11 (Initial class counts).**

$$\forall (b: \operatorname{Fin}\left(5\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{firstCount}\left(b\right) = \sum_{(c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{Row})} ((\operatorname{if} ((c\left((0: \operatorname{Fin}\left(3\right))\right) = (0: \operatorname{Fin}\left(8\right))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{good}\left((\operatorname{Bool}.\operatorname{false}, (\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false})), c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{seenClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{finish}\left((\operatorname{Bool}.\operatorname{false}, (\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false})), c\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{pairs}\left(c\right)\right) = b)))) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.firstCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233197: eight-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233197>.

*Commentary.*

The first rows (0,1,0),(0,1,7),(0,1,2) give vector [2,0,1,0,0].

**Theorem 1.12 (The finite certificate).**

$$(\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (p: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(4\right))), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{Valid}\left(s, p\right)) \Rightarrow (\forall (b: \operatorname{Fin}\left(5\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{classCount}\left(s, p, b\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{T}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{seenClass}\left(s, p\right), b\right)))))) \land ((\forall (b: \operatorname{Fin}\left(5\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{firstCount}\left(b\right) = \operatorname{Matrix}.\operatorname{vecCons}\left((2: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((1: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right)\left(b\right))) \land (\operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{T})^{((1) + (3))}, (1: (\operatorname{Fin}\left(5\right)) \to (\operatorname{Int}))\right) = \sum_{(j: \operatorname{Fin}\left(3\right))} (\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{Matrix}.\operatorname{vecCons}\left((4096: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left(-(960: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((64: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\left(j\right), \operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{T})^{((1) + (\operatorname{Fin}.\operatorname{val}\left(j\right)))}, (1: (\operatorname{Fin}\left(5\right)) \to (\operatorname{Int}))\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233197: eight-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233197>.

*Commentary.*

The rows of T are [0,0,0,2,2], [0,0,0,8,8], [0,0,8,4,16], [0,0,0,16,16], [0,0,0,8,40]. The vector identity removes the transient zero eigenspace before applying the cubic relation.

**Theorem 1.13 (Barker's generating function).**

$$((((1: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) - (((8: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))))) \cdot ((((1: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) - (((56: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))))) + (((512: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) \cdot (((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right)))^{(2)})))) \cdot (\operatorname{PowerSeries}.\operatorname{mk}\left(((n: \operatorname{Nat}) \mapsto (\operatorname{Nat}.\operatorname{cast}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233197Strip}.\operatorname{a}\left(n\right)\right): \operatorname{Int}))\right)) = ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) \cdot (((((3: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) - (((156: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))))) + (((2016: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) \cdot (((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right)))^{(2)}))) - (((7168: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) \cdot (((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right)))^{(3)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233197` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233197","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233197: eight-colour complementary-pair exclusion on a three-column strip*. URL: <https://oeis.org/A233197>.

*Commentary.*

Let w(n)=Matrix.mulVec (T^n) 1. The imported width_counting_bridge and induction through the finite class counts give a(n+1)=2w(n)(0) +w(n)(2). This is iteration of the normalized one-step class map, the Function.Semiconj.iterate_right pattern. The finite vector relation and TransferMatrix.scalarRelationShift give a(n+5)=64a(n+4)-960a(n+3) +4096a(n+2). The first four counts are 3,36,1440,62720. Coefficient comparison, including a(0)=0, proves the identity. Natural counts are cast to Int before forming the series. This is a formal combinatorial identity; no assertion of a physical realization is required.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.Row`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.T`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.Valid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.bonds`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.classCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.firstCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.pairs`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.rowLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.seenClass`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip](HardinA233196Strip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
