# An Explicit Membership Graph Outside G₂

## Abstract

Cuts in arbitrary words reconstruct their two-letter projections. The explicit membership graph on 24 points and all their subsets has no two-uniform representation.

This construction addresses the unnumbered explicit-graph request in the source conclusion. It does not address Conjecture 31, minimum size or connectedness. The literature note attests the question and definitions, not a published answer. Novelty is suspected only within the supplied September 15, 2026 search scope; worldwide priority remains ASSUMED-UNVERIFIED.

All words are finite lists. Projection and representation use decidable equality on V; cuts need it only on B, reconstruction needs none, and the reconstruction theorem assumes it on A and B. Sum(A,B) is the tagged disjoint union, with injections inl and inr. Unit has the single element *. Empty lists are written []. The left restriction L(w) is filterMap(getLeft?,w), retaining each left letter in its original order. The renaming rho(b) sends inl(a) to inl(a) and inr(*) to inr(b). Its domain is Sum(A,Unit), and it is injective. Natural pred is truncated subtraction by one. The displayed proj, cuts and Rec abbreviate twoProjection, leftCuts and reconstruct. Finset(Fin(24)) is the full power set of the 24 points.

**Definition 1.1 (The actual two-letter projection).**

$$\forall V: \operatorname{Type}, \forall a: V, \forall b: V, \forall w: \operatorname{List}\left(V\right), \operatorname{proj}\left(a, b, w\right) = \operatorname{filter}\left(z\mapsto(z=a \lor z=b), w\right)$$

*Formalization.* `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.twoProjection` (`✓ std3`).

*Citation.* Duncan Adamson, Amanita Dietz, Pamela Fleischmann, Annika Huch, and Silas Cato Sacher (2026). *2-word-π-representable Graphs*. URL: <https://arxiv.org/abs/2605.27183v1>.

*Commentary.*

The filter keeps exactly the letters equal to either specified vertex, preserving order and repetitions. This is the source projection, not an alternation pattern or a union of graph representations.

**Definition 1.2 (Two words, each two-uniform).**

$$\forall V: \operatorname{Type}, \forall G: \operatorname{SimpleGraph}\left(V\right), (\operatorname{InG2}\left(G\right)) \iff (\exists w,v: \operatorname{List}\left(V\right), (\forall z: V, \operatorname{count}\left(z, w\right) = 2) \land ((\forall z: V, \operatorname{count}\left(z, v\right) = 2) \land (\forall x: V, \forall y: V, x \neq y \implies (\operatorname{Adj}\left(G, x, y\right)) \iff (\operatorname{proj}\left(x, y, w\right) = \operatorname{proj}\left(x, y, v\right)))))$$

*Formalization.* `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.InG2` (`✓ std3`).

*Citation.* Duncan Adamson, Amanita Dietz, Pamela Fleischmann, Annika Huch, and Silas Cato Sacher (2026). *2-word-π-representable Graphs*. URL: <https://arxiv.org/abs/2605.27183v1>.

*Commentary.*

Both occurrence conditions quantify over every vertex. Since two is positive, both word alphabets equal the vertex type. The edge equivalence is required for every distinct pair; SimpleGraph already excludes loops and is symmetric.

**Definition 1.3 (Cuts counted in the original word).**

$$\begin{gathered}\forall A,B:\operatorname{Type}, b,c:B, a:A, w:\operatorname{List}\left(\operatorname{Sum}\left(A, B\right)\right)\\\operatorname{cuts}\left(b, []\right) = []\\\operatorname{cuts}\left(b, (\operatorname{inl}\left(a\right))::w\right) = \operatorname{map}\left(\operatorname{succ}, \operatorname{cuts}\left(b, w\right)\right)\\\operatorname{cuts}\left(b, (\operatorname{inr}\left(b\right))::w\right) = (0)::\operatorname{cuts}\left(b, w\right)\\c \neq b \implies \operatorname{cuts}\left(b, (\operatorname{inr}\left(c\right))::w\right) = \operatorname{cuts}\left(b, w\right)\end{gathered}$$

*Formalization.* `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.leftCuts` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson, Amanita Dietz, Pamela Fleischmann, Annika Huch, and Silas Cato Sacher (2026). *2-word-π-representable Graphs*. URL: <https://arxiv.org/abs/2605.27183v1>.

*Commentary.*

Each left letter increments every later cut. An occurrence of b contributes a zero cut before the cuts of the remaining suffix, while other right letters are deleted. Thus the list records, in occurrence order, the number of preceding left letters at every b. Right letters between occurrences are ignored. Consecutive b markers may have the same cut.

**Definition 1.4 (Insert markers at absolute cuts).**

$$\begin{gathered}\forall A:\operatorname{Type}, a:A, r:\operatorname{List}\left(A\right), n:\mathbb{N}, c:\operatorname{List}\left(\mathbb{N}\right)\\\operatorname{Rec}\left(r, []\right) = \operatorname{map}\left(\operatorname{inl}, r\right)\\\operatorname{Rec}\left(r, (0)::c\right) = (\operatorname{inr}\left(*\right))::\operatorname{Rec}\left(r, c\right)\\\operatorname{Rec}\left([], (n + 1)::c\right) = []\\\operatorname{Rec}\left((a)::r, (n + 1)::c\right) = (\operatorname{inl}\left(a\right))::\operatorname{Rec}\left(r, (n)::\operatorname{map}\left(\operatorname{pred}, c\right)\right)\end{gathered}$$

*Formalization.* `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.reconstruct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson, Amanita Dietz, Pamela Fleischmann, Annika Huch, and Silas Cato Sacher (2026). *2-word-π-representable Graphs*. URL: <https://arxiv.org/abs/2605.27183v1>.

*Commentary.*

With no cuts, retain the left list. A zero cut inserts a marker without consuming a left letter, so tied cuts give consecutive markers. A positive cut consumes one left letter and decrements every remaining cut. The branch with an empty left list and a positive first cut returns the empty list; it is unreachable for cuts of actual words. Recursion decreases the sum of the two input lengths.

**Theorem 1.5 (Reconstruction for every word).**

$$\forall A: \operatorname{Type}, \forall B: \operatorname{Type}, \forall a: A, \forall b: B, \forall w: \operatorname{List}\left(\operatorname{Sum}\left(A, B\right)\right), \operatorname{proj}\left(\operatorname{inl}\left(a\right), \operatorname{inr}\left(b\right), w\right) = \operatorname{map}\left(\operatorname{rho}\left(b\right), \operatorname{proj}\left(\operatorname{inl}\left(a\right), \operatorname{inr}\left(*\right), \operatorname{Rec}\left(\operatorname{L}\left(w\right), \operatorname{cuts}\left(b, w\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.projection_eq_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson, Amanita Dietz, Pamela Fleischmann, Annika Huch, and Silas Cato Sacher (2026). *2-word-π-representable Graphs*. URL: <https://arxiv.org/abs/2605.27183v1>.

*Commentary.*

Induct on the original word. A left head shifts all cuts by one; the reconstructor consumes that same head and restores the original cuts. A right head equal to b inserts a zero cut and hence a marker. A different right head changes neither side. Projecting and renaming gives the displayed identity. There is no uniformity, cut-separation or word-order hypothesis.

**Definition 1.6 (The literal membership graph).**

$$\begin{gathered}V = \operatorname{Sum}\left(\operatorname{Fin}\left(24\right), \operatorname{Finset}\left(\operatorname{Fin}\left(24\right)\right)\right)\\\operatorname{U24}:\operatorname{SimpleGraph}\left(V\right)\\\forall a,b:\operatorname{Fin}\left(24\right), S,T:\operatorname{Finset}\left(\operatorname{Fin}\left(24\right)\right)\\(\operatorname{Adj}\left(\operatorname{U24}, \operatorname{inl}\left(a\right), \operatorname{inr}\left(S\right)\right)) \iff (a \in S)\\(\operatorname{Adj}\left(\operatorname{U24}, \operatorname{inr}\left(S\right), \operatorname{inl}\left(a\right)\right)) \iff (a \in S)\\(\neg\operatorname{Adj}\left(\operatorname{U24}, \operatorname{inl}\left(a\right), \operatorname{inl}\left(b\right)\right)) \land (\neg\operatorname{Adj}\left(\operatorname{U24}, \operatorname{inr}\left(S\right), \operatorname{inr}\left(T\right)\right))\end{gathered}$$

*Formalization.* `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.U24` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson, Amanita Dietz, Pamela Fleischmann, Annika Huch, and Silas Cato Sacher (2026). *2-word-π-representable Graphs*. URL: <https://arxiv.org/abs/2605.27183v1>.

*Commentary.*

The carrier is the tagged union V of Fin(24) and all finite subsets of Fin(24). Adjacency is membership across the two tags, in either direction, and false within either part. These equations directly provide symmetry and looplessness. V is finite with 24 + 2^24 = 16,777,240 vertices. The vertex inr(emptyset) is isolated and is permitted by the source definition.

**Theorem 1.7 (No pair of two-uniform words represents U₂₄).**

$$\neg\exists w,v: \operatorname{List}\left(V\right), (\forall z: V, \operatorname{count}\left(z, w\right) = 2) \land ((\forall z: V, \operatorname{count}\left(z, v\right) = 2) \land (\forall x: V, \forall y: V, x \neq y \implies (\operatorname{Adj}\left(\operatorname{U24}, x, y\right)) \iff (\operatorname{proj}\left(x, y, w\right) = \operatorname{proj}\left(x, y, v\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.u24_not_in_g2` (`✓ std3`). ∎

*Resolves.* `Problems/adamson-explicit-graph-outside-g2` (proved) by `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.u24_not_in_g2`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"adamson-explicit-graph-outside-g2","declaration_gid":"D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.u24_not_in_g2","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson, Amanita Dietz, Pamela Fleischmann, Annika Huch, and Silas Cato Sacher (2026). *2-word-π-representable Graphs*. URL: <https://arxiv.org/abs/2605.27183v1>.

*Commentary.*

Assume the displayed representation. Each left restriction has length 48, because each of the 24 left letters occurs twice. Each subset occurs twice, so its cut list has length two, and every cut is between zero and 48. Choose these two cuts in each word to obtain a signature in (Fin(49) × Fin(49))². The domain has 2^24 = 16,777,216 elements, whereas the signature space has 49^4 = 5,764,801. The existing pigeonhole theorem therefore gives distinct subsets S,T with equal signatures. Apply reconstruction separately to w and v for each left letter a. Injectivity of rho(S) and rho(T) shows that equality of the two a/S projections is equivalent to equality of the two a/T projections. Hence a belongs to S exactly when it belongs to T. Finite-set extensionality gives S=T, contradicting distinctness. The two left restrictions may have different orders throughout this proof.

The pigeonhole step directly reuses `D5/S0/Diagonal/PigeonholeFiber.finite_reading_has_fiber`. Count identities, finite cardinalities, marker injectivity and membership extensionality are local steps, not separate new theorems. The live new content in both theorem proofs is reconstruction from cuts. The argument is structural for arbitrary words; the concluding finite arithmetic does not enumerate words or graphs.

## References

- Truth anchor: `D5/S0/Diagonal/PigeonholeFiber.finite_reading_has_fiber`
- Truth anchor: `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.InG2`
- Truth anchor: `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.U24`
- Truth anchor: `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.leftCuts`
- Truth anchor: `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.projection_eq_reconstruction`
- Truth anchor: `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.reconstruct`
- Truth anchor: `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.twoProjection`
- Truth anchor: `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.u24_not_in_g2`
- Dependency: [D5/S0/Diagonal/PigeonholeFiber](../../../S0/Diagonal/PigeonholeFiber.md)
