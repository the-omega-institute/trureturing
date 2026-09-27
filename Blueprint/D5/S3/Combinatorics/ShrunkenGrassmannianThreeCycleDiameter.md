# Diameter of the inverse-closed consecutive 3-cycle Schreier coset graph

## Abstract

For 2 <= L <= N and N > 3, on binary words with L zeros and N - L ones, where a move rotates three consecutive letters one place in either direction, every word can be turned into every other in at most the ceiling of L(N - L)/2 moves, and turning the sorted word 0...01...1 into its reversal needs that many, as conjectured for k = 3 in Conjecture 16 of CayleyPy-4.

**Definition 1.1 (The consecutive cycle on a window).**

$$\operatorname{rotL}\left(k, i, x\right) = \operatorname{append}\left(\operatorname{append}\left(\operatorname{take}\left(i, x\right), \operatorname{rotate}\left(\operatorname{take}\left(k, \operatorname{drop}\left(i, x\right)\right), 1\right)\right), \operatorname{drop}\left(i + k, x\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.rotL` (`✓ std3`).

*Citation.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

The cycle (i, i + 1, ..., i + k - 1) acts on a word by rotating the window of length k starting at position i one place to the left: the letters a_1, a_2, ..., a_k of the window become a_2, ..., a_k, a_1.

**Definition 1.2 (The inverse cycle).**

$$\operatorname{rotR}\left(k, i, x\right) = \operatorname{append}\left(\operatorname{append}\left(\operatorname{take}\left(i, x\right), \operatorname{rotate}\left(\operatorname{take}\left(k, \operatorname{drop}\left(i, x\right)\right), k - 1\right)\right), \operatorname{drop}\left(i + k, x\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.rotR` (`✓ std3`).

*Citation.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

The inverse cycle rotates the same window one place to the right: a_1, ..., a_(k-1), a_k become a_k, a_1, ..., a_(k-1).

**Definition 1.3 (Edges of the inverse-closed graph).**

$$\operatorname{Step}\left(k, x, y\right) \Leftrightarrow (\exists i \in \mathbb{N},\; i + k \le \operatorname{length}\left(x\right) \land \left((y = \operatorname{rotL}\left(k, i, x\right)) \lor (y = \operatorname{rotR}\left(k, i, x\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.Step` (`✓ std3`).

*Citation.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

Two words are adjacent when some window of k consecutive positions lies inside the word and one word arises from the other by the cycle or its inverse on that window.

**Definition 1.4 (Reachability within m moves).**

$$(\operatorname{Reach}\left(k, 0, x, y\right) \Leftrightarrow (y = x)) \land (\operatorname{Reach}\left(k, m + 1, x, y\right) \Leftrightarrow ((\operatorname{Reach}\left(k, m, x, y\right)) \lor (\exists z \in \operatorname{List}\left(Bool\right),\; \operatorname{Reach}\left(k, m, x, z\right) \land \operatorname{Step}\left(k, z, y\right))))$$

*Formalization.* `D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.Reach` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

Reach(k, m, x, y) says that y is reached from x in at most m moves: with no move only x itself, and with m + 1 moves every word reached within m moves together with every neighbour of such a word.

**Definition 1.5 (Vertices of the coset graph).**

$$\operatorname{IsVertex}\left(L, N, x\right) \Leftrightarrow (\operatorname{length}\left(x\right) = N \land \operatorname{count}\left(false, x\right) = L)$$

*Formalization.* `D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.IsVertex` (`✓ std3`).

*Citation.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

The vertices of the Schreier coset graph of S_N / (S_L x S_(N - L)) are the words of length N with exactly L zeros.

**Definition 1.6 (Largest distance from the central state).**

$$\operatorname{ecc}\left(k, L, N\right) = \operatorname{sInf}\left(\{m\in\mathbb{N}:\forall y \in \operatorname{List}\left(Bool\right),\; (\operatorname{IsVertex}\left(L, N, y\right)) \Rightarrow (\operatorname{Reach}\left(k, m, \operatorname{normalWord}\left(L, N - L\right), y\right))\}\right)$$

*Formalization.* `D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.ecc` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

The least m such that every vertex is reached from the central state within m moves. The central state [0]^L + [1]^(N - L), L zeros followed by N - L ones, is normalWord(L, N - L) of D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange, reused here. This is the quantity CayleyPy's growth computation reports as the diameter of a coset graph.

**Definition 1.7 (Diameter).**

$$\operatorname{diam}\left(k, L, N\right) = \operatorname{sInf}\left(\{m\in\mathbb{N}:\forall x \in \operatorname{List}\left(Bool\right),\; \forall y \in \operatorname{List}\left(Bool\right),\; (\operatorname{IsVertex}\left(L, N, x\right) \land \operatorname{IsVertex}\left(L, N, y\right)) \Rightarrow (\operatorname{Reach}\left(k, m, x, y\right))\}\right)$$

*Formalization.* `D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.diam` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

The least m such that every vertex is reached from every vertex within m moves, the diameter in the graph-theoretic sense.

**Definition 1.8 (The k = 3 clause of Conjecture 16).**

$$claim \Leftrightarrow (\forall L \in \mathbb{N},\; \forall N \in \mathbb{N},\; (\left(2 \le L \land L \le N\right) \land 3 < N) \Rightarrow (\operatorname{ecc}\left(3, L, N\right) = \left\lfloor\frac{L \cdot (N - L) + 1}{2}\right\rfloor \land \operatorname{diam}\left(3, L, N\right) = \left\lfloor\frac{L \cdot (N - L) + 1}{2}\right\rfloor))$$

*Formalization.* `D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.claim` (`✓ std3`).

*Citation.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

Conjecture 16 of the source (inverse-closed case), clause k = 3: for L >= 2 the diameter is the ceiling of L(N - L)/2, which equals the floor of (L(N - L) + 1)/2. Both readings of the diameter are included, for N > 3 because the source takes n > k.

**Theorem 1.9 (Proof of the k = 3 clause).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.result` (`✓ std3`). ∎

*Resolves.* `Problems/chervov-2026-cayleypy4-three-cycle-grassmannian-diameter` (proved) by `D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chervov-2026-cayleypy4-three-cycle-grassmannian-diameter","declaration_gid":"D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

Lower bound: count the inversions, the pairs of positions p < q holding a one at p and a zero at q. A rotation of three consecutive letters leaves the pairs outside the window and the pairs across its boundary unchanged, so it changes the count by at most 2. The central state has no inversion and its reversal, the N - L ones followed by the L zeros, has L(N - L), so reaching the reversal from the central state takes at least the ceiling of L(N - L)/2 moves. Upper bound, from any vertex x to any vertex y, by induction on N from N = 3, where the three arrangements are pairwise one rotation apart. Let b be the last letter of y and let rho be the number of letters after the last b in x. Moving that b across them, two places per move and with one final move when rho is odd, costs the ceiling of rho/2 moves, after which the first N - 1 letters are handled by induction. With M = N - L, this fits the budget for b = 1, where rho <= L, unless L is odd, M is even and rho = L, and for b = 0, where rho <= M, unless M is odd, L is even and rho = M. In these two cases x ends in the other letter, so the same peeling from y to x fits the budget for that letter, and a path from y to x reversed is a path from x to y.

## References

- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.IsVertex`
- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.Reach`
- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.Step`
- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.claim`
- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.diam`
- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.ecc`
- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.result`
- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.rotL`
- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.rotR`
- Dependency: [D5/S1/Digit/Carry/ListInversions](../../S1/Digit/Carry/ListInversions.md)
- Dependency: [D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange](../ConceptDynamics/Completion/CommutingCompletionExchange.md)
