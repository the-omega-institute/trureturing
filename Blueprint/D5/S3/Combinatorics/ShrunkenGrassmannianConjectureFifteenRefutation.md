# Conjecture 15 of CayleyPy-4 fails at k = 5, L = 4, N = 13

## Abstract

The k = 5 clause of Conjecture 15 of CayleyPy-4 is false: without inverses, rotations of five consecutive letters need at least 9 moves to turn 0000111111111 into its reversal, whichever way the rotation acts, while the clause gives 8.

**Definition 1.1 (Directed moves).**

$$\operatorname{StepDir}\left(left, k, x, y\right) \Leftrightarrow (\exists i \in \mathbb{N},\; i + k \le \operatorname{length}\left(x\right) \land y = (\operatorname{if} left \operatorname{then} \operatorname{rotL}\left(k, i, x\right) \operatorname{else} \operatorname{rotR}\left(k, i, x\right)))$$

*Formalization.* `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureFifteenRefutation.StepDir` (`✓ std3`).

*Citation.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

Without inverses a move applies the cycle on a window of k consecutive positions, which rotates the window one place left or one place right depending on the convention for the action of a permutation on a word; the flag left selects the convention.

**Definition 1.2 (Directed reachability within m moves).**

$$(\operatorname{ReachDir}\left(left, k, 0, x, y\right) \Leftrightarrow (y = x)) \land (\operatorname{ReachDir}\left(left, k, m + 1, x, y\right) \Leftrightarrow ((\operatorname{ReachDir}\left(left, k, m, x, y\right)) \lor (\exists z \in \operatorname{List}\left(Bool\right),\; \operatorname{ReachDir}\left(left, k, m, x, z\right) \land \operatorname{StepDir}\left(left, k, z, y\right))))$$

*Formalization.* `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureFifteenRefutation.ReachDir` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

ReachDir(left, k, m, x, y) says that y is reached from x in at most m directed moves.

**Definition 1.3 (Largest directed distance from the central state).**

$$\operatorname{eccDir}\left(left, k, L, N\right) = \operatorname{sInf}\left(\{m\in\mathbb{N}:\forall y \in \operatorname{List}\left(Bool\right),\; (\operatorname{IsVertex}\left(L, N, y\right)) \Rightarrow (\operatorname{ReachDir}\left(left, k, m, \operatorname{normalWord}\left(L, N - L\right), y\right))\}\right)$$

*Formalization.* `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureFifteenRefutation.eccDir` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

The least m such that every vertex is reached from the central state within m directed moves. A vertex is a word of length N with exactly L zeros (IsVertex(L, N, x)); the central state [0]^L + [1]^(N - L), L zeros followed by N - L ones, is normalWord(L, N - L) of D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange. IsVertex, rotL and rotR are reused from D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.

**Definition 1.4 (Directed diameter).**

$$\operatorname{diamDir}\left(left, k, L, N\right) = \operatorname{sInf}\left(\{m\in\mathbb{N}:\forall x \in \operatorname{List}\left(Bool\right),\; \forall y \in \operatorname{List}\left(Bool\right),\; (\operatorname{IsVertex}\left(L, N, x\right) \land \operatorname{IsVertex}\left(L, N, y\right)) \Rightarrow (\operatorname{ReachDir}\left(left, k, m, x, y\right))\}\right)$$

*Formalization.* `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureFifteenRefutation.diamDir` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

The least m such that every vertex is reached from every vertex within m directed moves.

**Definition 1.5 (The k = 5 clause of Conjecture 15).**

$$\operatorname{clauseFive}\left(D\right) \Leftrightarrow (\forall L \in \mathbb{N},\; \forall N \in \mathbb{N},\; (4 \le L \land L + 9 \le N) \Rightarrow (D\left(5, L, N\right) = L \cdot \left\lfloor\frac{N - L}{4}\right\rfloor + (\operatorname{if} (N - L) \bmod 4 = 0 \operatorname{then} 1 \operatorname{else} 0)))$$

*Formalization.* `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureFifteenRefutation.clauseFive` (`✓ std3`).

*Citation.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

For all L >= 4 and N >= L + 9, with t + 1 = N - L, the diameter is L times the floor of (t + 1)/4, plus 1 when t + 1 is divisible by 4.

**Definition 1.6 (The clause for some convention and reading).**

$$claim \Leftrightarrow (\exists left \in Bool,\; (\operatorname{clauseFive}\left(\operatorname{eccDir}\left(left\right)\right)) \lor (\operatorname{clauseFive}\left(\operatorname{diamDir}\left(left\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureFifteenRefutation.claim` (`✓ std3`).

*Citation.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

The clause holds for one of the two conventions and one of the two readings of the diameter.

**Theorem 1.7 (Refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureFifteenRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/chervov-2026-cayleypy4-conjecture-fifteen-refutation` (refuted) by `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureFifteenRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chervov-2026-cayleypy4-conjecture-fifteen-refutation","declaration_gid":"D5/S3/Combinatorics/ShrunkenGrassmannianConjectureFifteenRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

Count the inversions of a word, the pairs of positions holding a one before a zero. Rotating five consecutive letters one place carries one letter past the other four, so it changes the count by at most 4, and a directed move is in either convention such a rotation. The central state 0000111111111 has no inversion and its reversal 1111111110000 has 36, so reaching the reversal takes at least 9 moves. If the central eccentricity or the diameter were 8 at L = 4, N = 13 in either convention, the least element of its defining set would be 8, and the reversal, a vertex, would be within 8 moves of the central state, also a vertex. The clause gives 4 times the floor of 9/4, which is 8, since 9 is not divisible by 4.

## References

- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureFifteenRefutation.ReachDir`
- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureFifteenRefutation.StepDir`
- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureFifteenRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureFifteenRefutation.clauseFive`
- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureFifteenRefutation.diamDir`
- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureFifteenRefutation.eccDir`
- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureFifteenRefutation.result`
- Dependency: [D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter](ShrunkenGrassmannianThreeCycleDiameter.md)
