# Conjecture 16 of CayleyPy-4 fails at k = 4, L = 2, N = 5

## Abstract

Conjecture 16 of CayleyPy-4 is false under both readings of the diameter: with rotations of four consecutive letters on words with two zeros and three ones, the word 11010 is three moves from 00111, one more than the conjectured formula.

**Definition 1.1 (The k = 4 formula).**

$$\operatorname{formulaFour}\left(L, N\right) = \operatorname{if} 3 \mid L \operatorname{then} \left\lfloor\frac{L}{3}\right\rfloor \cdot (N - L) \operatorname{else} \left\lfloor\frac{L \cdot (N - L) + 2}{3}\right\rfloor$$

*Formalization.* `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureSixteenRefutation.formulaFour` (`✓ std3`).

*Citation.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

The k = 4 clause of Conjecture 16: L/3 times (N - L) when 3 divides L, and the floor of (L(N - L) + 2)/3 otherwise.

**Definition 1.2 (The k = 5 formula).**

$$\operatorname{formulaFive}\left(L, N\right) = \left\lfloor\frac{L \cdot N + 2}{4}\right\rfloor - 2 \cdot \left\lfloor\frac{L^{2}}{8}\right\rfloor - (\operatorname{if} L \bmod 4 = 2 \land N \bmod 4 = 2 \operatorname{then} 1 \operatorname{else} 0)$$

*Formalization.* `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureSixteenRefutation.formulaFive` (`✓ std3`).

*Citation.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

The k = 5 clause of Conjecture 16: the floor of (LN + 2)/4, minus twice the floor of L^2/8, minus 1 when both L and N are congruent to 2 modulo 4.

**Definition 1.3 (Conjecture 16 under a reading of the diameter).**

$$\operatorname{conjSixteen}\left(D\right) \Leftrightarrow (\left((\forall L \in \mathbb{N},\; \forall N \in \mathbb{N},\; (\left(2 \le L \land L \le N\right) \land 3 < N) \Rightarrow (D\left(3, L, N\right) = \left\lfloor\frac{L \cdot (N - L) + 1}{2}\right\rfloor)) \land (\forall L \in \mathbb{N},\; \forall N \in \mathbb{N},\; (\left(2 \le L \land L \le N\right) \land 4 < N) \Rightarrow (D\left(4, L, N\right) = \operatorname{formulaFour}\left(L, N\right)))\right) \land (\exists C \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall N \in \mathbb{N},\; (C \le L \land C \le N - L) \Rightarrow (D\left(5, L, N\right) = \operatorname{formulaFive}\left(L, N\right))))$$

*Formalization.* `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureSixteenRefutation.conjSixteen` (`✓ std3`).

*Citation.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

The three clauses of Conjecture 16 for a reading D(k, L, N) of the diameter: k = 3 from L >= 2, k = 4 from L >= 2, both for N > k, and k = 5 once L and N - L exceed some constant.

**Definition 1.4 (The conjecture under either reading).**

$$claim \Leftrightarrow (\operatorname{conjSixteen}\left(ecc\right) \lor \operatorname{conjSixteen}\left(diam\right))$$

*Formalization.* `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureSixteenRefutation.claim` (`✓ std3`).

*Citation.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

The conjecture holds for the largest distance from the central state or for the largest distance between two vertices.

**Theorem 1.5 (Refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureSixteenRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/chervov-2026-cayleypy4-conjecture-sixteen-refutation` (refuted) by `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureSixteenRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chervov-2026-cayleypy4-conjecture-sixteen-refutation","declaration_gid":"D5/S3/Combinatorics/ShrunkenGrassmannianConjectureSixteenRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

Every word reached from x within m moves lies in the list obtained from [x] by m times appending all rotations of all listed words. For k = 4 and the words of length 5 the kernel evaluates this list for m = 2 from 00111 and finds that it does not contain 11010, which has two zeros and three ones. If either reading gave the value 2 at L = 2, N = 5, the least element of the defining set would be 2, so 11010 would be reached from 00111, which is also a vertex, within two moves. The formula gives the floor of 8/3, which is 2, because 3 does not divide 2.

## References

- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureSixteenRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureSixteenRefutation.conjSixteen`
- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureSixteenRefutation.formulaFive`
- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureSixteenRefutation.formulaFour`
- Truth anchor: `D5/S3/Combinatorics/ShrunkenGrassmannianConjectureSixteenRefutation.result`
- Dependency: [D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter](ShrunkenGrassmannianThreeCycleDiameter.md)
