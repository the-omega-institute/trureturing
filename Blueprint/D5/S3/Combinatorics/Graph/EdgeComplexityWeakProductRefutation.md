# Weak products do not preserve edge-complexity equality

## Abstract

K3 times K3 refutes unrestricted weak-product closure of energy equality.

**Definition 1.1 (Labeled adjacency indicator).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(G.\operatorname{Adj}\right)] \forall sigma \in \operatorname{Equiv}\left(V, \operatorname{Fin}\left(\operatorname{Fintype.card}(V)\right)\right),\; \forall x \in \operatorname{Fin}\left(\operatorname{Fintype.card}(V)\right),\; \forall y \in \operatorname{Fin}\left(\operatorname{Fintype.card}(V)\right),\; \operatorname{f}\left(G, sigma, x, y\right) = if (G.\operatorname{Adj}\left(sigma.\operatorname{symm}\left(x\right), sigma.\operatorname{symm}\left(y\right)\right)) then 1 else 0$$

*Formalization.* `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.f` (`✓ std3`).

*Citation.* V. Gupta, A. Iosevich, J. Iosevich, B. Song, H. Tian (2026). *Edge complexity of graphs*. DOI: [10.48550/arXiv.2607.15598](https://doi.org/10.48550/arXiv.2607.15598). URL: <https://arxiv.org/abs/2607.15598v1>.

*Commentary.*

Section 1, page 1: “Let G = (V, E) be a simple graph with at least one edge and |V| = N. After choosing a labeling of the vertices by Z_N, identify the adjacency matrix with the edge indicator” followed by f : Z_N × Z_N → {0, 1}. A labeling sigma is an equivalence from V to Fin (Fintype.card V). The values zero and one are real numbers.

**Definition 1.2 (Fourier transform).**

$$\forall N \in \mathbb{N},\; \forall a \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right),\; \forall m \in \operatorname{Fin}\left(N\right),\; \forall n \in \operatorname{Fin}\left(N\right),\; \operatorname{fhat}\left(a, m, n\right) = \frac{1}{(N: \mathbb{C})} \cdot \sum_{x:\operatorname{Fin}\left(N\right)} (\sum_{y:\operatorname{Fin}\left(N\right)} ((\operatorname{a}\left(x, y\right): \mathbb{C}) \cdot \operatorname{Complex.exp}(\frac{-2 \cdot (\operatorname{Real.pi}: \mathbb{C}) \cdot \operatorname{Complex.I} \cdot (\operatorname{val}\left(m\right) \cdot \operatorname{val}\left(x\right) + \operatorname{val}\left(n\right) \cdot \operatorname{val}\left(y\right): \mathbb{C})}{(N: \mathbb{C})})))$$

*Formalization.* `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.fhat` (`✓ std3`).

*Citation.* V. Gupta, A. Iosevich, J. Iosevich, B. Song, H. Tian (2026). *Edge complexity of graphs*. DOI: [10.48550/arXiv.2607.15598](https://doi.org/10.48550/arXiv.2607.15598). URL: <https://arxiv.org/abs/2607.15598v1>.

*Commentary.*

Section 1, page 1: “Its two-dimensional discrete Fourier transform is” the displayed sum. Fin N represents the cyclic labels; val reads their natural-number representatives. Both the indicator and the natural-number expression in the exponent are coerced to Complex. Division here is in Complex.

**Definition 1.3 (Fourier ratio).**

$$\forall N \in \mathbb{N},\; \forall a \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right),\; \operatorname{FR}\left(a\right) = \frac{\sum_{m:\operatorname{Fin}\left(N\right)} (\sum_{n:\operatorname{Fin}\left(N\right)} (\left\lVert \operatorname{fhat}\left(a, m, n\right) \right\rVert))}{\operatorname{Real.sqrt}(\sum_{m:\operatorname{Fin}\left(N\right)} (\sum_{n:\operatorname{Fin}\left(N\right)} (\left\lVert \operatorname{fhat}\left(a, m, n\right) \right\rVert^{2})))}$$

*Formalization.* `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.FR` (`✓ std3`).

*Citation.* V. Gupta, A. Iosevich, J. Iosevich, B. Song, H. Tian (2026). *Edge complexity of graphs*. DOI: [10.48550/arXiv.2607.15598](https://doi.org/10.48550/arXiv.2607.15598). URL: <https://arxiv.org/abs/2607.15598v1>.

*Commentary.*

Section 1, page 2: “The Fourier ratio of f is” the displayed quotient of the entrywise l1 norm by the Frobenius norm. Both sums range over all Fin N labels; the denominator is the real square root of the sum of squared complex norms.

**Definition 1.4 (Minimum over labelings).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(G.\operatorname{Adj}\right)] \operatorname{FRmin}\left(G\right) = \operatorname{Finset.univ}.\operatorname{inf}'(\langle\operatorname{Fintype.equivFin}(V), by simp\rangle, fun (sigma: \operatorname{Equiv}\left(V, \operatorname{Fin}\left(\operatorname{Fintype.card}(V)\right)\right)) \mapsto \operatorname{FR}\left(\operatorname{f}\left(G, sigma\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.FRmin` (`✓ std3`).

*Citation.* V. Gupta, A. Iosevich, J. Iosevich, B. Song, H. Tian (2026). *Edge complexity of graphs*. DOI: [10.48550/arXiv.2607.15598](https://doi.org/10.48550/arXiv.2607.15598). URL: <https://arxiv.org/abs/2607.15598v1>.

*Commentary.*

Section 1, page 2: “If fσ is the adjacency matrix produced by a vertex labeling σ, the edge complexity introduced in [7] is” the minimum Fourier ratio over all labelings. Finset.univ is the finite set of equivalences V to Fin (Fintype.card V), which contains Fintype.equivFin V. Its inf' is its attained minimum, including for an empty vertex type.

**Definition 1.5 (Graph energy).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(G.\operatorname{Adj}\right)] \operatorname{energy}\left(G\right) = \sum_{j:V} (\left|(G.\operatorname{isHermitian_{adjMatrix}}(\mathbb{R})).\operatorname{eigenvalues}\left(j\right)\right|)$$

*Formalization.* `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.energy` (`✓ std3`).

*Citation.* V. Gupta, A. Iosevich, J. Iosevich, B. Song, H. Tian (2026). *Edge complexity of graphs*. DOI: [10.48550/arXiv.2607.15598](https://doi.org/10.48550/arXiv.2607.15598). URL: <https://arxiv.org/abs/2607.15598v1>.

*Commentary.*

Section 1, page 2: “The graph energy is” the sum of the absolute adjacency eigenvalues, “where λ1(G), . . . , λN(G) are the adjacency eigenvalues.” The Hermitian proof is G.isHermitian_adjMatrix Real; eigenvalues are real, indexed by V.

**Definition 1.6 (Number of edges).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(G.\operatorname{Adj}\right)] \operatorname{size}\left(G\right) = G.\operatorname{edgeFinset.card}$$

*Formalization.* `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.size` (`✓ std3`).

*Citation.* V. Gupta, A. Iosevich, J. Iosevich, B. Song, H. Tian (2026). *Edge complexity of graphs*. DOI: [10.48550/arXiv.2607.15598](https://doi.org/10.48550/arXiv.2607.15598). URL: <https://arxiv.org/abs/2607.15598v1>.

*Commentary.*

The size s in Theorem 1.1 counts unoriented edges once. The cardinality of G.edgeFinset implements that convention.

**Definition 1.7 (Energy equality with a positive edge count).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(G.\operatorname{Adj}\right)] \operatorname{AttainsEquality}\left(G\right) \Leftrightarrow \left(0 < \operatorname{size}\left(G\right) \land \operatorname{FRmin}\left(G\right) = \frac{\operatorname{energy}\left(G\right)}{\operatorname{Real.sqrt}(2 \cdot (\operatorname{size}\left(G\right): \mathbb{R}))}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.AttainsEquality` (`✓ std3`).

*Citation.* V. Gupta, A. Iosevich, J. Iosevich, B. Song, H. Tian (2026). *Edge complexity of graphs*. DOI: [10.48550/arXiv.2607.15598](https://doi.org/10.48550/arXiv.2607.15598). URL: <https://arxiv.org/abs/2607.15598v1>.

*Commentary.*

Theorem 1.1, page 2, states the lower bound FR_min(G) at least E(G)/sqrt(2s) for size s greater than zero. AttainsEquality is exactly a positive size together with equality in that bound.

**Definition 1.8 (Unrestricted weak-product closure).**

$$claim \Leftrightarrow \left(\forall V \in Type,\; \forall W \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] [\operatorname{Fintype}\left(W\right)] [\operatorname{DecidableEq}\left(W\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall H \in \operatorname{SimpleGraph}\left(W\right),\; [\operatorname{DecidableRel}\left(G.\operatorname{Adj}\right)] [\operatorname{DecidableRel}\left(H.\operatorname{Adj}\right)] \operatorname{AttainsEquality}\left(G\right) \Rightarrow \left(\operatorname{AttainsEquality}\left(H\right) \Rightarrow \operatorname{AttainsEquality}\left(\operatorname{D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap.dirProd}(G, H)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.claim` (`✓ std3`).

*Citation.* V. Gupta, A. Iosevich, J. Iosevich, B. Song, H. Tian (2026). *Edge complexity of graphs*. DOI: [10.48550/arXiv.2607.15598](https://doi.org/10.48550/arXiv.2607.15598). URL: <https://arxiv.org/abs/2607.15598v1>.

*Commentary.*

Remark after Corollary 3.10, page 18: “Remark. The coprimality hypothesis is not merely a technicality in the present argument: it is what permits the product labeling to be viewed as a cyclic labeling. Proposition 3.7 does not prove closure under arbitrary weak products. Consequently, unrestricted closure of the equality class under the weak product has not been established. Whether such closure holds is a natural open question.” The equality class is AttainsEquality. The quantifiers cover all finite vertex types and simple graphs, with decidable adjacency. Definition 3.1, page 15: “Definition 3.1. Let G and H be graphs. Their weak product G × H has vertex set V(G) × V(H), and (g₁, h₁) is adjacent to (g₂, h₂) if and only if g₁ is adjacent to g₂ in G and h₁ is adjacent to h₂ in H.” The operation in the formula is the existing dirProd, with exactly that adjacency relation.

**Theorem 1.9 (The closure assertion is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/gupta-iosevich-2026-edge-complexity-weak-product` (refuted) by `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gupta-iosevich-2026-edge-complexity-weak-product","declaration_gid":"D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* V. Gupta, A. Iosevich, J. Iosevich, B. Song, H. Tian (2026). *Edge complexity of graphs*. DOI: [10.48550/arXiv.2607.15598](https://doi.org/10.48550/arXiv.2607.15598). URL: <https://arxiv.org/abs/2607.15598v1>.

*Commentary.*

Both factors are the complete graph on Fin 3. Their Fourier ratio minimum is 4/sqrt(6), their energy is four and their size is three. The product has size eighteen and energy sixteen. For every labeling its Fourier ratio is strictly greater than 8/3. Equality would make its squared adjacency circulant; the identity A squared equals 2J plus 2I minus A would then make A circulant. No zero-one circulant matrix of order nine satisfies that identity. The sign matrix (6A+3I-2J)/9 supplies the norm bound and its equality conditions.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.AttainsEquality`
- Truth anchor: `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.FR`
- Truth anchor: `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.FRmin`
- Truth anchor: `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.energy`
- Truth anchor: `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.f`
- Truth anchor: `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.fhat`
- Truth anchor: `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.size`
- Dependency: [D5/S3/Quantum/Dynamics/PolygonalFourierCouplings](../../Quantum/Dynamics/PolygonalFourierCouplings.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../../Quantum/Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Matrix/CommutatorGap](../../Quantum/Matrix/CommutatorGap.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity](../../Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.md)
- Dependency: [D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap](../../StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.md)
