# Counting Kepler's signed support-two eigenvectors

## Abstract

The equivalence-class sum counts Kepler's supports, with two signed vectors per support.

**Definition 1.1 (The Bα matrix).**

$$\forall V \in Type,\; \forall [\operatorname{Fintype}\left(V\right)], \forall [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall [\operatorname{DecidableRel}\left(G.\operatorname{Adj}\right)], \forall \alpha : \mathbb{R}, \operatorname{bAlpha}\left(G, \alpha\right) = \alpha \cdot \operatorname{SimpleGraph}.\operatorname{adjMatrix}\left(G, \mathbb{R}\right) + (1 - \alpha) \cdot \operatorname{SimpleGraph}.\operatorname{lapMatrix}\left(G, \mathbb{R}\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.bAlpha` (`✓ std3`).

*Citation.* Garrett Kepler (2026). *Some Spectral Properties of the Bα Matrix of a Graph*. DOI: [10.48550/arXiv.2607.25221](https://doi.org/10.48550/arXiv.2607.25221). URL: <https://arxiv.org/abs/2607.25221v1>.

*Commentary.*

Kepler's Definition 1.5, printed p. 1 of arXiv:2607.25221v1, defines the matrix for α in [0,1]. A is the adjacency matrix, D the diagonal degree matrix and L = D − A the graph Laplacian. The same expression defines the Lean matrix for every real α.

**Definition 1.2 (Agreement outside a pair).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall u \in V,\; \forall v \in V,\; \operatorname{Twins}\left(G, u, v\right) \Leftrightarrow (\forall w \in V,\; (w \neq u) \Rightarrow \left((w \neq v) \Rightarrow \left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G, w, u\right) \Leftrightarrow (\operatorname{SimpleGraph}.\operatorname{Adj}\left(G, w, v\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.Twins` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Garrett Kepler (2026). *Some Spectral Properties of the Bα Matrix of a Graph*. DOI: [10.48550/arXiv.2607.25221](https://doi.org/10.48550/arXiv.2607.25221). URL: <https://arxiv.org/abs/2607.25221v1>.

*Commentary.*

Adjacency is compared at every vertex outside the two named vertices.

**Definition 1.3 (Signed coordinate vector).**

$$\forall V \in Type,\; \forall [\operatorname{DecidableEq}\left(V\right)], \forall u \in V,\; \forall v \in V,\; \operatorname{signedPair}\left(u, v\right) = \operatorname{Pi}.\operatorname{single}\left(u, 1\right) - \operatorname{Pi}.\operatorname{single}\left(v, 1\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.signedPair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Garrett Kepler (2026). *Some Spectral Properties of the Bα Matrix of a Graph*. DOI: [10.48550/arXiv.2607.25221](https://doi.org/10.48550/arXiv.2607.25221). URL: <https://arxiv.org/abs/2607.25221v1>.

*Commentary.*

The first endpoint contributes +1 and the second contributes −1.

**Definition 1.4 (Eigenvalue on a qualifying pair).**

$$\forall V \in Type,\; \forall [\operatorname{Fintype}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall [\operatorname{DecidableRel}\left(G.\operatorname{Adj}\right)], \forall \alpha : \mathbb{R}, \forall u \in V,\; \forall v \in V,\; \operatorname{pairEigenvalue}\left(G, \alpha, u, v\right) = (1 - \alpha) \cdot (\operatorname{SimpleGraph}.\operatorname{degree}\left(G, u\right) : \mathbb{R}) - (2 \cdot \alpha - 1) \cdot \operatorname{ite}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G, u, v\right), 1, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.pairEigenvalue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Garrett Kepler (2026). *Some Spectral Properties of the Bα Matrix of a Graph*. DOI: [10.48550/arXiv.2607.25221](https://doi.org/10.48550/arXiv.2607.25221). URL: <https://arxiv.org/abs/2607.25221v1>.

*Commentary.*

The degree is cast to the reals. The adjacency term is 1 precisely when the endpoints are adjacent.

**Definition 1.5 (The equivalence relation for the parameter).**

$$\forall V \in Type,\; \forall [\operatorname{Fintype}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall [\operatorname{DecidableRel}\left(G.\operatorname{Adj}\right)], \forall \alpha : \mathbb{R}, \begin{aligned}r = \operatorname{ite}\left(\alpha = \frac{1}{2}, \lambda u v. \operatorname{SimpleGraph}.\operatorname{degree}\left(G, u\right) = \operatorname{SimpleGraph}.\operatorname{degree}\left(G, v\right), \operatorname{Twins}\left(G\right)\right)\\h : \operatorname{Equivalence}\left(r\right)\\\operatorname{classSetoid}\left(G, \alpha\right) = \langle r, h\rangle\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.classSetoid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Garrett Kepler (2026). *Some Spectral Properties of the Bα Matrix of a Graph*. DOI: [10.48550/arXiv.2607.25221](https://doi.org/10.48550/arXiv.2607.25221). URL: <https://arxiv.org/abs/2607.25221v1>.

*Commentary.*

At half the equivalence proof uses reflexivity, symmetry and transitivity of equality of degrees. Away from half it uses the equivalence of outside-adjacency agreement.

**Definition 1.6 (The complete graph within each class).**

$$\forall V \in Type,\; \forall s \in \operatorname{Setoid}\left(V\right),\; \begin{aligned}a = \lambda u v. u \neq v \land s.\operatorname{r}\left(u, v\right)\\h : \operatorname{Std}.\operatorname{Symm}\left(a\right)\quad k : \operatorname{Std}.\operatorname{Irrefl}\left(a\right)\\\operatorname{classGraph}\left(s\right) = \langle a, h, k\rangle\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.classGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Garrett Kepler (2026). *Some Spectral Properties of the Bα Matrix of a Graph*. DOI: [10.48550/arXiv.2607.25221](https://doi.org/10.48550/arXiv.2607.25221). URL: <https://arxiv.org/abs/2607.25221v1>.

*Commentary.*

Symmetry reverses the inequality and applies symmetry of the setoid relation. A loop contradicts the inequality at its endpoint.

**Definition 1.7 (Vertices in a quotient class).**

$$\forall V \in Type,\; \forall s \in \operatorname{Setoid}\left(V\right),\; \forall C \in \operatorname{Quotient}\left(s\right),\; \operatorname{Class}\left(s, C\right) = \{v : V \mid \operatorname{Quotient}.\operatorname{mk}\left(s, v\right) = C\}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.Class` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Garrett Kepler (2026). *Some Spectral Properties of the Bα Matrix of a Graph*. DOI: [10.48550/arXiv.2607.25221](https://doi.org/10.48550/arXiv.2607.25221). URL: <https://arxiv.org/abs/2607.25221v1>.

*Commentary.*

A class is the fiber over its quotient element.

**Definition 1.8 (Sum of binomial class sizes).**

$$\forall V \in Type,\; \forall [\operatorname{Fintype}\left(V\right)], \forall s \in \operatorname{Setoid}\left(V\right),\; \operatorname{classPairSum}\left(s\right) = \sum_{C : \operatorname{Quotient}\left(s\right)} \operatorname{Nat}.\operatorname{choose}\left(\operatorname{Nat}.\operatorname{card}\left(\operatorname{Class}\left(s, C\right)\right), 2\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.classPairSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Garrett Kepler (2026). *Some Spectral Properties of the Bα Matrix of a Graph*. DOI: [10.48550/arXiv.2607.25221](https://doi.org/10.48550/arXiv.2607.25221). URL: <https://arxiv.org/abs/2607.25221v1>.

*Commentary.*

Each finite class contributes the number of its two-element subsets.

**Definition 1.9 (Signed eigenvector predicate).**

$$\forall V \in Type,\; \forall [\operatorname{Fintype}\left(V\right)], \forall [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall [\operatorname{DecidableRel}\left(G.\operatorname{Adj}\right)], \forall \alpha : \mathbb{R}, \forall x \in V \to \mathbb{R},\; \operatorname{IsSignedEigenvector}\left(G, \alpha, x\right) \Leftrightarrow ((\exists u \in V,\; \exists v \in V,\; u \neq v \land \left(x\left(u\right) = 1 \land \left(x\left(v\right) = -1 \land \left(\forall w \in V,\; (w \neq u) \Rightarrow \left((w \neq v) \Rightarrow x\left(w\right) = 0\right)\right)\right)\right)) \land (\exists l \in \mathbb{R},\; \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{bAlpha}\left(G, \alpha\right), x\right) = l \cdot x))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.IsSignedEigenvector` (`✓ std3`).

*Citation.* Garrett Kepler (2026). *Some Spectral Properties of the Bα Matrix of a Graph*. DOI: [10.48550/arXiv.2607.25221](https://doi.org/10.48550/arXiv.2607.25221). URL: <https://arxiv.org/abs/2607.25221v1>.

*Commentary.*

Remark 4.3 specifies one +1 entry, one −1 entry and zeros elsewhere. The eigen-equation for Bα uses a real eigenvalue.

**Definition 1.10 (Type of qualifying vectors).**

$$\forall V \in Type,\; \forall [\operatorname{Fintype}\left(V\right)], \forall [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall [\operatorname{DecidableRel}\left(G.\operatorname{Adj}\right)], \forall \alpha : \mathbb{R}, \operatorname{SignedEigenvectors}\left(G, \alpha\right) = \{x : V \to \mathbb{R} \mid \operatorname{IsSignedEigenvector}\left(G, \alpha, x\right)\}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.SignedEigenvectors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Garrett Kepler (2026). *Some Spectral Properties of the Bα Matrix of a Graph*. DOI: [10.48550/arXiv.2607.25221](https://doi.org/10.48550/arXiv.2607.25221). URL: <https://arxiv.org/abs/2607.25221v1>.

*Commentary.*

The subtype counts each signed vector once.

**Definition 1.11 (Unordered qualifying supports).**

$$\forall V \in Type,\; \forall [\operatorname{Fintype}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall [\operatorname{DecidableRel}\left(G.\operatorname{Adj}\right)], \forall \alpha : \mathbb{R}, \operatorname{SupportPairs}\left(G, \alpha\right) = \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(\operatorname{classGraph}\left(\operatorname{classSetoid}\left(G, \alpha\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.SupportPairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Garrett Kepler (2026). *Some Spectral Properties of the Bα Matrix of a Graph*. DOI: [10.48550/arXiv.2607.25221](https://doi.org/10.48550/arXiv.2607.25221). URL: <https://arxiv.org/abs/2607.25221v1>.

*Commentary.*

Edges of the class graph are Mathlib unordered pairs.

**Definition 1.12 (Realization of each oriented dart).**

$$\forall V \in Type,\; \forall [\operatorname{Fintype}\left(V\right)], \forall [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall [\operatorname{DecidableRel}\left(G.\operatorname{Adj}\right)], \forall \alpha : \mathbb{R}, \begin{aligned}D = \operatorname{SimpleGraph}.\operatorname{Dart}\left(\operatorname{classGraph}\left(\operatorname{classSetoid}\left(G, \alpha\right)\right)\right)\\S = \operatorname{SignedEigenvectors}\left(G, \alpha\right)\\p : \forall d \in D,\; \operatorname{IsSignedEigenvector}\left(G, \alpha, \operatorname{signedPair}\left(d.\operatorname{fst}, d.\operatorname{snd}\right)\right)\\(f : D \to S) = \lambda d : D. \langle \operatorname{signedPair}\left(d.\operatorname{fst}, d.\operatorname{snd}\right), p\left(d\right)\rangle\\h : \operatorname{Function}.\operatorname{Bijective}\left(f\right)\\(\operatorname{directedRealization}\left(G, \alpha\right) : D \equiv S) = \operatorname{Equiv}.\operatorname{ofBijective}\left(f, h\right)\\\forall x \in S,\; \operatorname{directedRealization}\left(G, \alpha\right).\operatorname{invFun}\left(x\right) = \operatorname{Classical}.\operatorname{choose}\left(h.\operatorname{surjective}\left(x\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.directedRealization` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Garrett Kepler (2026). *Some Spectral Properties of the Bα Matrix of a Graph*. DOI: [10.48550/arXiv.2607.25221](https://doi.org/10.48550/arXiv.2607.25221). URL: <https://arxiv.org/abs/2607.25221v1>.

*Commentary.*

The proof p(d) uses the dart's distinct endpoints for the signed coordinates and its class-graph edge for the eigen-equation. The +1 and −1 entries recover the ordered endpoints, so f is injective. For surjectivity, the signed coordinates and eigen-equation give an admissible dart with those endpoints. The inverse chooses a preimage using this surjectivity proof, and injectivity identifies it with that dart.

**Theorem 1.13 (Unordered supports and signed eigenvectors).**

$$\forall V \in Type,\; \forall [\operatorname{Fintype}\left(V\right)], \forall [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall [\operatorname{DecidableRel}\left(G.\operatorname{Adj}\right)], \forall \alpha : \mathbb{R}, \operatorname{Nat}.\operatorname{card}\left(\operatorname{SupportPairs}\left(G, \alpha\right)\right) = \operatorname{classPairSum}\left(\operatorname{classSetoid}\left(G, \alpha\right)\right) \land \operatorname{Nat}.\operatorname{card}\left(\operatorname{SignedEigenvectors}\left(G, \alpha\right)\right) = 2 \cdot \operatorname{classPairSum}\left(\operatorname{classSetoid}\left(G, \alpha\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.graphwise_count` (`✓ std3`). ∎

*Resolves.* `Problems/kepler-2026-remark-4-3-support-two-count` (proved) by `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.graphwise_count`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kepler-2026-remark-4-3-support-two-count","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.graphwise_count","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Garrett Kepler (2026). *Some Spectral Properties of the Bα Matrix of a Graph*. DOI: [10.48550/arXiv.2607.25221](https://doi.org/10.48550/arXiv.2607.25221). URL: <https://arxiv.org/abs/2607.25221v1>.

*Commentary.*

Remark 4.3, printed p. 8, asks “What Theorem 4.2 does not address is how many of these types of eigenvectors a given graph has.” The vector has exactly one +1, one −1 and zeros elsewhere.

The outside rows give (2α − 1) times the difference of the two adjacency entries. The inside rows give the eigenvalue (1 − α)d − (2α − 1)ε, where d is the common degree and ε indicates the edge within the pair. A class C contributes a pair for each two-element subset. The two oriented darts of each support realize the two opposite signed vectors. Empty and singleton carriers give zero in both counts.

The source resolution scope is the fixed-graph question in Remark 4.3 together with the Bα definition in Definition 1.5. The Lean result covers every finite simple undirected graph represented by a Mathlib SimpleGraph and every real α, so the source interval [0,1], α = 0, α = 1/2 and α = 1 are included.

The verified output ends with the exact unordered-support class sum and the exact factor-of-two signed-vector count. Theorems 4.1 and 4.2 supply source context. Their correction, the labeled-graph enumeration, union bound, limiting proportion and half-parameter all-graphs statement lie outside this result.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.Class`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.IsSignedEigenvector`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.SignedEigenvectors`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.SupportPairs`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.Twins`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.bAlpha`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.classGraph`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.classPairSum`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.classSetoid`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.directedRealization`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.graphwise_count`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.pairEigenvalue`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.signedPair`
