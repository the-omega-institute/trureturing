# A disconnected counterexample to the token-radius conjecture

## Abstract

The graph consisting of one edge and two isolated vertices has Laplacian spectral radius 2, as does its two-token graph, but it is not a star. This refutes the all-graphs statement of Conjecture 1.1 of Song, Dalfo, Fiol and Zhang.

**Definition 1.1 (Moving one token).**

$$\forall (V : Type), [\operatorname{DecidableEq}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (k : \mathbb{N}), \forall (s : Set.powersetCard\left(V, k\right)), \forall (t : Set.powersetCard\left(V, k\right)), (\operatorname{Adj}\left(\operatorname{tokenGraph}\left(G, k\right), s, t\right)) \Leftrightarrow (\exists (u : V) (v : V), (\operatorname{val}\left(s\right) \setminus \operatorname{val}\left(t\right) = \{u\}) \land ((\operatorname{val}\left(t\right) \setminus \operatorname{val}\left(s\right) = \{v\}) \land (\operatorname{Adj}\left(G, u, v\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.tokenGraph` (`✓ std3`).

*Citation.* X. Song and C. Dalfó and M. À. Fiol and S. Zhang (2026). *The Algebraic Connectivity and Laplacian Spectral Radius of Token Graphs*. DOI: [10.48550/arXiv.2610.00500](https://doi.org/10.48550/arXiv.2610.00500). URL: <https://arxiv.org/abs/2610.00500v1>.

*Commentary.*

The token vertices are Mathlib's Set.powersetCard V k, the finite subsets of cardinality k, with val denoting the underlying finite subset. The carrier is defined for every k; claim restricts k to the source's range. The Abstract's adjacency sentence is encoded by the two set differences. For equal-cardinality subsets, a symmetric difference equal to an edge {u,v} has one endpoint in each difference: the differences are disjoint, and equal cardinalities force their sizes to agree. Conversely, the displayed singleton differences give symmetric difference {u,v}; G.Adj u v ensures distinct endpoints. Thus this adjacency is exactly the source's adjacency. Symmetry follows by exchanging u and v, and a subset cannot be adjacent to itself.

**Definition 1.2 (Decidable token adjacency).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \forall (k : \mathbb{N}), \operatorname{DecidableRel}\left(\operatorname{Adj}\left(\operatorname{tokenGraph}\left(G, k\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.instTokenGraphDecidableAdj` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On a finite carrier with decidable equality and graph adjacency, finite search over u and v decides the displayed adjacency predicate. This instance uses the existing finite-subset and subtype instances.

**Definition 1.3 (The Laplacian spectral radius).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \operatorname{rho}\left(G\right) = \left\{\begin{aligned}\operatorname{supPrime}\left(\operatorname{univ}\left(V\right), \operatorname{eigenvalues}\left(\operatorname{isHermitian_{lapMatrix}}\left(\mathbb{R}, G\right)\right)\right) & \text{if} \operatorname{Nonempty}\left(\operatorname{univ}\left(V\right)\right)\\0 & \text{otherwise}\end{aligned}\right.$$

*Formalization.* `D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.rho` (`✓ std3`).

*Citation.* X. Song and C. Dalfó and M. À. Fiol and S. Zhang (2026). *The Algebraic Connectivity and Laplacian Spectral Radius of Token Graphs*. DOI: [10.48550/arXiv.2610.00500](https://doi.org/10.48550/arXiv.2610.00500). URL: <https://arxiv.org/abs/2610.00500v1>.

*Commentary.*

Section 2, page 5: "Let L = L(G) = D(G) − A(G) be the Laplacian matrix of G." It states: "the spectral radius of L is ρ(L) = λ_n. We denote ρ(G) = ρ(L) as the Laplacian spectral radius of G." Here lapMatrix is Mathlib's degree matrix minus adjacency matrix. The indexed operator is SimpleGraph.isHermitian_lapMatrix, the canonical Hermitian proof object for this Laplacian. Its eigenvalues are real because it is Hermitian, and nonnegative because the graph Laplacian is positive semidefinite (SimpleGraph.posSemidef_lapMatrix). Therefore their maximum is also the maximum absolute eigenvalue, the source's spectral radius. supPrime denotes Finset.sup' over all eigenvalue indices, with its proof argument implicit and supplied in the nonempty branch; the empty carrier has radius zero.

**Definition 1.4 (Conjecture 1.1).**

$$(claim) \Leftrightarrow (\forall (n : \mathbb{N}), (4 \le n) \Rightarrow (\forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], (\forall (k : \mathbb{N}), (2 \le k) \Rightarrow ((k \le \operatorname{div}\left(n, 2\right)) \Rightarrow (\operatorname{rho}\left(\operatorname{tokenGraph}\left(G, k\right)\right) = \operatorname{rho}\left(G\right)))) \Leftrightarrow (\operatorname{Nonempty}\left(\operatorname{Iso}\left(G, \operatorname{starGraph}\left(\langle0\rangle : \operatorname{Fin}\left(n\right)\right)\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.claim` (`✓ std3`).

*Citation.* X. Song and C. Dalfó and M. À. Fiol and S. Zhang (2026). *The Algebraic Connectivity and Laplacian Spectral Radius of Token Graphs*. DOI: [10.48550/arXiv.2610.00500](https://doi.org/10.48550/arXiv.2610.00500). URL: <https://arxiv.org/abs/2610.00500v1>.

*Commentary.*

Section 1, page 4: "Conjecture 1.1. Let G be a graph of order n(≥ 4), the equality ρ(F_k(G)) = ρ(G) holds for all k with 2 ≤ k ≤ ⌊n/2⌋ if and only if G ≅ S_n." The quantified graph is finite and simple, with vertices Fin n, labelled 0 through n−1. No connectedness hypothesis is imposed in this sentence. S_n is K_{1,n−1}, represented directly by Mathlib's starGraph centered at the Fin n vertex of value zero. Iso is Mathlib's SimpleGraph.Iso; Nonempty of this graph-isomorphism type expresses existence of an isomorphism. div means natural-number division, so div(n,2) is ⌊n/2⌋. Proof arguments establishing that vertex zero exists are implicit in the formula.

**Theorem 1.5 (One edge and two isolated vertices).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/song-dalfo-fiol-zhang-2026-token-graph-laplacian-radius-refutation` (refuted) by `D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"song-dalfo-fiol-zhang-2026-token-graph-laplacian-radius-refutation","declaration_gid":"D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* X. Song and C. Dalfó and M. À. Fiol and S. Zhang (2026). *The Algebraic Connectivity and Laplacian Spectral Radius of Token Graphs*. DOI: [10.48550/arXiv.2610.00500](https://doi.org/10.48550/arXiv.2610.00500). URL: <https://arxiv.org/abs/2610.00500v1>.

*Commentary.*

Take the graph on Fin 4 whose only edge is {0,1}. Its two-token graph has edges {0,2}–{1,2} and {0,3}–{1,3}, with {0,1} and {2,3} isolated. Both nonzero Laplacians satisfy L² = 2L. Applied to an eigenvector, this identity gives λ² = 2λ, so every eigenvalue is zero or two; if all were zero, the Hermitian matrix itself would be zero. Hence both radii are two. For n = 4, the only integer k in the conjecture's range is two. The original graph has one edge, while the star on four vertices has three; isomorphisms preserve this edge count. Thus the left side of the asserted equivalence holds and its right side fails. This result addresses the literal all-graphs statement; the version restricted to connected graphs remains open.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.instTokenGraphDecidableAdj`
- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.rho`
- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.tokenGraph`
