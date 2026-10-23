# The token-graph cut bound fails on a five-cycle blow-up

## Abstract

A phase product on the 100-token graph of the five-cycle blow-up with block size 40 has Rayleigh quotient below the cut and matching bound of Apte, Parekh and Sud.

**Definition 1.1 (An unordered edge crossing a cut).**

$$\forall (n: \mathbb{N}), \forall (S: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), \forall (e: \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)), (\operatorname{crosses}\left(S, e\right)) \Leftrightarrow (\operatorname{Sym2}.\operatorname{lift}\left(\langle fun (u: \operatorname{Fin}\left(n\right)) \mapsto fun (v: \operatorname{Fin}\left(n\right)) \mapsto (u \in S) \ne (v \in S)\rangle, e\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.crosses` (`✓ std3`).

*Citation.* Anuj Apte; Ojas Parekh; James Sud (2025). *Conjectured Bounds for 2-Local Hamiltonians via Token Graphs*. URL: <https://arxiv.org/abs/2506.03441v2>.

*Commentary.*

Page 8: "Let δ(S) be the set of edges in G that cross from S to V ∖ S, and Cut(S) be the sum of the weights of the edges δ(S)." Exactly one endpoint belongs to S. Sym2.lift descends the displayed symmetric endpoint predicate to unordered pairs; its proof of symmetry is implicit.

**Definition 1.2 (The maximum cut).**

$$\forall (n: \mathbb{N}), \forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)], \operatorname{maxCut}\left(G\right) = \operatorname{Finset}.\operatorname{sup}\left((\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right)), fun (S: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(fun (e: \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto \operatorname{crosses}\left(S, e\right), \operatorname{SimpleGraph}.\operatorname{edgeFinset}\left(G\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.maxCut` (`✓ std3`).

*Citation.* Anuj Apte; Ojas Parekh; James Sud (2025). *Conjectured Bounds for 2-Local Hamiltonians via Token Graphs*. URL: <https://arxiv.org/abs/2506.03441v2>.

*Commentary.*

Page 8: "We denote the maximum of Cut(S) over all S by C(G), i.e., C(G) is the solution to the Maximum Cut (MaxCut) problem on G." Every edge has weight one, so the weight of a cut is the cardinality of the filtered unordered edge set. Finset.sup over all finite subsets gives the maximum, including the empty cut.

**Definition 1.3 (The size-restricted maximum matching).**

$$\forall (n: \mathbb{N}), \forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)], \forall (k: \mathbb{N}), \operatorname{maxMatchingLe}\left(G, k\right) = \operatorname{Finset}.\operatorname{sup}\left(\operatorname{Finset}.\operatorname{filter}\left(fun (M: \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)\right)) \mapsto (\operatorname{Finset}.\operatorname{card}\left(M\right) \le k) \land (\operatorname{Set}.\operatorname{Pairwise}\left((M: \operatorname{Set}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)\right)), fun (e: \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto fun (f: \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto \operatorname{Disjoint}\left((e: \operatorname{Set}\left(\operatorname{Fin}\left(n\right)\right)), (f: \operatorname{Set}\left(\operatorname{Fin}\left(n\right)\right))\right)\right)), \operatorname{Finset}.\operatorname{powerset}\left(\operatorname{SimpleGraph}.\operatorname{edgeFinset}\left(G\right)\right)\right), fun (M: \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)\right)) \mapsto \operatorname{Finset}.\operatorname{card}\left(M\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.maxMatchingLe` (`✓ std3`).

*Citation.* Anuj Apte; Ojas Parekh; James Sud (2025). *Conjectured Bounds for 2-Local Hamiltonians via Token Graphs*. URL: <https://arxiv.org/abs/2506.03441v2>.

*Commentary.*

Page 8: "Let M_k(G) denote the maximum weight matching under the restriction that |M| ≤ k." For unit weights, weight is cardinality. The powerset ranges over edge subsets; Pairwise requires disjoint endpoint sets for distinct edges, and the cardinality is at most k. The coercion from an unordered edge to its endpoint set and that from a finite edge family to a set are shown explicitly.

**Definition 1.4 (The least real adjacency eigenvalue).**

$$\forall (iota: Type), [\operatorname{Fintype}\left(iota\right)], [\operatorname{DecidableEq}\left(iota\right)], \forall (A: \operatorname{Matrix}\left(iota, iota, \mathbb{R}\right)), \operatorname{lambdaMin}\left(A\right) = if hA: \operatorname{Matrix}.\operatorname{IsHermitian}\left(A\right) then (if h: \operatorname{Finset}.\operatorname{Nonempty}\left((\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(iota\right))\right) then \operatorname{Finset}.\operatorname{inf}'\left((\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(iota\right)), h, hA.eigenvalues\right) else 0) else 0$$

*Formalization.* `D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.lambdaMin` (`✓ std3`).

*Citation.* Anuj Apte; Ojas Parekh; James Sud (2025). *Conjectured Bounds for 2-Local Hamiltonians via Token Graphs*. URL: <https://arxiv.org/abs/2506.03441v2>.

*Commentary.*

Page 9: "Let λ_max(·), λ_min(·), and eigs(·) describe the maximum eigenvalue, minimum eigenvalue, and the set of unique eigenvalues of a matrix." The adjacency matrix is real and Hermitian. The nonempty branch uses Finset.inf' on Matrix.IsHermitian.eigenvalues, the real eigenvalues with multiplicity. Its dependent proof arguments hA and h appear explicitly. The empty-carrier and non-Hermitian extensions are zero; neither extension is used in the counterexample.

**Definition 1.5 (Conjecture 7).**

$$(claim) \Leftrightarrow (\forall (n: \mathbb{N}), \forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)], \forall (k: \mathbb{N}), (1 \le k) \Rightarrow ((k \le \operatorname{Nat}.\operatorname{div}\left(n, 2\right)) \Rightarrow (-\frac{(\operatorname{maxCut}\left(G\right): \mathbb{R}) + (\operatorname{maxMatchingLe}\left(G, k\right): \mathbb{R})}{2} \le \operatorname{lambdaMin}\left(\operatorname{SimpleGraph}.\operatorname{adjMatrix}\left(\mathbb{R}, \operatorname{tokenGraph}\left(G, k\right)\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.claim` (`✓ std3`).

*Citation.* Anuj Apte; Ojas Parekh; James Sud (2025). *Conjectured Bounds for 2-Local Hamiltonians via Token Graphs*. URL: <https://arxiv.org/abs/2506.03441v2>.

*Commentary.*

Appendix D.2, page 39: "In contrast, the following bound was shown to hold on our dataset"; "Conjecture 7. For all G and for all 1 ≤ k ≤ ⌊n/2⌋" followed by "λ_min(A(F_k(G))) ≥ −(C(G)+M_k(G))/2." The formula quantifies all finite simple graphs with decidable adjacency, with unit edge weights. This is a specialization of the source's all-graphs assertion. Fin n labels the n vertices; Nat.div n 2 is floor(n/2). The tokenGraph is the existing finite-subset graph: two equally sized subsets differ by one token moved along an edge. The natural cut and matching cardinalities are coerced to real numbers before division by two. No connectedness or bipartiteness hypothesis is imposed.

**Theorem 1.6 (A phase test contradicts the bound).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/apte-parekh-sud-2025-token-graph-cut-bound` (refuted) by `D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"apte-parekh-sud-2025-token-graph-cut-bound","declaration_gid":"D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Anuj Apte; Ojas Parekh; James Sud (2025). *Conjectured Bounds for 2-Local Hamiltonians via Token Graphs*. URL: <https://arxiv.org/abs/2506.03441v2>.

*Commentary.*

Take the five-cycle blow-up with five independent blocks of size 40 and complete bipartite edges between successive blocks. Its 100-token graph uses the existing tokenGraph. Put z = (−4+3i)/5 and multiply z to the block index over the occupied vertices. Each phase has modulus one. Each oriented edge of the original graph occurs as a token move in choose(198,99) token subsets, so the energy reduces to a sum over the original graph. The squared norm is choose(200,100), and the ratio of these binomial coefficients is 50/199. The real part of the edge-phase sum is 2·40²·(4 Re z + Re z⁴), with 4 Re z + Re z⁴ = −2527/625. The quotient is −646912/199. Splitting the complex phase vector into its real and imaginary parts connects this quotient to the least eigenvalue of the real adjacency matrix. The cut weight is affine in each block occupancy; rounding each occupancy to zero or 40 gives at most four cut cycle edges, hence maximum cut at most 6400. The matching weight is at most 100. The conjectured lower bound is therefore at least −3250, whereas the least eigenvalue is at most −646912/199, smaller by 162/199.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.crosses`
- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.lambdaMin`
- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.maxCut`
- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.maxMatchingLe`
- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.result`
- Dependency: [D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation](../TokenGraphLaplacianRadiusRefutation.md)
