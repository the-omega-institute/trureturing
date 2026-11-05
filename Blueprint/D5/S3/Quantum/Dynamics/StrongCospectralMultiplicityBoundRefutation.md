# Strong cospectrality does not satisfy the general multiplicity bound

## Abstract

The connected graph K_{2,3} has two pairwise strongly cospectral vertices and an adjacency eigenspace of dimension at least three, contradicting the proposed multiplicity bound.

**Definition 1.1 (Strong cospectrality for adjacency).**

$$\forall (n: \mathbb{N}), (\forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(G\right)\right)], (\forall (u: \operatorname{Fin}\left(n\right)), (\forall (v: \operatorname{Fin}\left(n\right)), ((\operatorname{D5.S3.Quantum.Dynamics.StrongCospectralMultiplicityBoundRefutation.StronglyCospectral}\left(G, u, v\right)) \Leftrightarrow (\forall (\theta: \mathbb{R}), (\exists (c: \mathbb{R}), ((\left|c\right| = (1: \mathbb{R})) \land (\operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum.idempotent}\left(G, \theta\right), \operatorname{Pi.single}\left(u, (1: \mathbb{R})\right)\right) = (c) \cdot (\operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum.idempotent}\left(G, \theta\right), \operatorname{Pi.single}\left(v, (1: \mathbb{R})\right)\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.StronglyCospectral` (`✓ std3`).

*Citation.* Hermie Monterde (2022). *Strong cospectrality and twin vertices in weighted graphs*. DOI: [10.13001/ela.2022.6721](https://doi.org/10.13001/ela.2022.6721). URL: <https://arxiv.org/abs/2111.01265v2>.

*Commentary.*

For a simple graph G on Fin n with decidable adjacency, idempotent G θ is the real orthogonal projection onto the θ-eigenspace of its adjacency matrix. The vertices u and v are strongly cospectral when their projected coordinate vectors differ, at each real θ, by a real scalar c of absolute value one. This is the real symmetric case of the source's definition in arXiv v2 TeX, lines 170–192. The coordinate vector at u is Pi.single u 1. For a real number outside the spectrum the projection is zero, so quantifying over all real θ adds no restriction. The definition permits u and v to be equal.

**Definition 1.2 (The largest adjacency eigenvalue multiplicity).**

$$\forall (n: \mathbb{N}), (\forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(G\right)\right)], ((\operatorname{D5.S3.Quantum.Dynamics.StrongCospectralMultiplicityBoundRefutation.maxMultiplicity}\left(G\right): \mathbb{N}) = \operatorname{sSup}\left(\operatorname{Set.range}\left(\lambda (\theta: \mathbb{R}) \mapsto (\operatorname{Module.finrank}\left(\mathbb{R}, \operatorname{Subtype}\left(\lambda (x: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})) \mapsto (x \in \operatorname{Module.End.eigenspace}\left(\operatorname{Matrix.mulVecLin}\left(\operatorname{SimpleGraph.adjMatrix}\left(\mathbb{R}, G\right)\right), \theta\right))\right)\right))\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.maxMultiplicity` (`✓ std3`).

*Citation.* Hermie Monterde (2022). *Strong cospectrality and twin vertices in weighted graphs*. DOI: [10.13001/ela.2022.6721](https://doi.org/10.13001/ela.2022.6721). URL: <https://arxiv.org/abs/2111.01265v2>.

*Commentary.*

Take the natural-valued supremum of the real dimensions of the adjacency eigenspaces, over all real θ. Every such dimension is at most n, and a number outside the spectrum contributes zero. For a nonempty vertex set this is the largest eigenvalue multiplicity used in arXiv v2 TeX, line 727; the definition also gives zero for the empty graph. Matrix.mulVecLin is the linear map induced by the real adjacency matrix. Its eigenspace is viewed as the subtype of real coordinate vectors that belong to it.

**Definition 1.3 (The extension to connected simple graphs).**

$$(\operatorname{D5.S3.Quantum.Dynamics.StrongCospectralMultiplicityBoundRefutation.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), (\forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(G\right)\right)], ((\operatorname{SimpleGraph.Connected}\left(G\right)) \to (\forall (S: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((\forall (u: \operatorname{Fin}\left(n\right)), ((u \in S) \to (\forall (v: \operatorname{Fin}\left(n\right)), ((v \in S) \to (\operatorname{D5.S3.Quantum.Dynamics.StrongCospectralMultiplicityBoundRefutation.StronglyCospectral}\left(G, u, v\right)))))) \to ((\operatorname{Nat.cast}\left(\operatorname{Finset.card}\left(S\right)\right): \mathbb{R}) \le \frac{(\operatorname{Nat.cast}\left(n\right): \mathbb{R})}{(\operatorname{Nat.cast}\left(\operatorname{D5.S3.Quantum.Dynamics.StrongCospectralMultiplicityBoundRefutation.maxMultiplicity}\left(G\right)\right): \mathbb{R})})))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hermie Monterde (2022). *Strong cospectrality and twin vertices in weighted graphs*. DOI: [10.13001/ela.2022.6721](https://doi.org/10.13001/ela.2022.6721). URL: <https://arxiv.org/abs/2111.01265v2>.

*Commentary.*

In arXiv v2 TeX, line 727, Monterde recalls the bound for normal Cayley graphs and asks whether it extends to other graph classes and generalized adjacency matrices. Here the assertion is that every connected simple graph G on n vertices and every finite set S of pairwise adjacency strongly cospectral vertices satisfy |S| ≤ n/maxMultiplicity G. Ordinary adjacency is the case α = β = 0 and γ = 1 of the generalized adjacency matrix in lines 143–150 and 161. Pairwise strong cospectrality includes equal vertices. The cardinality of S, n and maxMultiplicity G are each cast from the natural numbers to the reals before comparison and division.

**Theorem 1.4 (A counterexample on five vertices).**

$$\neg (\operatorname{D5.S3.Quantum.Dynamics.StrongCospectralMultiplicityBoundRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/monterde-2022-strong-cospectral-multiplicity-bound-refutation` (refuted) by `D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"monterde-2022-strong-cospectral-multiplicity-bound-refutation","declaration_gid":"D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Hermie Monterde (2022). *Strong cospectrality and twin vertices in weighted graphs*. DOI: [10.13001/ela.2022.6721](https://doi.org/10.13001/ela.2022.6721). URL: <https://arxiv.org/abs/2111.01265v2>.

*Commentary.*

Let G = K_{2,3} have parts {0,1} and {2,3,4}, and write A for its real adjacency matrix. The real linear map f sends x = (x₀,x₁,x₂) to (x₀,−x₀,x₁+x₂,−x₁,−x₂). The sum of the coordinates on each part is zero, so A f(x) = 0. Coordinates 1, 3 and 4 recover −x₀, −x₁ and −x₂, making f injective into the zero eigenspace. That eigenspace therefore has dimension at least three. Every eigenspace has dimension at most five, so the defining supremum is bounded and m = maxMultiplicity G is at least three.

Set Q = A²/3 − I and let e₀ and e₁ be the coordinate vectors at 0 and 1. Direct multiplication gives Q e₀ = e₁ and A³ = 6A. If A v = θv for a nonzero real vector v, the cubic identity gives θ(θ²−6) = 0, hence θ = 0 or θ² = 6. For every vector with A v = θv, evaluation of the quadratic expression gives Q v = (θ²/3−1)v.

Write c = θ²/3−1. The matrix Q is symmetric. For an orthonormal adjacency eigenbasis vector w of eigenvalue θ, taking the inner product of w with Q e₀ = e₁ and moving Q to w gives w₁ = c w₀. The projection Eθ is the sum of w wᵀ over the basis vectors with eigenvalue θ. The coordinate identity thus yields Eθ e₁ = c Eθ e₀.

When θ occurs in the eigenbasis, its basis vector is nonzero, so θ = 0 or θ² = 6. Accordingly c is −1 or 1, has absolute value one and satisfies c² = 1. Substituting Eθ e₁ = c Eθ e₀ then gives Eθ e₀ = c Eθ e₁, the required orientation of strong cospectrality. When θ does not occur, Eθ is an empty sum and is zero; the scalar 1 suffices. For each equal pair in S = {0,1}, use the scalar 1. For the pair (0,1), use the relation just proved. For the reversed pair, a real scalar of absolute value one has square one, so the same scalar reverses the relation. Thus every ordered pair in S is strongly cospectral.

Both parts of G are nonempty, so G is connected. Apply the asserted bound with n = 5 and S = {0,1}, whose cardinality is two. It gives 2 ≤ 5/m. Since m ≥ 3, its real cast is positive; multiplying by it gives 2m ≤ 5, while m ≥ 3 gives 2m ≥ 6. This contradiction refutes the asserted extension.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.StronglyCospectral`
- Truth anchor: `D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.maxMultiplicity`
- Truth anchor: `D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.result`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation](../../Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.md)
- Dependency: [D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum](AverageMixingTraceMaximum.md)
