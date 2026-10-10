# BraunsteinGhoshSeveriniStarRefutation

## Abstract

Refutation of the Braunstein–Ghosh–Severini star maximum conjecture.

Scalar quotients are real unless a complex cast is displayed. Fin indices are zero based. Matrix, rankOneDensity, partialTraceRight and partialTransposeB denote the actual Lean operations. All entropy values are in bits.

**Definition 1.1 (degreeSum).**

$$\forall (p:\mathbb N), \forall (q:\mathbb N), \forall (G:\operatorname{SimpleGraph}\left((\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right))\right)), \operatorname{degreeSum}\left(G\right)=\sum_{v\in (\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right))} (G.\operatorname{degree}(v))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.degreeSum` (`✓ std3`).

*Citation.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Page 2 defines dG = ∑ᵢ₌₁ⁿ dG(vi). The sum is over Fin p × Fin q.

**Definition 1.2 (sigma).**

$$\forall (p:\mathbb N), \forall (q:\mathbb N), \forall (G:\operatorname{SimpleGraph}\left((\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right))\right)), \operatorname{sigma}\left(G\right)=(\frac{1}{\operatorname{degreeSum}\left(G\right):\mathbb R}:\mathbb C)\cdot G.\operatorname{lapMatrix}(\mathbb C)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.sigma` (`✓ std3`).

*Citation.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Definition 2.2, p. 3: “The density matrix of a graph G is the matrix” σ(G) = (1/dG)L(G). The source expression is the complex SimpleGraph.lapMatrix divided by degreeSum. A nonempty edge set ensures a positive denominator.

**Definition 1.3 (root).**

$$\forall (p:\mathbb N), \forall (q:\mathbb N), \forall (x:(\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right))), \operatorname{root}\left(x\right)\iff (\operatorname{val}\left(x.1\right)=0)\land (\operatorname{val}\left(x.2\right)=0)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.root` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

The source labels i = sq + s′. Its vertex v₁ is zero-based (0,0).

**Definition 1.4 (starGraph).**

$$\forall (p:\mathbb N), \forall (q:\mathbb N), \operatorname{starGraph}\left(p, q\right)=\begin{cases}\operatorname{SimpleGraph}.\operatorname{starGraph}((\langle0,h.1\rangle,\langle0,h.2\rangle))&\operatorname{if} h:(0<p)\land (0<q)\\\operatorname{Bot}.\operatorname{bot}&\operatorname{otherwise}\end{cases}$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.starGraph` (`✓ std3`).

*Citation.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

The source star K₁,ₙ₋₁ is rooted at v₁. The positive dimensions use Mathlib SimpleGraph.starGraph directly at the two Fin zero coordinates. The total extension is the empty graph when a dimension is zero; the conjecture domain excludes those cases because the edge set must be nonempty.

**Definition 1.5 (center).**

$$\forall (k:\mathbb N), \forall (x:(\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(2\cdot k\right))), \operatorname{center}\left(x\right)\iff (\operatorname{val}\left(x.1\right)=0)\land (\operatorname{Nat}.\operatorname{mod}(\operatorname{val}\left(x.2\right),2)=0)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.center` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

A block center has first coordinate zero and an even second coordinate. Nat.mod is natural-number remainder.

**Definition 1.6 (Gk).**

$$\forall (k:\mathbb N), \forall (x:(\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(2\cdot k\right))), \forall (y:(\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(2\cdot k\right))), \operatorname{Gk}\left(k\right).\operatorname{Adj}(x,y)\iff (x\neq y)\land (((\operatorname{Nat}.\operatorname{div}(\operatorname{val}\left(x.2\right),2)=\operatorname{Nat}.\operatorname{div}(\operatorname{val}\left(y.2\right),2))\land (\operatorname{center}\left(x\right)\lor \operatorname{center}\left(y\right)))\lor ((\operatorname{center}\left(x\right))\land (\operatorname{center}\left(y\right))\land (\operatorname{root}\left(x\right)\lor \operatorname{root}\left(y\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.Gk` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Each four-vertex block is a star. Block centers are joined to the global root. Nat.div means natural-number integer division; the displayed divisions are not real fractions.

**Definition 1.7 (claim).**

$$\operatorname{claim}\iff \forall (p:\mathbb N), \forall (q:\mathbb N), \forall (G:\operatorname{SimpleGraph}\left((\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right))\right)), ((G.\operatorname{Connected})\land (G.\operatorname{edgeSet}.\operatorname{Nonempty}))\longrightarrow E_F(\operatorname{sigma}\left(G\right))\le E_F(\operatorname{sigma}\left(\operatorname{starGraph}\left(p, q\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.claim` (`✓ std3`).

*Citation.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Conjecture 6.7, p. 18, verbatim: “Let 𝒢⁽ᶜ⁾ₙ be the set of all connected graphs on n vertices. Let G ∈ 𝒢⁽ᶜ⁾ₙ (|V| = pq). Then max𝒢⁽ᶜ⁾ₙ EF(σ(G)) = EF(σ(K₁,ₙ₋₁)).” Encoding: every p,q and connected simple graph on Fin p × Fin q with nonempty edge set. The maximum assertion means that every such graph has formation at most the rooted star.

**Theorem 1.8 (family).**

$$\forall (k:\mathbb N), (32\le k)\longrightarrow (\frac{499751}{16646144}<E_F(\operatorname{sigma}\left(\operatorname{Gk}\left(k\right)\right)))\land (E_F(\operatorname{sigma}\left(\operatorname{starGraph}\left(2, 2\cdot k\right)\right))<\frac{89}{3175})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

For every k ≥ 32 the family density has a strict lower bound exceeding the strict star upper bound. The difference between the rational bounds is positive.

**Theorem 1.9 (result).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/braunstein-ghosh-severini-2006-star-formation-maximum` (refuted) by `D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"braunstein-ghosh-severini-2006-star-formation-maximum","declaration_gid":"D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Refutation of BGS Conjecture 6.7: the instance k = 32 has 128 vertices with tensor dimensions 2 × 64. The graph is connected and has nonempty edge set, and its formation exceeds the rooted star.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.Gk`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.center`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.degreeSum`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.family`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.root`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.sigma`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.starGraph`
- Dependency: [D5/S3/Quantum/Entanglement/GraphDensity/SelectiveFormationBounds](SelectiveFormationBounds.md)
- Dependency: [D5/S3/Weil/Probability/FiniteGaussianSchoenberg](../../../Weil/Probability/FiniteGaussianSchoenberg.md)
