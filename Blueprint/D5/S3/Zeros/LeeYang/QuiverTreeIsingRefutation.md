# A tree Ising polynomial with an off-circle root

## Abstract

Positive joint split weights refute the tree Lee-Yang conjecture.

**Definition 1.1 (The positive edge splits).**

$$\forall (E:\operatorname{Type})[\operatorname{Fintype}\left(E\right)][\operatorname{DecidableEq}\left(E\right)](n:E \to \operatorname{Nat}),\operatorname{splits}\left(n\right) = \operatorname{Fintype}.\operatorname{piFinset}(\operatorname{fun} (i:E)\mapsto \operatorname{Finset}.\operatorname{Icc}(1,\operatorname{Nat}.\operatorname{sub}(\operatorname{n}\left(i\right),1)))$$

*Formalization.* `D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.splits` (`✓ std3`).

*Citation.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Section 2.2, printed p. 13 (PDF p. 14): “Assign a positive integer nᵢ to each of the e edges of the tree graph.” “For every edge, split nᵢ into two positive integers, nᵢ=kᵢ+(nᵢ−kᵢ) and assign each of these two integers to one of the vertices at the ends of that edge.” Fintype.piFinset gives exactly the configuration functions in the product of Finset.Icc 1 (n i − 1). Nat.sub is natural-number subtraction, truncated at zero.

**Definition 1.2 (Vertex masses).**

$$\forall (V:\operatorname{Type})(E:\operatorname{Type})[\operatorname{Fintype}\left(V\right)][\operatorname{DecidableEq}\left(V\right)][\operatorname{Fintype}\left(E\right)][\operatorname{DecidableEq}\left(E\right)](src:E \to V)(tgt:E \to V)(n:E \to \operatorname{Nat})(k:E \to \operatorname{Nat})(v:V),\operatorname{mass}\left(src, tgt, n, k, v\right) = (\sum_{i \in (\operatorname{Finset}.\operatorname{univ}:\operatorname{Finset}\left(E\right)).\operatorname{filter}(\operatorname{fun} (i:E)\mapsto \operatorname{src}\left(i\right) = v)}\operatorname{k}\left(i\right))+(\sum_{i \in (\operatorname{Finset}.\operatorname{univ}:\operatorname{Finset}\left(E\right)).\operatorname{filter}(\operatorname{fun} (i:E)\mapsto \operatorname{tgt}\left(i\right) = v)}\operatorname{Nat}.\operatorname{sub}(\operatorname{n}\left(i\right),\operatorname{k}\left(i\right)))$$

*Formalization.* `D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.mass` (`✓ std3`).

*Citation.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Section 2.2, printed p. 13 (PDF p. 14): “Then, if a vertex has degree dⱼ this procedure assigns to that vertex dⱼ integers. Let mⱼ be the sum of these integers at a given vertex; the magnetic field at that vertex is then mⱼ H.” The source endpoint receives k i and the target endpoint receives n i − k i. The formula displays both filtered finite sums; subtraction is Nat.sub.

**Definition 1.3 (The weighted tree Ising polynomial).**

$$\forall (V:\operatorname{Type})(E:\operatorname{Type})[\operatorname{Fintype}\left(V\right)][\operatorname{DecidableEq}\left(V\right)][\operatorname{Fintype}\left(E\right)][\operatorname{DecidableEq}\left(E\right)](src:E \to V)(tgt:E \to V)(n:E \to \operatorname{Nat})(rho:(E \to \operatorname{Nat}) \to \operatorname{Real})(tau:\operatorname{Real}),\operatorname{treePoly}\left(src, tgt, n, rho, tau\right) = \sum_{k \in \operatorname{splits}\left(n\right)}\operatorname{Polynomial}.\operatorname{C}(\operatorname{rho}\left(k\right))\cdot (\sum_{st:V \to \operatorname{Bool}}\operatorname{Polynomial}.\operatorname{C}(tau^{((\operatorname{Finset}.\operatorname{univ}:\operatorname{Finset}\left(E\right)).\operatorname{filter}(\operatorname{fun} (i:E)\mapsto st(\operatorname{src}\left(i\right)) \ne st(\operatorname{tgt}\left(i\right)))).\operatorname{card}})\cdot \operatorname{Polynomial}.\operatorname{X}^{\sum_{v \in (\operatorname{Finset}.\operatorname{univ}:\operatorname{Finset}\left(V\right)).\operatorname{filter}(\operatorname{fun} (v:V)\mapsto \operatorname{st}\left(v\right) = \operatorname{true})}\operatorname{mass}\left(src, tgt, n, k, v\right)})$$

*Formalization.* `D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.treePoly` (`✓ std3`).

*Citation.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Section 2.2, printed p. 13 (PDF p. 14), equation (2.30), defines P by summing over all splits and all spin states, with factors ρ(kᵢ,nᵢ), τ raised to the number of opposite-spin edges, and x raised to the sum of spin-up vertex masses. The source says: “where ρ(kᵢ,nᵢ) is a distribution that weights different configurations.” The coefficient type is ℝ; Polynomial.C embeds coefficients and Polynomial.X is the indeterminate. Spins have type V → Bool, and true means spin up. The weight rho depends jointly on the whole split.

**Definition 1.4 (Conjecture 1 with its binding conventions).**

$$\operatorname{claim} = (\forall (V:\operatorname{Type})(E:\operatorname{Type})[\operatorname{Fintype}\left(V\right)][\operatorname{DecidableEq}\left(V\right)][\operatorname{Fintype}\left(E\right)][\operatorname{DecidableEq}\left(E\right)](src:E \to V)(tgt:E \to V),((\forall (i:E),\operatorname{src}\left(i\right) \ne \operatorname{tgt}\left(i\right)) \land \left(\operatorname{Function}.\operatorname{Injective}(\operatorname{fun} (i:E)\mapsto \operatorname{s}\left(\operatorname{src}\left(i\right), \operatorname{tgt}\left(i\right)\right)) \land (\operatorname{SimpleGraph}.\operatorname{fromEdgeSet}(\operatorname{Set}.\operatorname{range}(\operatorname{fun} (i:E)\mapsto \operatorname{s}\left(\operatorname{src}\left(i\right), \operatorname{tgt}\left(i\right)\right)))).\operatorname{IsTree}\right)) \Rightarrow \forall (n:E \to \operatorname{Nat}),(\forall (i:E),2 \le \operatorname{n}\left(i\right)) \Rightarrow \forall (rho:(E \to \operatorname{Nat}) \to \operatorname{Real}),(\forall (k:E \to \operatorname{Nat}),k \in \operatorname{splits}\left(n\right) \Rightarrow 0 < \operatorname{rho}\left(k\right)) \Rightarrow \forall (tau:\operatorname{Real}),tau \in \operatorname{Set}.\operatorname{Icc}((-1:\operatorname{Real}),1) \Rightarrow \forall (z:\operatorname{Complex}),((\operatorname{treePoly}\left(src, tgt, n, rho, tau\right)).\operatorname{map}(\operatorname{algebraMap}\left(\operatorname{Real}, \operatorname{Complex}\right))).\operatorname{IsRoot}(z) \Rightarrow \left\lVert z \right\rVert = 1)$$

*Formalization.* `D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.claim` (`✓ std3`).

*Citation.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

Section 2.2, Conjecture 1, printed p. 14 (PDF p. 15): “For any tree with e edges, any fixed positive integers n₁,…,nₑ and arbitrary ρ(kᵢ,nᵢ)>0 the polynomials P(τ,x, n₁,…,nₑ) have all their x roots on the unit circle.” The displayed tree condition is NamedTreePhaseTransport.NamedSpanningTree src tgt Set.univ in Lean: all edges are selected, and its nonloop, distinct and isTree fields give precisely this condition. The orientation records which endpoint receives the split parameter. The convention uses n i ≥ 2, excluding the empty split sum at n i = 1, and τ ∈ Set.Icc (−1) 1. The source's one-edge argument uses |τ| ≤ 1. Every allowed joint weight is strictly positive. Polynomial.map along algebraMap ℝ ℂ is the complex coefficient polynomial; IsRoot means its evaluation is zero. The conclusion is the complex norm ‖z‖ = 1.

**Theorem 1.5 (Conjecture 1 is refuted for joint weights).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/fiol-martinezmontoya-riosfukelman-2020-tree-lee-yang` (refuted) by `D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fiol-martinezmontoya-riosfukelman-2020-tree-lee-yang","declaration_gid":"D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

The witness is the path 0 → 1 ← 2 with totals (4,4), τ = −1, and weights W₃₁ = ((1,1,1),(1,10,1),(1,1,31)), indexed by the two splits in {1,2,3}. Its masses are (k₁,8−k₁−k₂,k₂). The same polynomial arises from 0 → 1 → 2 with the second weight index reversed. Exact state and split enumeration gives 48−6X+8X²−62X³+24X⁴−62X⁵+8X⁶−6X⁷+48X⁸. It equals 2(X−1)²X³q(X+X⁻¹), where q(y)=24y³+45y²−2y−26. The cubic discriminant is −16404; Cubic.discr_eq_prod_three_roots would make it a square, so q cannot split over ℝ. Algebraic closure and descent of splitting give a nonreal complex root w. A root z of z²−wz+1=0 is nonzero and satisfies w=z+z⁻¹. It is an octic root; if ‖z‖=1, then z⁻¹=conj z, forcing w to be real. The product-weight and physical-weight versions remain open.

## References

- Truth anchor: `D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.claim`
- Truth anchor: `D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.mass`
- Truth anchor: `D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.result`
- Truth anchor: `D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.splits`
- Truth anchor: `D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.treePoly`
- Dependency: [D5/S3/Observer/AgencyHolonomy/NamedTreePhaseTransport](../../Observer/AgencyHolonomy/NamedTreePhaseTransport.md)
