# A positive nonconstant solution of the tree equations

## Abstract

A cubic tree admits positive nonconstant edge lengths satisfying the tree equations of motion.

**Definition 1.1 (The sum of reciprocal incident lengths).**

$$\forall (v: \operatorname{Type}), (\forall (g: \operatorname{SimpleGraph}\left(v\right)), ([\operatorname{SimpleGraph.LocallyFinite}\left(g\right)], (\forall (ell: (v) \to ((v) \to (\mathbb{R}))), (\forall (i: v), ((\operatorname{D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation.cVal}\left(g, ell, i\right): \mathbb{R}) = \sum_{j \in \operatorname{SimpleGraph.neighborFinset}\left(g, i\right)} (\frac{(1: \mathbb{R})}{ell\left(i, j\right)}))))))$$

*Formalization.* `D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.cVal` (`✓ std3`).

*Citation.* An Huang; Bogdan Stoica; Xuyang Xia; Xiao Zhong (2020). *Bounds on the Ricci curvature and solutions to the Einstein equations for weighted graphs*. URL: <https://arxiv.org/abs/2006.06716v1>.

*Commentary.*

For a locally finite simple graph g and a real function ell on ordered pairs of vertices, cVal sums the reciprocal lengths over the neighbours of i. This is c_i in Huang, Stoica, Xia and Zhong, ms.tex line 257. On a tree with positive edge lengths, the shortest-path length P_ij of adjacent vertices equals their edge length (lines 233–237 and 538). The definition itself imposes neither positivity nor symmetry.

**Definition 1.2 (The sum of reciprocal squared incident lengths).**

$$\forall (v: \operatorname{Type}), (\forall (g: \operatorname{SimpleGraph}\left(v\right)), ([\operatorname{SimpleGraph.LocallyFinite}\left(g\right)], (\forall (ell: (v) \to ((v) \to (\mathbb{R}))), (\forall (i: v), ((\operatorname{D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation.dVal}\left(g, ell, i\right): \mathbb{R}) = \sum_{j \in \operatorname{SimpleGraph.neighborFinset}\left(g, i\right)} (\frac{(1: \mathbb{R})}{(ell\left(i, j\right))^{2}}))))))$$

*Formalization.* `D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.dVal` (`✓ std3`).

*Citation.* An Huang; Bogdan Stoica; Xuyang Xia; Xiao Zhong (2020). *Bounds on the Ricci curvature and solutions to the Einstein equations for weighted graphs*. URL: <https://arxiv.org/abs/2006.06716v1>.

*Commentary.*

The quantity dVal sums the reciprocals of the squares of the incident lengths. It is d_i of ms.tex line 255, with the same finite neighbour set as cVal. Both definitions use real division, including its value zero when the denominator is zero.

**Definition 1.3 (The vertex ratio).**

$$\forall (v: \operatorname{Type}), (\forall (g: \operatorname{SimpleGraph}\left(v\right)), ([\operatorname{SimpleGraph.LocallyFinite}\left(g\right)], (\forall (ell: (v) \to ((v) \to (\mathbb{R}))), (\forall (i: v), ((\operatorname{D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation.ratio}\left(g, ell, i\right): \mathbb{R}) = \frac{\operatorname{D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation.cVal}\left(g, ell, i\right)}{\operatorname{D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation.dVal}\left(g, ell, i\right)})))))$$

*Formalization.* `D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.ratio` (`✓ std3`).

*Citation.* An Huang; Bogdan Stoica; Xuyang Xia; Xiao Zhong (2020). *Bounds on the Ricci curvature and solutions to the Einstein equations for weighted graphs*. URL: <https://arxiv.org/abs/2006.06716v1>.

*Commentary.*

The vertex ratio is cVal divided by dVal, the quantity c_i/d_i occurring in the tree equation of motion at ms.tex line 552. No nonzero-denominator hypothesis is part of this definition.

**Definition 1.4 (The tree equation residual).**

$$\forall (v: \operatorname{Type}), (\forall (g: \operatorname{SimpleGraph}\left(v\right)), ([\operatorname{SimpleGraph.LocallyFinite}\left(g\right)], (\forall (ell: (v) \to ((v) \to (\mathbb{R}))), (\forall (i: v), (\forall (j: v), ((\operatorname{D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation.tEoM}\left(g, ell, i, j\right): \mathbb{R}) = \frac{(1: \mathbb{R})}{ell\left(i, j\right)} \cdot \left((\operatorname{D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation.ratio}\left(g, ell, i\right))^{2} + (\operatorname{D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation.ratio}\left(g, ell, j\right))^{2}\right) - \operatorname{D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation.ratio}\left(g, ell, i\right) - \operatorname{D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation.ratio}\left(g, ell, j\right)))))))$$

*Formalization.* `D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.tEoM` (`✓ std3`).

*Citation.* An Huang; Bogdan Stoica; Xuyang Xia; Xiao Zhong (2020). *Bounds on the Ricci curvature and solutions to the Einstein equations for weighted graphs*. URL: <https://arxiv.org/abs/2006.06716v1>.

*Commentary.*

The residual on an ordered pair i,j is the reciprocal length times the sum of the squared vertex ratios, minus the two ratios. Its vanishing on every edge is the tree equation of motion in ms.tex lines 549–554. The formula defines a real value on every ordered pair; adjacency is required when asserting the equation on edges.

**Definition 1.5 (The conjecture on the cubic tree).**

$$(\operatorname{D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation.claim}) \Leftrightarrow (\forall (v: \operatorname{Type}), (\forall (g: \operatorname{SimpleGraph}\left(v\right)), ([\operatorname{SimpleGraph.LocallyFinite}\left(g\right)], ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(g\right)\right)], ((\operatorname{SimpleGraph.IsTree}\left(g\right)) \to ((\forall (i: v), (\operatorname{SimpleGraph.degree}\left(g, i\right) = (3: \mathbb{N}))) \to (\forall (ell: (v) \to ((v) \to (\mathbb{R}))), ((\forall (i: v), (\forall (j: v), ((\operatorname{SimpleGraph.Adj}\left(g, i, j\right)) \to (ell\left(i, j\right) = ell\left(j, i\right))))) \to ((\forall (i: v), (\forall (j: v), ((\operatorname{SimpleGraph.Adj}\left(g, i, j\right)) \to ((0: \mathbb{R}) < ell\left(i, j\right))))) \to ((\forall (i: v), (\forall (j: v), ((\operatorname{SimpleGraph.Adj}\left(g, i, j\right)) \to (\operatorname{D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation.tEoM}\left(g, ell, i, j\right) = (0: \mathbb{R}))))) \to (\exists (c: \mathbb{R}), (\forall (i: v), (\forall (j: v), ((\operatorname{SimpleGraph.Adj}\left(g, i, j\right)) \to (ell\left(i, j\right) = c)))))))))))))))$$

*Formalization.* `D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.claim` (`✓ std3`).

*Citation.* An Huang; Bogdan Stoica; Xuyang Xia; Xiao Zhong (2020). *Bounds on the Ricci curvature and solutions to the Einstein equations for weighted graphs*. URL: <https://arxiv.org/abs/2006.06716v1>.

*Commentary.*

The second conjecture in Section 5.2, ms.tex lines 1931–1934, asserts that T₂ has no positive nonconstant solution. The source defines T_q to have degree q+1 at every vertex (line 542) and calls equal edge lengths the constant solution (line 556). Here the assertion ranges over every locally finite simple tree on a type v with degree three everywhere and decidable adjacency. For each real length function symmetric and positive on edges, vanishing of every edge residual would imply a single real value c for all edge lengths. No boundary condition or uniform positive lower bound on lengths is assumed.

**Theorem 1.6 (A cubic tree with a positive nonconstant solution).**

$$\neg (\forall (v: \operatorname{Type}), (\forall (g: \operatorname{SimpleGraph}\left(v\right)), ([\operatorname{SimpleGraph.LocallyFinite}\left(g\right)], ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(g\right)\right)], ((\operatorname{SimpleGraph.IsTree}\left(g\right)) \to ((\forall (i: v), (\operatorname{SimpleGraph.degree}\left(g, i\right) = (3: \mathbb{N}))) \to (\forall (ell: (v) \to ((v) \to (\mathbb{R}))), ((\forall (i: v), (\forall (j: v), ((\operatorname{SimpleGraph.Adj}\left(g, i, j\right)) \to (ell\left(i, j\right) = ell\left(j, i\right))))) \to ((\forall (i: v), (\forall (j: v), ((\operatorname{SimpleGraph.Adj}\left(g, i, j\right)) \to ((0: \mathbb{R}) < ell\left(i, j\right))))) \to ((\forall (i: v), (\forall (j: v), ((\operatorname{SimpleGraph.Adj}\left(g, i, j\right)) \to (\operatorname{D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation.tEoM}\left(g, ell, i, j\right) = (0: \mathbb{R}))))) \to (\exists (c: \mathbb{R}), (\forall (i: v), (\forall (j: v), ((\operatorname{SimpleGraph.Adj}\left(g, i, j\right)) \to (ell\left(i, j\right) = c)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/huang-stoica-xia-zhong-2020-tree-equations-nonconstant` (refuted) by `D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"huang-stoica-xia-zhong-2020-tree-equations-nonconstant","declaration_gid":"D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* An Huang; Bogdan Stoica; Xuyang Xia; Xiao Zhong (2020). *Bounds on the Ricci curvature and solutions to the Einstein equations for weighted graphs*. URL: <https://arxiv.org/abs/2006.06716v1>.

*Commentary.*

Use vertices vₙ indexed by integers n and vertices bₙ,𝑤 indexed by an integer and a finite Boolean list w. Define a predecessor p by p(vₙ)=vₙ₋₁, p(bₙ,∅)=vₙ, and p(bₙ,β::w)=bₙ,𝑤. Give vₙ height n and bₙ,𝑤 height n+1+|w|, where the natural list length is included in the integers. Every predecessor lowers height by one. Join two vertices precisely when one is the predecessor of the other; this is symmetric and has no loops.

The neighbours of vₙ are vₙ₋₁, vₙ₊₁ and bₙ,∅. The neighbours of bₙ,𝑤 are its predecessor, bₙ,false::w and bₙ,true::w. These lists give all neighbours, with three distinct entries in each case: the two children differ in their first Boolean, and their height exceeds that of the predecessor. Thus the simple graph is locally finite and has degree three everywhere.

Every vₙ is connected to v₀ by finitely many spine edges, using integer induction in both directions. Repeatedly removing the first Boolean connects bₙ,𝑤 to vₙ, so all vertices are connected. If a cycle existed, choose a vertex of maximal height on it and rotate the cycle to start there. Each of its two cycle neighbours has height at most that maximum and therefore must be its unique predecessor. This identifies the second and penultimate vertices of the cycle, a contradiction. The graph is a tree.

Set sₙ=2ⁿ in the real numbers, with integer exponent n. Then sₙ is positive, sₙ₊₁=2sₙ and sₙ₋₁=sₙ/2. Define a real function L on all ordered pairs by L(vₙ,vₘ)=(5/3)sₖ, L(vₙ,bₘ,𝑤)=sₘ, L(bₙ,𝑤,vₘ)=sₙ and L(bₙ,𝑤,bₘ,𝑧)=sₖ, where k=min(n,m). These expressions are symmetric and positive. On an edge vₙ∼vₙ₊₁ the length is (5/3)sₙ; on every edge in the branch attached to vₙ, including its attachment edge, the length is sₙ.

At vₙ the three incident lengths are 5sₙ/6, 5sₙ/3 and sₙ. Summing their reciprocals gives cVal=14/(5sₙ), while summing their reciprocal squares gives dVal=14/(5sₙ²). Their ratio is sₙ. At bₙ,𝑤 all three incident lengths are sₙ, so cVal=3/sₙ, dVal=3/sₙ² and the ratio is again sₙ. Positivity of sₙ permits the divisions in both calculations.

First evaluate the residual on each edge from a vertex to its predecessor. For vₙ and vₙ₋₁ the endpoint ratios are sₙ and sₙ/2 and the length is 5sₙ/6. Hence the residual is (sₙ²+(sₙ/2)²)/(5sₙ/6)−sₙ−sₙ/2=0. For bₙ,𝑤 and its predecessor, whether w is empty or nonempty, the ratios at both endpoints and the edge length are sₙ, giving 2sₙ²/sₙ−2sₙ=0. Every edge has one of these orientations; symmetry of L and the residual expression gives zero for the reverse orientation as well.

The attachment edge v₀∼b₀,∅ has length 1, whereas v₀∼v₁ has length 5/3, so the edge lengths cannot all equal a single c. Applying the conjectured implication to this tree and L would give exactly such a c, contradicting these two edge values.

## References

- Truth anchor: `D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.cVal`
- Truth anchor: `D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.claim`
- Truth anchor: `D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.dVal`
- Truth anchor: `D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.ratio`
- Truth anchor: `D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.result`
- Truth anchor: `D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.tEoM`
