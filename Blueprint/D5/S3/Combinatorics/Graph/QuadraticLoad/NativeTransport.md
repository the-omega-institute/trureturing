# Transport of native quadratic allocations

## Abstract

The native finite-graph quadratic-load infimum respects injective graph maps and is additive on Cartesian products.

Let G and H be finite simple graphs on nonempty vertex types V and W. A feasible allocation a assigns a real number in [0,1] to every ordered pair, with a(v,w)+a(w,v)=1 on edges. Its native load at v is the sum of a(v,w)^2 over neighbours w. The function maxLoad is the maximum of those loads, and kappa is the infimum of maxLoad over all feasible allocations. Nonedge coordinates remain bounded and never enter the load. The Cartesian graph has vertices (v,w); an edge changes exactly one coordinate along an edge of its factor, leaving the other coordinate fixed.

**Theorem 1.1 (Restriction along an injective graph map).**

$$\forall V \in Type,\; \forall W \in Type,\; [\mathrm{Fintype}\left(V\right)] [\mathrm{Fintype}\left(W\right)] [\mathrm{Nonempty}\left(V\right)] [\mathrm{Nonempty}\left(W\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \forall H \in \mathrm{SimpleGraph}\left(W\right),\; [\mathrm{DecidableRel}\left(\mathrm{Adj}\left(G\right)\right)] [\mathrm{DecidableRel}\left(\mathrm{Adj}\left(H\right)\right)] \forall f \in V \to W,\; \mathrm{Injective}\left(f\right) \Rightarrow \left(\left(\forall x \in V,\; \forall y \in V,\; \mathrm{Adj}\left(G, x, y\right) \Rightarrow \mathrm{Adj}\left(H, \mathrm{f}\left(x\right), \mathrm{f}\left(y\right)\right)\right) \Rightarrow \mathrm{kappa}\left(G\right) \le \mathrm{kappa}\left(H\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/QuadraticLoad/NativeTransport.kappa_le_of_injective_hom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take an actual minimizing allocation a on H. Pull it back by f: the share at (v,v') is a(f(v),f(v')). All share bounds and edge-complement equations are preserved. Injectivity makes the images of the neighbours of v distinct; edge preservation places all of them among the neighbours of f(v). The pulled-back load is consequently at most the ambient load because the additional ambient summands are nonnegative squares. Taking the maximum and using the native minimizing allocation proves the inequality. The map need not be surjective or reflect adjacency.

**Theorem 1.2 (Cartesian additivity on the full allocation domain).**

$$\forall V \in Type,\; \forall W \in Type,\; [\mathrm{Fintype}\left(V\right)] [\mathrm{Fintype}\left(W\right)] [\mathrm{Nonempty}\left(V\right)] [\mathrm{Nonempty}\left(W\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \forall H \in \mathrm{SimpleGraph}\left(W\right),\; [\mathrm{DecidableRel}\left(\mathrm{Adj}\left(G\right)\right)] [\mathrm{DecidableRel}\left(\mathrm{Adj}\left(H\right)\right)] \mathrm{kappa}\left(\mathrm{boxProd}\left(G, H\right)\right) = \mathrm{kappa}\left(G\right) + \mathrm{kappa}\left(H\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/QuadraticLoad/NativeTransport.kappa_box` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the upper bound take actual factor minimizers a and b. At an ordered pair x,y in V times W use b(x.second,y.second) when x.first=y.first, and a(x.first,y.first) otherwise. This is feasible even off edges. The two disjoint neighbour classes give exactly the sum of the factor loads.

For the lower bound use the full simplex of nonnegative vectors of total mass one. On actual feasible allocations the payoff is the weighted sum of native loads. The allocation domain is compact and convex; the simplex is nonempty, compact and convex. The payoff is continuous, convex in allocation, and affine in the law. Pinned Sion supplies a saddle point. Testing every point mass shows that its law p bounds kappa(G) below the p-weighted load for every feasible allocation; the same argument gives q for H.

Fix one ambient product allocation A. Every slice at fixed w is feasible on G, and every slice at fixed v is feasible on H. Apply the two universal factor certificates, multiply by q(w) and p(v), respectively, then sum. Under the one common law p(v)q(w), the disjoint neighbour classes combine to the ambient load. Normalization bounds its expectation by maxLoad(A). Choosing an actual ambient minimizer gives the lower inequality. All feasible allocations are retained, and zero masses are allowed: the argument never divides by a law coordinate. It includes singletons, edgeless factors and unequal vertex-type universes. These two graph results do not establish legal-word block correspondences or the existence and characterization of a legal-word growth constant.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/QuadraticLoad/NativeTransport.kappa_box`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadraticLoad/NativeTransport.kappa_le_of_injective_hom`
- Dependency: [D5/S3/Combinatorics/Graph/QuadraticEdgeLoad](../QuadraticEdgeLoad.md)
