# Relative open-preserving zero-dimensional resolution

## Abstract

An open compact Hausdorff map with a compact metrizable kernel admits a zero-dimensional resolution preserving openness over an arbitrary compact zero-dimensional base.

The universe levels uB, uT and uK are independent. B is compact Hausdorff and totally disconnected, T is compact Hausdorff, and K is compact metric. The map p is continuous, open and surjective. The continuous map u separates points within fibers: pairmap(p,u) sends t to (p(t),u(t)) and is a topological embedding. This is the relative metrizable-kernel hypothesis. No metric or countable basis on B, and no metric on T, is assumed.

**Theorem 1.1 (Full relative resolution).**

$$\begin{aligned}\forall B: Type_{uB}, \forall T: Type_{uT}, \forall K: Type_{uK}, \\{}[\operatorname{TopologicalSpace}\left(B\right)] {}[\operatorname{CompactSpace}\left(B\right)] {}[\operatorname{TTwoSpace}\left(B\right)] {}[\operatorname{TotallyDisconnectedSpace}\left(B\right)] \\{}[\operatorname{TopologicalSpace}\left(T\right)] {}[\operatorname{CompactSpace}\left(T\right)] {}[\operatorname{TTwoSpace}\left(T\right)] {}[\operatorname{MetricSpace}\left(K\right)] {}[\operatorname{CompactSpace}\left(K\right)] \\\forall p: T \to B, \forall u: T \to K, \\\operatorname{Continuous}\left(p\right) \land \operatorname{IsOpenMap}\left(p\right) \land \operatorname{Surjective}\left(p\right) \land \operatorname{Continuous}\left(u\right) \land \operatorname{IsEmbedding}\left(\operatorname{pairmap}\left(p, u\right)\right) \Rightarrow\\\exists Z: Type_{uB}, \exists tZ: \operatorname{TopologicalSpace}\left(Z\right),\\\operatorname{CompactSpace}\left(Z\right) \land \operatorname{TTwoSpace}\left(Z\right) \land \operatorname{TotallyDisconnectedSpace}\left(Z\right) \land\\\exists r: Z \to T, \operatorname{Continuous}\left(r\right) \land \operatorname{Surjective}\left(r\right) \land\\\operatorname{IsOpenMap}\left(\operatorname{compose}\left(p, r\right)\right) \land \operatorname{Surjective}\left(\operatorname{compose}\left(p, r\right)\right) \land{\operatorname{MetrizableSpace}\left(B\right) \Rightarrow \operatorname{MetrizableSpace}\left(Z\right)}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Resolution/RelativeOpen.exists_relative_open_resolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All properties of Z and r use the returned topology tZ. compose(p,r) denotes p after r. The same constructed Z is metrizable whenever B is metrizable. The theorem supplies an actual type and map, rather than assuming a package of sections, paths or open projections.

Let F be the literal range of pairmap(p,u). Compactness and the Hausdorff product make F closed. Define Phi(b) to be exactly the set of k with (b,k) in F. Surjectivity of p makes each fiber nonempty; its closedness is the preimage of F under k mapped to (b,k). For every open U in K the hitting set {b : Phi(b) intersects U} equals p applied to the inverse image of U under u. It is open. Compact K supplies completeness by complete_of_compact. The classical prescribed-point selection theorem CompactZeroDimensional.exists_continuous_selection_through therefore gives a continuous K-valued fiber selector through every t.

Put epsilon(n)=(1/2)^n. For each t the distance-open set W(t) consists of x in T with dist(u(x),v(t)(p(x))) less than epsilon(n), where v(t) is the selector through t. These W(t) cover all of T. A finite subcover of compact T, reindexed by I(n)=Fin(N(n)), gives finitely many global selectors v(n,i). For every actual fiber point k over b, some v(n,i)(b) is within epsilon(n) of k. The finite cover is taken on all T, rather than on a single fiber or only on B.

The distance between v(n,i) and v(n+1,j) is continuous on B. Interpolate its closed band distance at most epsilon(n)+epsilon(n+1) inside its open band distance less than 2 epsilon(n)+epsilon(n+1), using exists_clopen_of_closed_subset_open. Call the resulting clopen set A(n,i,j). At every base b, every vertex i has a successor: apply the next net to the fiber member v(n,i)(b). Separately, for every prescribed k in Phi(b), choose net indices at all levels for that same k. The triangle inequality puts all consecutive pairs in their lower distance bands. This gives a full allowed path approximating k.

Z is the closed subtype of B times the dependent product of I(n), containing exactly pairs (b,a) with b in A(n,a(n),a(n+1)) for every n. Each transition predicate is a finite union of clopen slices, and their intersection is closed. Compactness, Hausdorffness and total disconnectedness pass from the product to Z. The dynamic map z mapped to v(n,z.indices(n))(z.base) is continuous by continuous_prod_of_discrete_right. Its bounded continuous maps have uniform increments at most (5/2)epsilon(n). The geometric Cauchy theorem and completeness give a continuous uniform limit k, with tail at most 5 epsilon(n).

For every path the pairs (z.base,v(n,z.indices(n))(z.base)) belong to F. Their limit (z.base,k(z)) stays in F by closedness, without any metric on B. Apply the inverse of IsEmbedding.toHomeomorph to return to the original T; this defines continuous r and proves p after r equals the base projection. For each t, its specific approximating path has limit u(t): the uniform tail and net error bound its distance by 6 epsilon(n), which tends to zero. The range homeomorphism then gives r(z)=t literally. Both r and p after r are surjective.

For an open V in B and a prefix x of length N, the base-projection image of the corresponding cylinder in Z is exactly V intersected with A(n,x(n),x(n+1)) for n in Finset.range(N-1). The reverse inclusion extends the final prescribed vertex at that same base, using dependent Nat recursion and seriality. For length zero there are no prescribed transitions: start at x(0) and construct a path at that base. Thus every cylinder image is open. PiNat.isTopologicalBasis_cylinders, the product and subtype bases, and IsTopologicalBasis.isOpenMap_iff prove openness for arbitrary open subsets of Z.

No Nonempty instance is assumed on B, T or K. Empty T can produce empty finite covers, and all constructions are empty functions where required. If B has a point, surjectivity of p supplies a point of T and then of K; no arbitrary K point is used. For the optional clause only, PiNat.metricSpace gives the dependent Nat product its compatible discrete-product metric. Metrizability of B then passes through the product and subtype to this same Z.

The selection input is Michael's classical zero-dimensional selection principle, with the attribution and inspected scope in Library/Topology/valov2008milyutinmaps.md. The relative construction and its applicability are explained in Library/Topology/project2026relativeopenresolution.md. This theorem concerns a metrizable relative kernel; it does not resolve unrestricted nonmetric open-map resolution or Peng Questions 5.1 and 5.2.

## References

- Truth anchor: `D5/S3/Topology/Resolution/RelativeOpen.exists_relative_open_resolution`
- Dependency: [D5/S3/Topology/Selection/CompactZeroDimensional](../Selection/CompactZeroDimensional.md)
