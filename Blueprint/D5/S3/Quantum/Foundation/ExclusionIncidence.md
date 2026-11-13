# Original exclusion incidence

## Abstract

Upper association of the entire original exclusion fibers at pure limiting labels.

V is an arbitrary finite dimensional real normed vector space. C is the original pointed cone, closed and generating, and the original real linear unit u is strictly positive on nonzero cone vectors. K is the entire base C intersect {u=1}, P is all of ext(K) with its actual subspace topology, proper effects are all real linear f with 0<=f<=u on C, and D_p is the entire original exclusion set. The hypotheses do not supply a physical inner product, compactness or closedness of P, label injectivity, Pair, least effects, spectrality or a Jordan representation.

**Theorem 1.1 (Limits of actual original exclusions).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionIncidence.exclusion_upper_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionIncidence.exclusion_upper_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original pure p, every sequence pn of original pure labels converging to p in P, every sequence yn in V converging to y, if yn(n) belongs to the entire D_pn(n) for every n, then y belongs to the entire D_p. There is no ball assumption in this prerequisite of IX118.3. It also applies to the nonzero original EB3 domain.

Choose an actual full-interval proper confirmer f_n witnessing yn(n) in D_pn(n). Regard it as a continuous linear map in the unchanged original norm; finite dimensionality makes this representation exact. The unchanged effects_compact proof from ContinuousFrameSum supplies a convergent subsequence in the entire original effect interval. Joint continuous evaluation at the same subsequence of labels and states gives e(p)=1 and e(y)=0. Closedness of the original compact base gives y in K. The same e is therefore an actual witness for y in D_p. This pointwise argument needs no continuously selected confirmer and no pure-limit closure assumption. exclusion_upper_eventually consumes this statement on its live subsequence path.

**Theorem 1.2 (Uniform upper approximation of entire fibers).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionIncidence.exclusion_upper_eventually`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionIncidence.exclusion_upper_eventually` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original pure p, every pn tending to p in the actual P, and every positive real epsilon, eventually for every y in the entire D_pn(n) there is z in the entire D_p with original-norm distance dist(y,z)<epsilon. The quantifiers include every mixed state of every exclusion fiber. Compactness of K is derived from the closed cone and strictly positive original unit; it is not an extra input.

If uniform upper approximation fails, extract a strictly increasing sequence of bad indices and one actual bad exclusion state per index. Compactness of K supplies a second subsequence converging to z. The same composed label subsequence still tends to the original pure p. exclusion_upper_limit places z in D_p, contradicting the positive lower bound on the distances of all chosen bad states to every point of D_p. This is the upper half of the whole-fiber Hausdorff argument in IX118.3, not that theorem's equivalence.

**Definition 1.3 (Original edge lifting at every index).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionIncidence.edgeLifting`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionIncidence.edgeLifting` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

edgeLifting(C,u) uses the original full-interval comparison equal to zero and is precisely original (O): for all p,q in all pure(C,u) with q in the entire original D_p, and every pn:Nat to pure(C,u) converging to p in the actual subtype topology, there exists qn:Nat to pure(C,u) converging to q such that qn(n) is in D_pn(n) for every n. The original_open_incidence_whole_limit theorem consumes this definition. The private comparison_zero_iff_exclusion bridge proves that, for every original mixed state in K, this infimum is attained in the full original confirming interval and its zero is equivalent to membership in the entire D_p. Its compact confirming interval is the intersection of the entire compact original effect set with the closed one-value evaluation constraint; the original unit supplies a member. The bridge is consumed both when lifting boundary points and when passing between original edge lifting and actual projection fibers. No selected or eventually-only incidence relation is substituted.

**Definition 1.4 (The entire actual incidence).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionIncidence.incidence`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionIncidence.incidence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

incidence(C,u) is the subtype of all ordered pairs of original pure points (p,q) for which q belongs to the whole original D_p. Its topology is exactly the subtype topology from the actual P squared.

**Definition 1.5 (First actual projection).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionIncidence.firstProjection`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionIncidence.firstProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

firstProjection(C,u) sends each actual incidence pair (p,q) to p.

**Definition 1.6 (Second actual projection).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionIncidence.secondProjection`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionIncidence.secondProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

secondProjection(C,u) sends each actual incidence pair (p,q) to q.

**Definition 1.7 (Actual zero-symmetry swap).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionIncidence.incidenceSwap`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionIncidence.incidenceSwap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original C,u, incidenceSwap(C,u) is the homeomorphism of the actual incidence taking (p,q) to (q,p). It consumes the original exclusion_symmetric theorem, whose witness is the complementary full original effect u-f. Both maps are restrictions of the actual product coordinate swap.

**Theorem 1.8 (Actual open incidence controls the whole balls).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionIncidence.original_open_incidence_whole_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionIncidence.original_open_incidence_whole_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original finite dimensional real normed V, closed generating cone C, strictly positive original unit u, and whole exclusionBalls(C,u), exact original edgeLifting(C,u) is equivalent to openness of firstProjection on the actual incidence. Under that condition secondProjection is open and every sequence pn in all P tending to an original pure p satisfies hausdorffDist(D_pn(n),D_p) tending to zero in the unchanged original norm. This proves O iff actual open first projection, actual second projection openness, and the forward O-to-whole-ball implication of IX118.3 on the larger EB_ge1 domain, including EB3. It does not assert the reverse Hausdorff implication or sphere continuity.

For O-to-open, lift the second endpoints along a convergent sequence of first endpoints outside an open image; convergence in the actual product subtype contradicts avoidance of that open set. Conversely apply the pinned lower-hemicontinuity sequential selection theorem to the actual first-projection fibers. Its eventual lift is repaired at every exceptional index using an actual pure point of that full original exclusion face; no selected surrogate relation is used. Original effect-complement zero symmetry constructs incidenceSwap as a homeomorphism of the actual incidence, with secondProjection=firstProjection composed with incidenceSwap. OriginalFacePolarity.chart_boundary identifies every entire chart sphere with D_p intersect P. The pinned affine-image convex-hull theorem and convexHull_sphere_eq_closedBall identify all D_p as the convex hull of these actual original pure points. The set of points admitting convergent whole-fiber lifts along the fixed pn is convex: lift two points along that same pn and preserve their scalar coefficients. Original (O) puts every boundary point in this set. Convex-hull minimality therefore supplies a whole-fiber lift of every mixed point. Compactness of D_p supplies a finite epsilon/2 net. Only finitely many lift estimates must hold simultaneously, so the lower approximation is uniform on all D_p. Combining it with exclusion_upper_eventually bounds the whole Hausdorff distance. No new continuous chart, common metric, fixed dimension, compact P, or effect supplier is assumed.

**Theorem 1.9 (Intrinsic boundaries of full rank ball limits).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionIncidence.affine_ball_boundary_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionIncidence.affine_ball_boundary_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be a nontrivial finite dimensional strictly convex real normed space and V any finite dimensional real normed space. Let a_n:E to V and b:E to V be injective affine maps. If the entire images a_n of the closed unit ball converge in Hausdorff distance to the entire image under b, then their intrinsic frontiers converge in Hausdorff distance to the intrinsic frontier of the limiting image. Every convergent sequence xn in the respective intrinsic frontiers has its limit in the limiting intrinsic frontier. Taking E as Euclidean three-space proves the moving affine-hull three-ball statement; V retains its original norm. Neither the centers, the linear maps, their axes nor any chosen gauges are assumed continuous.

Convergence in the native nonempty compact hyperspace makes the union of the whole ball images compact. Its norm bound controls the centers and, by the unit-sphere operator-norm bound, the arbitrary linear parts. Finite dimensionality supplies a convergent parameter subsequence inside every index subsequence. Joint continuous evaluation gives convergence of compact ball and sphere images. Equality of the limiting ball image with the injective limiting chart puts the latter linear range inside the limiting operator range; rank-nullity forces the limiting operator to be injective. Injective affine maps carry the extreme points of the strictly convex unit ball to the extreme points of their whole image, so the two limiting sphere images agree. The subsequence criterion gives convergence of the entire sphere-image sequence. Restriction to the actual affine range, an affine equivalence onto that range and its isometric subtype inclusion transport intrinsic frontiers. The full-rank limiting chart is essential: the three-ball images under diag(1,1,1/n) tend to a disk, while their sphere images tend to the entire disk.

**Theorem 1.10 (Open original incidence and continuous whole exclusions).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionIncidence.original_open_incidence_iff_whole_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionIncidence.original_open_incidence_iff_whole_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the entire original finite dimensional real normed cone and unit domain above, assume that for every original pure p there exists an injective affine chart of the entire D_p by the Euclidean closed three-ball. Exact original edge lifting O is equivalent to openness of the actual first projection and to Hausdorff continuity of p mapped to the entire D_p in the unchanged original norm. Under these equivalent conditions p mapped to the entire P intersect D_p is also Hausdorff continuous, and the actual second projection is open. The statement uses neighborhood limits at every original pure label, includes every actual edge and every label sequence, and imposes no Inj, closedness of P, Pair, continuous chart selection or inner product on the original V.

The forward direction and the actual projection equivalence reuse original_open_incidence_whole_limit. Choose arbitrary three-dimensional charts only to represent the actual fibers. The full-rank boundary-limit theorem applies to their whole images in V with its original norm. The original chart_boundary identity identifies each intrinsic frontier with the entire original pure sphere. For every actual q in the limiting sphere and every n, compactness supplies a nearest point in the entire sphere over pn(n). Continuity of infimum distance in the native nonempty compact hyperspace makes these nearest points tend to q, so the lift belongs to the exact original relation at every index. Sequential continuity on the actual metric subtype P yields the displayed neighborhood limits. The second projection uses the existing actual effect-complement swap.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionIncidence.affine_ball_boundary_limit`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionIncidence.edgeLifting`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionIncidence.exclusion_upper_eventually`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionIncidence.exclusion_upper_limit`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionIncidence.firstProjection`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionIncidence.incidence`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionIncidence.incidenceSwap`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionIncidence.original_open_incidence_iff_whole_continuous`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionIncidence.original_open_incidence_whole_limit`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionIncidence.secondProjection`
- Dependency: [D5/S3/Quantum/Foundation/ContinuousFrameSum](ContinuousFrameSum.md)
- Dependency: [D5/S3/Quantum/Foundation/OriginalFacePolarity](OriginalFacePolarity.md)
