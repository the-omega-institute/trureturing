# Fixed zero effects on the entire original state body

## Abstract

Entire original zero effects attain their global maximum in the exclusion face; whole-ball collapse obstructs every fixed complete zero test on one common edge.

**Definition 1.1 (zeroEffects).**

Lean statement: `D5/S3/Quantum/Foundation/FixedZeroObstruction.zeroEffects`

*Formalization.* `D5/S3/Quantum/Foundation/FixedZeroObstruction.zeroEffects` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original pure t, this is exactly the set of original linear g satisfying proper(C,u,g) and g(t)=0.

**Definition 1.2 (fullZeroConfirmers).**

Lean statement: `D5/S3/Quantum/Foundation/FixedZeroObstruction.fullZeroConfirmers`

*Formalization.* `D5/S3/Quantum/Foundation/FixedZeroObstruction.fullZeroConfirmers` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original pure s, this is exactly the set of original linear h satisfying confirms(C,u,s,h) and h(x)=0 for every x in the entire exclusion(C,u,s).

**Definition 1.3 (stateReadout).**

Lean statement: `D5/S3/Quantum/Foundation/FixedZeroObstruction.stateReadout`

*Formalization.* `D5/S3/Quantum/Foundation/FixedZeroObstruction.stateReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original linear f, this is its continuous restriction to the entire subtype base(C,u), evaluated at every original normalized state.

**Definition 1.4 (stateNorm).**

Lean statement: `D5/S3/Quantum/Foundation/FixedZeroObstruction.stateNorm`

*Formalization.* `D5/S3/Quantum/Foundation/FixedZeroObstruction.stateNorm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the original closed-cone and strictly-positive-unit hypotheses and every original linear f, this is the continuous-map supremum norm of stateReadout(f). The compact-space instance is obtained from compactness of the original base.

**Definition 1.5 (faceMaximum).**

Lean statement: `D5/S3/Quantum/Foundation/FixedZeroObstruction.faceMaximum`

*Formalization.* `D5/S3/Quantum/Foundation/FixedZeroObstruction.faceMaximum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original pure t and original linear h, this is sSup of the image of the entire exclusion(C,u,t) under h.

**Definition 1.6 (zeroDistance).**

Lean statement: `D5/S3/Quantum/Foundation/FixedZeroObstruction.zeroDistance`

*Formalization.* `D5/S3/Quantum/Foundation/FixedZeroObstruction.zeroDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under original compact-base hypotheses, for every pure t and original linear h, this is Metric.infDist from stateReadout(h) to the image of the entire zeroEffects(C,u,t) under stateReadout.

**Definition 1.7 (stableZeroWitness).**

Lean statement: `D5/S3/Quantum/Foundation/FixedZeroObstruction.stableZeroWitness`

*Formalization.* `D5/S3/Quantum/Foundation/FixedZeroObstruction.stableZeroWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original s,r with r in exclusion(C,u,s), there exists one h in fullZeroConfirmers(C,u,s) such that for every pure sequence t(n) tending to r there exists a sequence g(n) of original linear effects, each in zeroEffects(C,u,t(n)), with stateNorm(g(n)-h) tending to zero. The h quantifier precedes the t sequence.

**Definition 1.8 (openEdges).**

Lean statement: `D5/S3/Quantum/Foundation/FixedZeroObstruction.openEdges`

*Formalization.* `D5/S3/Quantum/Foundation/FixedZeroObstruction.openEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original p,s with s in exclusion(C,u,p), and every original pure sequence t(n) tending to p, there exists an original pure sequence v(n), in exclusion(C,u,t(n)) at every index, tending to s.

V is any finite dimensional real normed carrier, C is its closed generating cone, and u is strictly positive on every nonzero cone vector. K is the entire normalized base, P all its extreme points, and effects are the entire original interval between zero and u. StrictPositiveUnit denotes exactly that cone condition; InjectiveExclusionLabels denotes injectivity of p mapped to the whole exclusion. Every exclusion is an affine Euclidean closed ball of positive dimension, with dimensions allowed to vary.

zeroEffects(C,u,t) contains exactly the proper linear effects zero at t. fullZeroConfirmers(C,u,s) contains exactly the proper confirmers of s vanishing on all of its exclusion. stateReadout restricts a linear functional to every point of K as a continuous real function. stateNorm is the existing supremum norm of that function, so its value is the maximum absolute readout over all K. faceMaximum is the supremum on the entire exclusion; compactness makes it an attained maximum. zeroDistance is the existing metric infimum distance in C(K,R) to the image of the entire zero-effect fiber, preserving the original full-state norm.

The exclusion interface agrees with the original lower-envelope zero set: x belongs to exclusion(C,u,p) exactly when x is in K and comparison(C,u,p,x)=0. ContinuousFrameSum.effects_compact gives compactness of the entire original effect interval under strict positivity and generation. The confirming slice is closed and contains u, so every evaluation attains its minimum there; nonnegativity proves the stated equivalence. The pure global maximizer below therefore gives max over all K of g equal to max over the entire original D(t) of g, including g=0.

**Theorem 1.9 (A pure global maximizer in the entire exclusion).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\operatorname{StrictPositiveUnit}\left(C, u\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\operatorname{exclusionBalls}\left(C, u\right) \Rightarrow \left(\forall t \in \operatorname{pure}\left(C, u\right),\; \forall g \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; g\in \operatorname{zeroEffects}\left(C, u, t\right) \Rightarrow \left(\exists v \in \operatorname{pure}\left(C, u\right),\; v\in \operatorname{exclusion}\left(C, u, t\right) \land \left(\forall x \in V,\; x\in \operatorname{base}\left(C, u\right) \Rightarrow \operatorname{apply}\left(g, x\right)\le \operatorname{apply}\left(g, v\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FixedZeroObstruction.zero_effect_maximizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero zero effect, its global maximum is strictly positive because the original pure states span V. Its compact exposed maximum face contains an original pure point. Normalizing by this actual maximum gives a proper confirmer; complementing it puts the same point in the full exclusion of t. For the zero effect, any extreme point of the nonempty compact exclusion is also extreme in K. Thus all indices, including zero effects, admit such a choice.

**Theorem 1.10 (The exact zero and one faces).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\operatorname{StrictPositiveUnit}\left(C, u\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\operatorname{exclusionBalls}\left(C, u\right) \Rightarrow \left(\operatorname{InjectiveExclusionLabels}\left(C, u\right) \Rightarrow \left(\forall s \in \operatorname{pure}\left(C, u\right),\; \forall h \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; h\in \operatorname{fullZeroConfirmers}\left(C, u, s\right) \Rightarrow \left(\operatorname{ZeroFace}\left(\operatorname{base}\left(C, u\right), h\right) = \operatorname{exclusion}\left(C, u, s\right) \land \operatorname{OneFace}\left(\operatorname{base}\left(C, u\right), h\right) = \left\{s\right\}\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FixedZeroObstruction.full_zero_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ZeroFace(K,h) is the set of x in K with h(x)=0; OneFace uses h(x)=1. Any pure one-point v has an exclusion containing the whole exclusion of s. The ball-face theorem and faithful labels force v=s. The one-face is compact, exposed and convex. Krein-Milman makes it the closed convex hull of its extreme points, all of which are the same s. Mixed limit states are therefore included without assuming P closed or finite pure decomposition.

**Theorem 1.11 (The entire-state repair lower bound).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\operatorname{StrictPositiveUnit}\left(C, u\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\operatorname{exclusionBalls}\left(C, u\right) \Rightarrow \left(\forall s \in \operatorname{pure}\left(C, u\right),\; \forall t \in \operatorname{pure}\left(C, u\right),\; \forall h \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; h\in \operatorname{fullZeroConfirmers}\left(C, u, s\right) \Rightarrow \operatorname{divide}\left(\operatorname{subtract}\left(1, \operatorname{faceMaximum}\left(t, h\right)\right), 2\right)\le \operatorname{zeroDistance}\left(C, u, t, h\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FixedZeroObstruction.fixed_zero_distance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any actual g zero at t choose its pure global maximizer v in the full exclusion. Evaluation at s and v is bounded by the continuous-map supremum norm. The resulting inequality is 1 <= max over D(t) of h plus twice the distance between g and h. Taking the infimum over the entire zero-effect image gives the displayed bound. No faithful-label condition is needed for this estimate.

**Theorem 1.12 (One fixed witness per edge implies all-index lifting).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\operatorname{StrictPositiveUnit}\left(C, u\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\operatorname{exclusionBalls}\left(C, u\right) \Rightarrow \left(\operatorname{InjectiveExclusionLabels}\left(C, u\right) \Rightarrow \left(\operatorname{stableZeroWitness}\left(C, u\right) \Rightarrow \operatorname{openEdges}\left(C, u\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FixedZeroObstruction.stable_zero_implies_open_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

stableZeroWitness quantifies every original s,r with r in D(s), then chooses one h in fullZeroConfirmers(s), then quantifies every sequence of original pure t(n) tending to r, and finally chooses proper g(n) zero at each t(n), with stateNorm(g(n)-h) tending to zero. openEdges quantifies every original p,s with s in D(p), every pure t(n) tending to p, and returns pure v(n) in D(t(n)) for every index with v(n) tending to s. Original zero symmetry first reverses the input edge. The repair bound forces the maxima of h on D(t(n)) to tend to one. Pure maximizers exist on every compact exposed face, including every initial index. Compactness of K and the singleton one-face force the full sequence to converge to s. No pure-point closedness, ball continuity, continuous selector, rate, Hilbert representation, or selected effect menu is assumed.

**Theorem 1.13 (A convergent selection belongs to the common whole compact limit).**

Lean statement: `D5/S3/Quantum/Foundation/FixedZeroObstruction.mem_compact_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FixedZeroObstruction.mem_compact_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every normed additive commutative group V, every sequence F(n) and every G of nonempty compact subsets of V, suppose F(n) tends to G in the native nonempty compact topology. For every sequence yn in V and every y in V, if yn(n) belongs to the actual whole F(n) for every n and yn tends to y along those same natural indices, then y belongs to G. No real scalar structure, finite dimensionality, convexity, rank condition or pure state domain is required.

The infimum distance from a point to a nonempty compact set is jointly continuous in the native point and compact-set variables. Evaluating it on the common pair sequence (yn(n),F(n)) gives the constant zero sequence, so the distance from y to G is zero. Compactness makes G closed, which gives membership.

**Theorem 1.14 (Whole-limit labels without closed pure points).**

Lean statement: `D5/S3/Quantum/Foundation/FixedZeroObstruction.exclusion_limit_labels`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FixedZeroObstruction.exclusion_limit_labels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite dimensional real normed V, original closed generating pointed cone C and strictly positive unit u, assume every entire original exclusion has an injective affine closed Euclidean ball chart of positive dimension, with dimensions allowed to vary. For every sequence pn of actual pure points, every x in V with pn(n) tending to x, and every nonempty compact G with hausdorffDist(D(pn(n)),G) tending to zero, the following conjunction holds. If the map from all original pure p to its entire D(p) is injective, then (i) G containing two distinct points forces x to be an actual pure point, and (ii) for every q in V, G={q} and x not pure force q to be actual pure and x to belong to intrinsicInterior(real,D(q)). Independently of that injectivity assumption, if x is actual pure then the entire G is contained in D(x). Membership of x and all of G in the original K is derived, and closedness of the pure locus is never assumed.

Choose an original full zero confirmer for every whole D(pn(n)). Compactness of the entire effect interval gives one convergent effect subsequence. Every point of the same whole compact limit is recovered by nearest points along those indices, so one actual limit effect e satisfies e(x)=1 and vanishes on all G. The existing common_zero_pure declaration in ExclusionWidthCompactness is used directly: two distinct common zeros force the confirmed state pure. For singleton G and mixed x, the compact exposed one-face of e contains an actual pure p distinct from x. The complementary effect u-e confirms q and has the two distinct zeros x,p, so the same original declaration forces q pure. It also places x in the entire D(q). The original chart_boundary identity and intrinsic frontier transport identify the whole relative boundary with the actual pure points of D(q); mixed x therefore lies in its intrinsic interior. The proof uses the closed convex hull and extreme points directly, without an extra finite pure decomposition or an inner product on V.

**Theorem 1.15 (One common edge obstructs every fixed zero test).**

Lean statement: `D5/S3/Quantum/Foundation/FixedZeroObstruction.fixed_zero_distance_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FixedZeroObstruction.fixed_zero_distance_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite dimensional real normed V with the same original closed cone, strict unit and generating hypotheses, assume that every actual pure p has an injective affine chart of the entire D(p) by the closed Euclidean three-ball, and that p mapped to D(p) is injective. For every original pure sequence pn, every x,q in V with pn(n) tending to x and hausdorffDist(D(pn(n)),{q}) tending to zero, there exist actual pure s and r with r in D(s), and one sequence tn of actual pure points tending to r, such that for every fixed original linear h in fullZeroConfirmers(C,u,s), h(tn(n)) tends to zero and the real filter liminf atTop of zeroDistance(hc,hs,tn(n),h) is strictly positive. The existential choices of the edge and entire tn sequence precede the universal h. Only the positive lower bound may depend on h. The norm and zero-effect fiber are exactly the original whole-state objects defined above. Membership of x in K follows from compactness of K; no assumption of O, WZ, closed P, ball continuity, continuous axes, Pair, or an inner product on V is added.

When x is pure, the original pure_pair_in_ball declaration supplies two distinct actual pure points of D(x). Choose s different from q, set r=x and tn=pn, and use original zero symmetry. The full_zero_faces theorem makes s the unique one-point of every fixed complete zero confirmer, including among mixed states. The limit set {q} lies in K and avoids s; compact maxima converge to h(q)<1. This branch never assumes q pure.

When x is mixed, exclusion_limit_labels proves q pure and x in intrinsicInterior(real,D(q)). Choose actual pure tn in D(pn(n)) at every index. Whole-fiber convergence forces tn to q, and original zero symmetry puts pn(n) in D(tn(n)). Native compactness of all nonempty compact subsets of the original K supplies one common strictly increasing index subsequence and one whole compact limit G of these exchanged exclusions. Nearest-point recovery preserves convex combinations, so G is convex; moving-point closure gives x in G, and the pure-label upper graph gives G contained in D(q). This argument imposes no lower bound on a limiting rank or diameter, so point, segment, disk and full-dimensional limits all remain allowed. If G were the whole D(q), the already proved ExclusionIncidence.affine_ball_boundary_limit applies directly to the arbitrary injective three-ball charts of the actual exchanged fibers and D(q). The points pn on their original pure boundaries would force x into the boundary of D(q), contradicting its intrinsic-interior location. Full-rank boundary transport is used only in that equality case. Thus G is a proper subset. Since D(q) is the closed convex hull of its actual pure extreme points, at least one actual pure s of D(q) lies outside the same closed convex G. Set r=q and retain that one exchanged subsequence before considering any h.

For either branch, compactness attains max_G h at an original state. The singleton one-face and s outside G give max_G h<1 for every fixed h. Vietoris upper neighborhoods and nearest-point recovery prove that maxima over the entire moving exclusions converge to max_G h. The existing fixed_zero_distance_bound then bounds the actual zeroDistance from below eventually by (1-max_G h)/4>0. Distance to the actual zero effect supplies a finite upper bound, making the positive real liminf conclusion valid. Continuity gives h(tn(n)) tending to h(r)=0. All subsequences, G, s,r and tn are fixed before h; no test-dependent subsequence is introduced.

These results apply on the entire real normed space of complex Hermitian three by three matrices, with the full positive semidefinite cone and the original trace unit. HermitianExclusionKernel.exclusion_iff_kernel describes the exclusion defined by all original proper real-linear effects, and HermitianExclusionBall.all_pure_charts supplies an injective global affine three-ball chart for every actual extreme point of the entire trace-one base. Closedness of the cone, strict positivity of the trace and generation of the whole real carrier supply the remaining base hypotheses. The carrier is nonzero. Faithfulness follows on the same entire pure carrier: for p=vv*, the density (I-p)/2 lies in D(p); equality D(p)=D(q), with q=ww*, forces pw=w and pq=q. Reversing the labels and taking Hermitian adjoints gives pq=p, hence p=q. Distinct standard basis outer products at indices zero and one give an actual original exclusion edge.

On this common model, zero_effect_maximizer, full_zero_faces and fixed_zero_distance_bound retain every original pure label, every proper real-linear effect and every mixed state in their statements. ExclusionIncidence.original_open_incidence_iff_whole_continuous gives the full equivalences between edge lifting, openness of the first projection and continuity of entire exclusions; its pure-boundary continuity and second-projection openness remain conditional on edge lifting. ExclusionWidthCompactness gives the attained positive whole-effect widths, compact positive and saturated layers, countable width-layer exhaustion and a positive global maximum at an actual original pure label. The width statements use the same three-ball model as an instance of their more general positive-dimensional ball hypothesis.

The remaining case data keep their original quantifiers. stable_zero_implies_open_edges takes the full stableZeroWitness principle as its premise. exclusion_limit_labels quantifies every actual pure input sequence, every ambient limit and every nonempty compact whole-face limit satisfying the stated convergence. fixed_zero_distance_obstruction takes any actual pure sequence with the stated ambient convergence and singleton whole-exclusion collapse; it then selects one actual edge and one actual pure sequence before quantifying every fullZeroConfirmer on that edge. No existence of a collapse sequence or stableZeroWitness is inferred. The mixed-limit width and diameter implications retain their arbitrary convergent sequence and nonpure-limit premise; near_saturation_subsequence retains convergence of the original widths to one, and no_saturation_uniform_gap retains absence of saturation at every original pure label. Boundary transport uses the actual global three-ball charts only when the whole-face limit is the entire D(q).

The mathematical conclusions are conditional on the original geometric hypotheses. They assert no physical realization, reconstruction theorem, global novelty, or empirical claim. The source-bound Reg mirrors retain faithful telescope bridges and actual-positive laws; lawful four-slot registrations remain unfinished.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.exclusion_limit_labels`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.faceMaximum`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.fixed_zero_distance_bound`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.fixed_zero_distance_obstruction`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.fullZeroConfirmers`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.full_zero_faces`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.mem_compact_limit`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.openEdges`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.stableZeroWitness`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.stable_zero_implies_open_edges`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.stateNorm`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.stateReadout`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.zeroDistance`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.zeroEffects`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.zero_effect_maximizer`
- Dependency: [D5/S3/Quantum/Foundation/ExclusionBallFaces](ExclusionBallFaces.md)
- Dependency: [D5/S3/Quantum/Foundation/ExclusionIncidence](ExclusionIncidence.md)
- Dependency: [D5/S3/Quantum/Foundation/ExclusionWidthCompactness](ExclusionWidthCompactness.md)
