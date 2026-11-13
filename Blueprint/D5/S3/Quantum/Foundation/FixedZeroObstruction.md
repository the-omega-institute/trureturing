# Fixed zero effects on the entire original state body

## Abstract

Entire original zero effects attain their global maximum in the exclusion face, and fixed qualitative witnesses lift all original orthogonal edges.

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

These implications apply in particular when every exclusion has dimension three. They do not establish the rank-zero collapse obstruction: the mixed-label branch still requires purity of the collapsed point, relative-interior location of the mixed label, and a proper limit of the exchanged whole balls selected before all fixed tests. No reconstruction, physical operation, or literature priority is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.faceMaximum`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.fixed_zero_distance_bound`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.fullZeroConfirmers`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.full_zero_faces`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.openEdges`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.stableZeroWitness`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.stable_zero_implies_open_edges`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.stateNorm`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.stateReadout`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.zeroDistance`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.zeroEffects`
- Truth anchor: `D5/S3/Quantum/Foundation/FixedZeroObstruction.zero_effect_maximizer`
- Dependency: [D5/S3/Quantum/Foundation/ExclusionBallFaces](ExclusionBallFaces.md)
