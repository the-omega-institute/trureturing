# Finite common source tests on the whole original positive cone

## Abstract

Finite common source tests force an original positive-lift error or an increase of the return ball's intrinsic affine dimension.

**Theorem 1.1 (Directions of the whole affine ball).**

Lean statement: `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.ball_affine_span`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.ball_affine_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real normed E and V and any affine a:E to V, the direction of the affine span of a(closedBall(0,1)) equals the linear range of a. The entire source ball affinely spans E. This identifies the dimension and direction of the actual reflected original ball.

**Theorem 1.2 (Relative interiors under injective affine maps).**

Lean statement: `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.intrinsic_interior_image`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.intrinsic_interior_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite dimensional real normed E, any real normed target V, every injective affine a:E to V and every subset s of E, the intrinsic interior of a(s) equals a applied to the intrinsic interior of s. Restricting a to its affine range gives an affine equivalence. The center and reflected affine balls use this intrinsic topology transport.

The source is QUANTUM_ORIGIN_LOCAL_PURE_LIMIT_AND_COMMON_POSITIVE_LIFTS_CONTINUATION, 132.1--132.4. V is an arbitrary finite dimensional real normed space; C is the entire closed generating pointed cone; u is strictly positive on its nonzero vectors. K is its whole normalized base, P all original extreme points, and effects the complete interval [0,u] on C. Every entire original exclusion D(t) is a positive dimensional affine Euclidean closed ball; dimensions may vary and segments are included. All distances and dual norms use the supplied original norm. No global injectivity, fixed dimension, closedness of P, common inner product or continuous choice of charts is assumed.

**Definition 1.3 (Maximum on the whole original K).**

Lean statement: `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.baseMaximum`

*Formalization.* `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.baseMaximum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

baseMaximum(b)=sup b(K); compactness gives the actual maximum. For positive b it is exactly the supremum norm of the original stateReadout on all K.

**Definition 1.4 (Whole-ball upper displacement).**

Lean statement: `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.upperDisplacement`

*Formalization.* `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.upperDisplacement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

upperDisplacement(p,t)=max over x in the entire D(t) of infDist(x,D(p)). The notation upperDisplacementAt(p) in the formula means t mapped to this number.

**Definition 1.5 (Restriction to all of F).**

Lean statement: `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.sourceReadout`

*Formalization.* `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.sourceReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sourceReadout(p,b) is the continuous real function x mapped to b(x) on all F=D(p). Its supremum norm is a seminorm on ambient linear functionals. No quotient identifying different original states is imposed.

**Definition 1.6 (The original global unit normalization).**

Lean statement: `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.normalizePositive`

*Formalization.* `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.normalizePositive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

normalizePositive(b)=b/max(1,baseMaximum(b)), using scalar multiplication on the original dual space and the entire original state body.

**Definition 1.7 (Distance to the entire positive zero cone).**

Lean statement: `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.sourceDistance`

*Formalization.* `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.sourceDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sourceDistance(p,t,h)=inf over every b positive on ALL C and exactly zero at this SAME t of max over x in ALL F of abs(b(x)-h(x)). It is infDist from sourceReadout(p,h) to the restriction image of CommonPositiveExtension.zeroPositive(C,u,t) in C(F,R). Zero makes this image nonempty. It need not be closed; no attainment is assumed. There is no b<=u restriction and no pointwise or label-dependent patchwork.

**Theorem 1.8 (132.2: all moving positive annihilators share one control).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall z \in V,\; z\in C \Rightarrow \left(z\neq 0 \Rightarrow 0 < \operatorname{apply}\left(u, z\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\operatorname{exclusionBalls}\left(C, u\right) \Rightarrow \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \exists A \in \mathbb{R},\; 0 < A \land \left(\left(\forall b \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{dualNorm}\left(b\right) \le \operatorname{mul}\left(A, \operatorname{stateNorm}\left(C, u, b\right)\right)\right) \land \left(\operatorname{Tendsto}\left(\operatorname{upperDisplacementAt}\left(p\right), \operatorname{nhds}\left(p\right), \operatorname{nhds}\left(0\right)\right) \land \left(\forall t \in \operatorname{pure}\left(C, u\right),\; \operatorname{mul}\left(A, \operatorname{upperDisplacement}\left(p, t\right)\right) < 1 \Rightarrow \left(\forall b \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \left(\forall z \in V,\; z\in C \Rightarrow 0 \le \operatorname{apply}\left(b, z\right)\right) \Rightarrow \left(\operatorname{apply}\left(b, t\right) = 0 \Rightarrow \operatorname{baseMaximum}\left(C, u, b\right) \le \operatorname{div}\left(\operatorname{faceMaximum}\left(p, b\right), \operatorname{sub}\left(1, \operatorname{mul}\left(A, \operatorname{upperDisplacement}\left(p, t\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.moving_positive_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One A>0 bounds the supplied original dual norm by A times the whole-K norm for EVERY signed linear b. The entire compact K spans V, so its restriction map is injective and the pinned finite dimensional antilipschitz theorem supplies A. Pure-label upper incidence gives alpha(p,t)->0 at p, with no singleton-label premise. For every t with A alpha(p,t)<1 and EVERY positive b with b(t)=0, max_K b <= max_F b/(1-A alpha(p,t)). The existing positive_annihilator_maximum places a global maximum in D(t). Its nearest point in the same F and the dual estimate give the inequality; the zero functional is included.

**Theorem 1.9 (132.2: normalize every unbounded positive sequence).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall z \in V,\; z\in C \Rightarrow \left(z\neq 0 \Rightarrow 0 < \operatorname{apply}\left(u, z\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\operatorname{exclusionBalls}\left(C, u\right) \Rightarrow \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall t \in \operatorname{Function}\left(\mathbb{N}, \operatorname{pure}\left(C, u\right)\right),\; \operatorname{Tendsto}\left(t, \operatorname{atTop}\left(\right), \operatorname{nhds}\left(p\right)\right) \Rightarrow \left(\forall b \in \operatorname{Function}\left(\mathbb{N}, \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right)\right),\; \left(\forall n \in \mathbb{N},\; \forall z \in V,\; z\in C \Rightarrow 0 \le \operatorname{apply}\left(\operatorname{apply}\left(b, n\right), z\right)\right) \Rightarrow \left(\left(\forall n \in \mathbb{N},\; \operatorname{apply}\left(\operatorname{apply}\left(b, n\right), \operatorname{apply}\left(t, n\right)\right) = 0\right) \Rightarrow \left(\forall ell \in \operatorname{Function}\left(\operatorname{exclusion}\left(C, u, p\right), \mathbb{R}\right),\; \left(\forall x \in \operatorname{exclusion}\left(C, u, p\right),\; 0 \le \operatorname{apply}\left(ell, x\right) \land \operatorname{apply}\left(ell, x\right) \le 1\right) \Rightarrow \left(\operatorname{TendstoUniformly}\left(\operatorname{restrictions}\left(p, b\right), ell, \operatorname{atTop}\left(\right)\right) \Rightarrow \left(\left(\forall n \in \mathbb{N},\; \operatorname{proper}\left(C, u, \operatorname{normalizePositive}\left(C, u, \operatorname{apply}\left(b, n\right)\right)\right) \land \operatorname{apply}\left(\operatorname{normalizePositive}\left(C, u, \operatorname{apply}\left(b, n\right)\right), \operatorname{apply}\left(t, n\right)\right) = 0\right) \land \left(\operatorname{Tendsto}\left(\operatorname{normalizationGaps}\left(C, u, b\right), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(0\right)\right) \land \left(\operatorname{TendstoUniformly}\left(\operatorname{normalizedRestrictions}\left(p, b\right), ell, \operatorname{atTop}\left(\right)\right) \land \left(\operatorname{sSup}\left(\operatorname{range}\left(ell\right)\right) = 1 \Rightarrow \operatorname{Tendsto}\left(\operatorname{baseMaxima}\left(C, u, b\right), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(1\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.moving_positive_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original pure t(n)->p and every b(n) positive on all C and zero at t(n), suppose restrictions to all F converge uniformly to any ell:F->[0,1]. Continuity of ell is derived. With B(n)=max_K b(n), f(n)=b(n)/max(1,B(n)), every f(n) is an original proper effect, f(n)(t(n))=0, the whole-K norm of f(n)-b(n) tends to zero, and restrictions f(n)|F converge uniformly to the same ell. If sup_F ell=1, B(n)->1. The proof in fact sandwiches B(n) to the supremum norm of ell. In the formula, restrictions, normalizedRestrictions, normalizationGaps and baseMaxima denote these exact sequences, and values denotes subtype coercion into V. No bound on b(n), unit budget, singleton assumption or moving chart continuity is inserted.

**Theorem 1.10 (132.3: entire exclusions shrink to the local label).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall z \in V,\; z\in C \Rightarrow \left(z\neq 0 \Rightarrow 0 < \operatorname{apply}\left(u, z\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\operatorname{exclusionBalls}\left(C, u\right) \Rightarrow \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \operatorname{SingleLabel}\left(C, u, p\right) \Rightarrow \left(\forall y \in V,\; y\in \operatorname{intrinsicInterior}\left(\mathbb{R}, \operatorname{exclusion}\left(C, u, p\right)\right) \Rightarrow \left(\forall r \in \operatorname{Function}\left(\mathbb{N}, \operatorname{pure}\left(C, u\right)\right),\; \operatorname{Tendsto}\left(\operatorname{values}\left(r\right), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(y\right)\right) \Rightarrow \left(\forall epsilon \in \mathbb{R},\; 0 < epsilon \Rightarrow \left(\exists j \in \mathbb{N},\; \forall n \in \mathbb{N},\; j \le n \Rightarrow \left(\forall x \in V,\; x\in \operatorname{exclusion}\left(C, u, \operatorname{apply}\left(r, n\right)\right) \Rightarrow \operatorname{norm}\left(\operatorname{sub}\left(x, p\right)\right) < epsilon\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.single_label_mixed_shrinking` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume only I(F)={p}, expressed by SingleLabel(C,u,p), and y in the relative interior of F. Any hypothetical original pure sequence r(n)->y forces EVERY mixed x in D(r(n)) eventually within each positive epsilon of p. Complete common confirmers and compactness of the entire effect interval give one limiting effect equal to one on all F. Two distinct actual pure sphere points in F have different complete exclusions by single_label_neighbor, including dimension one. Two-point face rigidity then forces every exclusion cluster point to be p. Compactness upgrades this to uniform shrinking of the entire fibers. No injectivity criterion is applied to the mixed y and no such pure sequence is asserted to exist.

**Theorem 1.11 (132.4: positive source error or intrinsic dimension increase).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall z \in V,\; z\in C \Rightarrow \left(z\neq 0 \Rightarrow 0 < \operatorname{apply}\left(u, z\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\operatorname{exclusionBalls}\left(C, u\right) \Rightarrow \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \operatorname{SingleLabel}\left(C, u, p\right) \Rightarrow \left(\forall y \in V,\; y\in \operatorname{intrinsicInterior}\left(\mathbb{R}, \operatorname{exclusion}\left(C, u, p\right)\right) \Rightarrow \left(\exists m \in \mathbb{N},\; 0 < m \land \left(\exists a \in \operatorname{Function}\left(\operatorname{Fin}\left(m\right), \operatorname{pure}\left(C, u\right)\right),\; \exists h \in \operatorname{Function}\left(\operatorname{Fin}\left(m\right), \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(m\right),\; \operatorname{apply}\left(a, i\right)\in \operatorname{exclusion}\left(C, u, p\right) \land \operatorname{apply}\left(h, i\right)\in \operatorname{fullZeroConfirmers}\left(C, u, \operatorname{apply}\left(a, i\right)\right)\right) \land \left(\left(\exists epsilon \in \mathbb{R},\; \exists delta \in \mathbb{R},\; 0 < epsilon \land \left(0 < delta \land \left(\forall r \in \operatorname{pure}\left(C, u\right),\; \operatorname{norm}\left(\operatorname{sub}\left(r, y\right)\right) < epsilon \Rightarrow \left(\forall t \in \operatorname{pure}\left(C, u\right),\; t\in \operatorname{exclusion}\left(C, u, r\right) \Rightarrow \left(\operatorname{add}\left(\operatorname{affdim}\left(\operatorname{exclusion}\left(C, u, p\right)\right), 1\right) \le \operatorname{affdim}\left(\operatorname{exclusion}\left(C, u, t\right)\right) \lor \left(\exists i \in \operatorname{Fin}\left(m\right),\; delta \le \operatorname{sourceDistance}\left(C, u, p, t, \operatorname{apply}\left(h, i\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\forall tau \in \mathbb{R},\; 0 < tau \Rightarrow \left(\exists epsilon \in \mathbb{R},\; 0 < epsilon \land \left(\forall r \in \operatorname{pure}\left(C, u\right),\; \operatorname{norm}\left(\operatorname{sub}\left(r, y\right)\right) < epsilon \Rightarrow \left(\forall t \in \operatorname{pure}\left(C, u\right),\; t\in \operatorname{exclusion}\left(C, u, r\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(m\right),\; \operatorname{apply}\left(\operatorname{apply}\left(h, i\right), t\right) \le tau\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.finite_common_source_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are m>0 actual pure a(i) in F and fixed complete original h(i) in A(a(i)), chosen before ALL original r,t, and epsilon,delta>0. For every pure r with original norm distance to y less than epsilon and every pure t in the entire D(r), either affdim D(t)>=affdim F+1 or some sourceDistance(p,t,h(i))>=delta. Since Fin m is finite and nonempty, this last clause is exactly max_i R_F(t,h(i))>=delta. affdim means the real finrank of the direction of the actual affine span, not a chart certificate. For EVERY tau>0 a possibly different positive epsilon gives ALL h(i)(t)<=tau simultaneously for every such r,t, with the same finite family, source F and return t.

A finite simplex around the coordinate of y fits in the open ball. Each simplex vertex belongs to the convex hull of the entire sphere, so finite sphere subsets give a finite actual pure family spanning F with y in the relative interior of its convex hull. Local singleton propagation applies to every a(i). Any chosen full zero confirmer has whole original one-face exactly {a(i)}: proper face maximality identifies every pure one-point, and the compact exposed top face is the closed convex hull of its extreme points. Original zero symmetry gives h(i)(p)=0.

A failure of the uniform obstruction produces a SAME r(n),t(n) for all tests with r(n)->y, t(n) in D(r(n)), actual affdim D(t(n))<=k, and every source distance tending to zero. Selection from the infimum gives positive b(i,n) zero at this same t(n) with uniform whole-F error tending to zero, without minimizers. The entire-fiber shrinking gives t(n)->p. Moving positive normalization yields proper f(i,n) with the same source limits. Original pure maxima lie in the SAME entire D(t(n)); compact joint limits of effects and states, upper incidence, and the singleton whole one-face force x(i,n)->a(i).

Extract one subsequence of constant positive integer dimension d<=k. Compactness of K gives a whole-ball Hausdorff limit H and the ORIGINAL parameter_subsequence theorem gives a further common convergent center and linear map, with H=c+L(closed unit ball). Upper incidence gives H subset F. Every finite a(i) lies in H; therefore affineSpan H=affineSpan F and rank L=k. Since rank L<=d<=k, d=k and L is injective. ONLY NOW the existing affine_ball_boundary_limit theorem transports the pure r(n), which lie on those same return spheres, to the relative boundary of H. The finite convex hull lies in H and has that same affine span, so y is also in the relative interior of H, a contradiction. No boundary claim is made for a rank-collapsed map. Centers and arbitrary chart maps are controlled through their entire images, so no common axes or continuous chart choices are assumed.

132.5 remains a boundary: this proves neither LP(p,y), existence of an original pure sequence approaching the mixed y, existence of common positive lifts, resolution of repeated balls, nor a complete EB countermodel. A maximal dimension F removes only the dimension-increase branch; no arbitrary specified F is replaced by a maximal one, and the source-error branch remains. Separate return labels for separate tests do not meet the same-label requirement. The whole-K effect-distance obstruction with global injectivity and fixed dimension is not used as a bridge to this stronger source-F positive-cone distance. The result is repository-derived, with no global originality or physical-realization claim.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.ball_affine_span`
- Truth anchor: `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.baseMaximum`
- Truth anchor: `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.finite_common_source_obstruction`
- Truth anchor: `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.intrinsic_interior_image`
- Truth anchor: `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.moving_positive_control`
- Truth anchor: `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.moving_positive_normalization`
- Truth anchor: `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.normalizePositive`
- Truth anchor: `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.single_label_mixed_shrinking`
- Truth anchor: `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.sourceDistance`
- Truth anchor: `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.sourceReadout`
- Truth anchor: `D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.upperDisplacement`
- Dependency: [D5/S3/Quantum/Foundation/CommonPositiveExtension](CommonPositiveExtension.md)
- Dependency: [D5/S3/Quantum/Foundation/ExclusionIncidence](ExclusionIncidence.md)
- Dependency: [D5/S3/Quantum/Foundation/FixedZeroObstruction](FixedZeroObstruction.md)
- Dependency: [D5/S3/Quantum/Foundation/UniqueConfirmationDensity](UniqueConfirmationDensity.md)
