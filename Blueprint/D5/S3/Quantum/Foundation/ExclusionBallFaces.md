# Entire exclusion balls and all original proper faces

## Abstract

Nondegenerate entire exclusion balls expose and exhaust the original proper convex faces; proper pure pairs then generate whole balls.

**Theorem 1.1 (Support for an original proper cone face).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallFaces.proper_cone_face_support`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionBallFaces.proper_cone_face_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a generating cone C in any finite-dimensional real normed V, every proper original face F has a nonzero real-linear functional nonnegative on C and zero on F. Neither closedness nor salience is required. The zero set may strictly contain F. NiceConeFaces.every_face_exposed applies this original support theorem in span(E), where its nonzero conclusion is relative to the relevant face span.

**Theorem 1.2 (chart face eq).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallFaces.chart_face_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionBallFaces.chart_face_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an original entire ExclusionChart and a convex extreme subset F of that exclusion, two distinct points of F force F to equal the entire exclusion ball. No closedness of F is assumed. OrthogonalJointCompletion.pair_geometry applies this to the entire intersection of the two exclusion faces.

**Theorem 1.3 (pair convex).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallFaces.pair_convex`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionBallFaces.pair_convex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The whole original pairBase is convex, because the original base and every native cone face containing both points are convex. OrthogonalJointCompletion.pair_geometry consumes the original declaration before applying the paid proper-face classification.

The original finite dimensional real normed carrier V has a closed generating cone C and a real-linear unit u strictly positive on every nonzero cone vector. Strict positivity excludes nonzero lines. K is the entire normalized base, P consists of all its extreme points, and proper effects are all real-linear f with 0<=f<=u on C. No finite or closed pure carrier, restricted effect menu, least effect, Jordan representation, projectivity or effect extension is an input. The argument also covers the zero carrier whenever its hypotheses hold.

**Definition 1.4 (A whole nondegenerate exclusion ball).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallFaces.ExclusionChart`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionBallFaces.ExclusionChart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a specified original point p, the chart has a natural dimension d>0, an affine map from EuclideanSpace R (Fin d) to V, injectivity on the entire Euclidean space, and equality of the image of the entire closed unit ball with exclusion(C,u,p). These are its only fields. Dimension one, giving a line segment, is included. Facial structure and exposedness are conclusions.

**Definition 1.5 (The entire mixed-state ball condition).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{exclusionBalls}\left(C, u\right) \Leftrightarrow \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \operatorname{Nonempty}\left(\operatorname{ExclusionChart}\left(C, u, p\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionBallFaces.exclusionBalls` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original pure p there is such a chart of its full original exclusion set. A mixed state x belongs to that set precisely when x belongs to K and some original proper confirmer f of p has f(x)=0. The confirmer may initially depend on x.

**Definition 1.6 (Properness of every whole pure-pair face).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{pairProper}\left(C, u\right) \Leftrightarrow \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall q \in \operatorname{pure}\left(C, u\right),\; p\neq q \Rightarrow \operatorname{pairBase}\left(C, u, p, q\right)\neq \operatorname{base}\left(C, u\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionBallFaces.pairProper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

pairBase is the existing intersection of the entire original base with every native cone face containing both p and q. Properness compares this whole set with K. It does not compare a selected slice or only the segment joining the two points.

**Theorem 1.7 (Common exposure, all-face exhaustion and entire pair balls).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall x \in V,\; x\in C \Rightarrow \left(x\neq 0 \Rightarrow 0< \operatorname{apply}\left(u, x\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\operatorname{exclusionBalls}\left(C, u\right) \Rightarrow \left(\left(\forall p \in \operatorname{pure}\left(C, u\right),\; \operatorname{Nontrivial}\left(\operatorname{exclusion}\left(C, u, p\right)\right) \land \left(\operatorname{IsCompact}\left(\operatorname{exclusion}\left(C, u, p\right)\right) \land \left(\operatorname{Convex}\left(\mathbb{R}, \operatorname{exclusion}\left(C, u, p\right)\right) \land \left(\operatorname{IsExposed}\left(\mathbb{R}, \operatorname{base}\left(C, u\right), \operatorname{exclusion}\left(C, u, p\right)\right) \land \left(\operatorname{IsExtreme}\left(\mathbb{R}, \operatorname{base}\left(C, u\right), \operatorname{exclusion}\left(C, u, p\right)\right) \land \left(\operatorname{exclusion}\left(C, u, p\right)\neq \operatorname{base}\left(C, u\right) \land \left(\exists f \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{confirms}\left(C, u, p, f\right) \land \operatorname{exclusion}\left(C, u, p\right) = \operatorname{inter}\left(\operatorname{base}\left(C, u\right), \operatorname{ker}\left(f\right)\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\forall F \in \operatorname{Set}\left(V\right),\; \operatorname{Nonempty}\left(F\right) \Rightarrow \left(\operatorname{Convex}\left(\mathbb{R}, F\right) \Rightarrow \left(\operatorname{IsExtreme}\left(\mathbb{R}, \operatorname{base}\left(C, u\right), F\right) \Rightarrow \left(F\neq \operatorname{base}\left(C, u\right) \Rightarrow \left(\left(\exists p \in \operatorname{pure}\left(C, u\right),\; F = \left\{p\right\}\right) \lor \left(\exists p \in \operatorname{pure}\left(C, u\right),\; F = \operatorname{exclusion}\left(C, u, p\right)\right)\right)\right)\right)\right)\right) \land \left(\operatorname{pairProper}\left(C, u\right) \Rightarrow \left(\left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall q \in \operatorname{pure}\left(C, u\right),\; p\neq q \Rightarrow \left(\exists r \in \operatorname{pure}\left(C, u\right),\; \operatorname{pairBase}\left(C, u, p, q\right) = \operatorname{exclusion}\left(C, u, r\right)\right)\right) \land \operatorname{wholePairBalls}\left(C, u\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionBallFaces.exclusion_ball_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each full exclusion set is nonpoint, compact, convex, exposed and extreme in K, and differs from K. One original proper confirmer cuts it out exactly as K intersect ker(f); inter denotes set intersection. Every nonempty proper original convex face is either an original pure singleton or an entire exclusion ball. There is no closed-face premise. If pairProper also holds, each whole minimal face of distinct pure points equals an entire exclusion set, and the existing wholePairBalls predicate follows.

Convexity of each entire exclusion ball implies original mixed-state midpoint gluing. The existing zero_gluing_common_effect then produces one original confirmer vanishing on every exclusion. Its negative functional exposes that full set, while confirmation at p makes the face proper. Compactness and nonpointness come directly from the full nondegenerate ball chart.

The existing base_face_lift identifies any convex face of K with the entire normalized slice of an original cone face, without assuming closedness. A proper cone face misses the cone interior: if it contained an interior point, extension of each original direction to an open segment would force it to contain the whole cone. The generating condition gives nonempty cone interior, so geometric Hahn-Banach supplies a nonzero functional nonnegative on the entire cone and zero on that entire face. A compact exposed maximum face contains an original pure maximizer. Dividing the functional by that strictly positive maximum gives one original proper confirmer and places the initial face inside its full exclusion set.

Pull the original face back through the injective affine ball chart. If it contains two distinct points, their midpoint is interior to the entire strictly convex ball. A face containing an interior point is the whole ball. This holds in dimension one as well. A remaining singleton is pure because it is itself an extreme subset of K. Under pairProper, the entire original pair base is a nonpoint proper convex face, so the classification identifies it with a full exclusion ball and transports the existing BallChart without replacing the minimal face.

The exposing confirmer is not asserted to be least. Reciprocal pure values, point-ball duality, rank-three or Jordan reconstruction, Born rules, composites and physical realization require their separate mathematical and operational premises. The result is a consequence within the original finite dimensional full-effect model; no literature priority is asserted.

## Application: all original states and every radial chart

This application combines the existing face classification with the base, support, frontier and chart-boundary results and pinned Mathlib convex geometry. Take a nonzero finite-dimensional real normed V, the entire closed generating pointed cone C, and a real-linear u strictly positive on C except at zero. K is the entire base C intersect u=1; P is every extreme point of K; the effect domain is every real-linear f satisfying 0<=f(c)<=u(c) for all c in C. Assume exclusionBalls: every p in P admits at least one ExclusionChart of its entire actual D(p). Every such chart is an injective affine map of a whole closed Euclidean unit ball of finite dimension d>0. Dimensions may vary and d=1 is included. The additional hypothesis Inj says only that D(p)=D(q) implies p=q. No pairProper, W, closed pure locus, continuous selector, common center or matrix-cone premise is used.

For these parameters, every original x in K admits p in P, y in the whole D(p), and 0<=lambda<=1 with x=lambda p+(1-lambda)y. If this same x is in the intrinsic interior of K, the choices can satisfy 0<lambda<1 and one original proper effect f with f(p)=1 and f(y)=0. Consequently K is exactly the union, over all original p in P, of the convex hull of {p} union D(p). Moreover, for the same selected y and every complete chart b at p, there are q,r in P intersect D(p) and 0<=theta<=1 with y=theta q+(1-theta)r and r=2 b(0)-q. Substitution gives x=lambda p+(1-lambda)(theta q+(1-theta)r). These are consequences of the jointly reused results, rather than a separately admitted theorem.

CircuitBalancedConfirmation.base_compact, base_convex, pure_mem and pure_span keep K compact and convex, retain the original pure carrier and exclude its collapse in the nonzero generating model. ExclusionWidthCompactness.comparison_zero_iff identifies each full D(p), on every original normalized state, with zero minimum comparison readback; the minimum over all original confirming effects is attained. Thus the existential full-effect exclusion used here agrees with the original readback, including mixed states. It changes neither the state domain nor the available effect interval.

For an intrinsic interior x, translate K to zero in the direction space of its affine span: L consists of the direction vectors v with x+v in K. The native affine equivalence transports compactness, convexity and intrinsic interior to a compact convex neighborhood of zero in that direction space. It has a nonzero direction: the positive-dimensional whole exclusion charts prevent K from being a singleton. The classical affine-diameter existence assertion is reported by Bárány, Hug and Schneider, Affine diameters of convex bodies, Sections 1 and 5, arXiv:1403.7158v2, DOI 10.1090/proc12746, citing Soltan assertion 3.3. Section 1 defines the endpoints by distinct parallel supporting hyperplanes; Section 5, in the paragraph beginning Concerning the left-hand inequality in (1.4), explicitly reports that every point of a convex body belongs to an affine diameter and cites assertion 3.3 of V. Soltan, Affine diameters of convex bodies: a survey, Expositiones Mathematicae 23 (2005), 47-63, bibliography item [9]. The primary locators are https://arxiv.org/html/1403.7158v2#S1 and https://arxiv.org/html/1403.7158v2#S5 and DOI 10.1090/proc12746. This citation uses the existence assertion reported by Bárány, Hug and Schneider; it does not claim separate inspection of Soltan’s text. No paper text or scan is redistributed. No counting theorem, smoothness or general-relative-position hypothesis is imported.

For the normalized inference, Mathlib IsCompact.exists_isMaxOn maximizes the reflected gauge z maps to gauge L (-z) on L. Positivity, homogeneity and the closure and frontier characterizations of the gauge give a positive tau and b in L with a=-tau b on the frontier and -tau L contained in L. The pinned geometric_hahn_banach_of_nonempty_interior_point supplies one nonzero supporting functional h at a. Its maximum M=h(a) is strictly positive because zero is interior. For every z in L, the same support inequality at -tau z gives h(z)>=h(b)=m, with m=-M/tau<0. Hence a and b realize the two support values of that same functional, and zero=(a+tau b)/(1+tau). These are joint applications and scalar normalization of existing compactness, gauge and separation facts; no single identically shaped upstream theorem is asserted.

Extend h from the direction subspace to a real-linear H on V using LinearMap.exists_extend. Put A=x+a and B=x+b. On the whole original V define f(xi)=(H(xi)-(H(x)+m)u(xi))/(M-m). For every k in K, the support bounds on k-x prove 0<=f(k)<=1; the two actual endpoints satisfy f(A)=1 and f(B)=0. CircuitBalancedConfirmation.cone_bound extends both halfspace inequalities from all original pure points to every c in C. Equivalently, for nonzero c write c=u(c)k with u(c)>0 and k in K; linearity gives 0<=f(c)<=u(c), while c=0 is immediate. Thus this is one full original proper effect with both endpoint readings, with no remaining effect-extension premise.

The support faces F0=K intersect ker(f) and F1={k in K : f(k)=1} are nonempty compact proper faces. ExclusionBallFaces.exclusion_ball_faces classifies F0 as an original pure singleton or an entire D(s), without a closed-face input. In the singleton case B=p and the complementary original effect u-f confirms p and vanishes at A. In the whole-ball case an extreme point t of F1 is an original pure point. Its same confirming f gives D(s) contained in D(t); ExclusionBallFaces.chart_face_eq and nonpointness give equality. Inj identifies t=s, and FixedZeroObstruction.full_zero_faces identifies F1 with {s}. Hence A=p and B belongs to the whole D(p). When A=p use f and lambda=1/(1+tau); when B=p use u-f and lambda=tau/(1+tau). Both pure weights are strictly between zero and one.

For a state outside the intrinsic interior, compactness identifies the intrinsic frontier. MixedExclusionGeometry.frontier_covered places it in a full D(p); take y=x and lambda=0. Its frontier_covered theorem has no weakPair input. One may also treat a pure x by p=x, lambda=1 and any member of its nonempty D(p). The reverse union containment uses only base_convex and pure_mem, since both p and the entire D(p) lie in K. No limit over moving pure labels or compactness of all P is required.

For every specified complete chart b at the selected p, pull y back to a coordinate v with norm at most one. If v is nonzero, take n=v/||v|| and theta=(1+||v||)/2; then v=theta n+(1-theta)(-n). If v=0, the positive chart dimension supplies a unit coordinate vector n and theta=1/2. Set q=b(n), r=b(-n). Affinity gives both the decomposition and r=2 b(0)-q. OriginalFacePolarity.chart_boundary puts both endpoints in the original P intersect D(p). This construction applies to every chart, including its center and its boundary, without a continuous chart choice or a common center across exclusions.

Each of q and r belongs to the same entire D(p), so each has a proper original effect distinguishing it from p. This conclusion does not supply an effect distinguishing q from r, a joint three-result test, state spectrality, an EJA representation, dynamics or physical instruments. Those claims retain their separate mathematical and operational premises. The application is an existing-result synthesis; the literature citation supplies classical provenance and no novelty is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallFaces.ExclusionChart`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallFaces.chart_face_eq`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallFaces.exclusionBalls`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallFaces.exclusion_ball_faces`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallFaces.pairProper`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallFaces.pair_convex`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallFaces.proper_cone_face_support`
- Dependency: [D5/S3/Quantum/Foundation/FacetZeroGluing](FacetZeroGluing.md)
- Dependency: [D5/S3/Quantum/Foundation/WholePairBallConfirmation](WholePairBallConfirmation.md)
