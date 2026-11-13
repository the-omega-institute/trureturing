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
