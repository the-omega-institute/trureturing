# Independent extreme-point tests in a polyhedral Banach plane

## Abstract

A complete real Banach plane refutes the assertion that any independent extreme-point basis detects scalar isometries in every polyhedral space.

Manna, Mandal, Paul and Sain, arXiv:2511.20345v1, final Open Question: “Open Question: In an n-dimensional polyhedral Banach space, does the preservation of Birkhoff-James orthogonality by a bounded linear operator at any n linearly independent extreme points necessarily imply that the operator is a scalar multiple of an isometry?” The standing field is real or complex. Preservation at a point quantifies every direction, with every scalar of the base field in each orthogonality inequality.

**Definition 1.1 (The source assertion over one field).**

$$\operatorname{fieldClaim}\left(K\right) \Leftrightarrow (\forall E: Type, \forall n: \mathbb{N}, \forall v: \operatorname{Function}\left(\operatorname{Fin}\left(n\right), E\right), \forall T: \operatorname{ContinuousLinearMap}\left(K, E, E\right), (((\operatorname{CompleteNormedSpace}\left(K, E\right)) \land (\operatorname{FiniteDimensional}\left(K, E\right))) \land ((\operatorname{finrank}\left(K, E\right) = n) \land ((\operatorname{Finite}\left(\operatorname{extremePoints}\left(\mathbb{R}, \operatorname{closedBall}\left(0, 1\right)\right)\right)) \land ((\operatorname{LinearIndependent}\left(K, v\right)) \land (\forall i: \operatorname{Fin}\left(n\right), (v\left(i\right) \in \operatorname{extremePoints}\left(\mathbb{R}, \operatorname{closedBall}\left(0, 1\right)\right)) \land (\left\lVert v\left(i\right) \right\rVert = 1)))))) \Rightarrow ((\forall i: \operatorname{Fin}\left(n\right), \forall y: E, (\forall t: K, \left\lVert v\left(i\right) \right\rVert \le \left\lVert v\left(i\right) + t \cdot y \right\rVert) \Rightarrow (\forall t: K, \left\lVert T\left(v\left(i\right)\right) \right\rVert \le \left\lVert T\left(v\left(i\right)\right) + t \cdot T\left(y\right) \right\rVert)) \Rightarrow (\exists c: K, \exists U: \operatorname{LinearIsometry}\left(K, E, E\right), T = c \cdot \operatorname{toContinuousLinearMap}\left(U\right))))$$

*Formalization.* `D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.fieldClaim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Manna; K. Mandal; K. Paul; D. Sain (2025). *An improvement of the Blanco-Koldobsky-Turnšek characterization of isometries*. URL: <https://arxiv.org/abs/2511.20345v1>.

*Commentary.*

For a scalar field K with RCLike structure, fieldClaim K quantifies every complete finite-dimensional normed K-space E, every natural dimension n equal to finrank K E, every independent tuple v indexed by Fin n of actual extreme unit points, and every continuous linear endomorphism T. The polyhedral premise is finiteness of the native real-convex extremePoints of Metric.closedBall 0 1, using the real structure obtained by restricting scalars. At every selected vᵢ and for every y, the all-K-scalar input inequality implies the all-K-scalar output inequality. The conclusion is literal equality T = c • U.toContinuousLinearMap for one unrestricted c in K and a native K-linear isometry U. The scalar zero is included. The tuple is chosen before T; preservation at all independent tuples is not assumed.

**Definition 1.2 (The complete real-or-complex assertion).**

$$claim \Leftrightarrow ((\operatorname{fieldClaim}\left(\mathbb{R}\right)) \land (\operatorname{fieldClaim}\left(\mathbb{C}\right)))$$

*Formalization.* `D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Manna; K. Mandal; K. Paul; D. Sain (2025). *An improvement of the Blanco-Koldobsky-Turnšek characterization of isometries*. URL: <https://arxiv.org/abs/2511.20345v1>.

*Commentary.*

The closed proposition is the conjunction of the real and complex instances of fieldClaim. It has no free space, dimension, tuple, operator or scalar parameter. One legal real instance suffices to refute this conjunction; no complex counterexample is needed.

**Definition 1.3 (The three-reading plane).**

$$facetPlane = \operatorname{setOf}\left(w\left(2\right) = w\left(1\right) - \frac{w\left(0\right)}{2}\right)$$

*Formalization.* `D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.facetPlane` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Manna; K. Mandal; K. Paul; D. Sain (2025). *An improvement of the Blanco-Koldobsky-Turnšek characterization of isometries*. URL: <https://arxiv.org/abs/2511.20345v1>.

*Commentary.*

The submodule of Fin 3 → ℝ is defined by w₂ = w₁ − w₀/2. It inherits the actual sup norm, metric and real normed-space structure from this ambient space. Its unit ball is a section of the cube; its extreme points are proved inside the section, rather than identified with the ambient cube vertices.

**Definition 1.4 (The complete normed carrier).**

$$Plane = facetPlane$$

*Formalization.* `D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.Plane` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Manna; K. Mandal; K. Paul; D. Sain (2025). *An improvement of the Blanco-Koldobsky-Turnšek characterization of isometries*. URL: <https://arxiv.org/abs/2511.20345v1>.

*Commentary.*

Plane is the subtype of facetPlane. Submodules of finite-dimensional real spaces are finite dimensional. The coordinate equivalence below proves finrank ℝ Plane = 2; finite-dimensional completeness supplies CompleteSpace Plane.

**Definition 1.5 (The norm and the selected unit vectors).**

$$(\operatorname{point}\left(a, b\right) = \operatorname{tuple}\left(a, a + b, \frac{a}{2} + b\right)) \land (\left\lVert \operatorname{point}\left(a, b\right) \right\rVert = \operatorname{max}\left(\operatorname{max}\left(\left|a\right|, \left|a + b\right|\right), \left|\frac{a}{2} + b\right|\right))$$

*Formalization.* `D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.point` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Manna; K. Mandal; K. Paul; D. Sain (2025). *An improvement of the Blanco-Koldobsky-Turnšek characterization of isometries*. URL: <https://arxiv.org/abs/2511.20345v1>.

*Commentary.*

Write p = point 1 0, q = point 0 1 and r = point (−1) (3/2). The actual closed unit ball consists exactly of points whose three facet readings have absolute value at most one. Every actual extreme point has at least two active readings: otherwise a nonzero tangent fixing the sole active reading permits a small feasible segment in both directions. Solving the three possible pairs of active equations places every extreme point in {±p, ±q, ±r}, so the actual extreme-point set is finite. At p the first two readings equal one; at q the last two equal one. Any proper convex decomposition of either point forces these two readings of each endpoint to equal one, hence forces the endpoint to be the point itself. Thus p and q are genuine extreme unit points.

**Definition 1.6 (Algebraic coordinates and independence).**

$$\operatorname{coordinates}\left(\operatorname{tuple}\left(a, b\right)\right) = \operatorname{point}\left(a, b\right)$$

*Formalization.* `D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Manna; K. Mandal; K. Paul; D. Sain (2025). *An improvement of the Blanco-Koldobsky-Turnšek characterization of isometries*. URL: <https://arxiv.org/abs/2511.20345v1>.

*Commentary.*

The inverse coordinate map is w ↦ (w₀, w₁ − w₀). This is an algebraic linear equivalence from ℝ × ℝ, without an assertion that the usual product norm is preserved. Mapping the standard two-vector basis through it gives the selected independent tuple (p,q).

**Definition 1.7 (The continuous linear endomorphism).**

$$operator\left(\operatorname{point}\left(a, b\right)\right) = \operatorname{point}\left(a + b, \frac{0 - 3}{2} \cdot b\right)$$

*Formalization.* `D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.operator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Manna; K. Mandal; K. Paul; D. Sain (2025). *An improvement of the Blanco-Koldobsky-Turnšek characterization of isometries*. URL: <https://arxiv.org/abs/2511.20345v1>.

*Commentary.*

The operator has coordinate formula T(a,b) = (a+b, −3b/2). Conjugating this linear map by coordinates and applying finite-dimensional continuity constructs an actual Plane →L[ℝ] Plane. In particular Tp = p and Tq = point 1 (−3/2). For a direction (a,b), orthogonality at p implies a(a+b) ≤ 0, and orthogonality at q implies (a+b)(a/2+b) ≤ 0. The existing active_not_BJ theorem supplies necessity for these all-direction statements. At the outputs the corresponding signed products are (a+b)(a−b/2) = (3/2)a(a+b) − (a+b)²/2 and (a+b)(b−a/2) = 3(a+b)(a/2+b) − 2(a+b)². They are nonpositive under the respective input hypotheses. Opposite weak signs ensure that for every real scalar, some active signed facet stays at least one. This proves full local preservation at p and q, including zero directions, zero slopes and both scalar signs.

**Theorem 1.8 (Refutation of the whole question).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/manna-mandal-paul-sain-2025-polyhedral-extreme-tests` (refuted) by `D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"manna-mandal-paul-sain-2025-polyhedral-extreme-tests","declaration_gid":"D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* J. Manna; K. Mandal; K. Paul; D. Sain (2025). *An improvement of the Blanco-Koldobsky-Turnšek characterization of isometries*. URL: <https://arxiv.org/abs/2511.20345v1>.

*Commentary.*

The real carrier, its dimension and completeness, finite actual extreme-point set, selected independent extreme unit tuple, continuous operator and full preservation implications instantiate every premise of the real source assertion. If T = cU for any scalar and native linear isometry, norm_smul and U.norm_map force ‖Tz‖ = |c| ‖z‖ for every z. But ‖p‖ = ‖r‖ = 1, ‖Tp‖ = 1 and ‖Tr‖ = 2. These equalities contradict a common |c|, including c = 0. The theorem has the literal type Not claim. It answers the universal question negatively; it does not classify polyhedral norms or their K-numbers. The positive sup-norm theorem LinfKNumber.result concerns a different norm and retains its conclusion.

## References

- Truth anchor: `D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.Plane`
- Truth anchor: `D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.claim`
- Truth anchor: `D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.coordinates`
- Truth anchor: `D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.facetPlane`
- Truth anchor: `D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.fieldClaim`
- Truth anchor: `D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.operator`
- Truth anchor: `D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.point`
- Truth anchor: `D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.result`
- Dependency: [D5/S3/Analytic/BanachGeometry/LinfKNumber](LinfKNumber.md)
