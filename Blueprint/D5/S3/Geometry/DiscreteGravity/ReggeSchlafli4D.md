# Simplex normals and Regge variation

## Abstract

Euclidean simplex normals, the Schläfli identity, and variation of the four-dimensional Regge action.

**Theorem 1.1 (Closure of the cofactor normals).**

$$\forall d\in \mathbb{N}, \forall v\in \operatorname{Fin}(d+1) \to \mathbb{R}^{d}, \sum_{i \in \operatorname{Fin}(d+1)} \operatorname{N}(v, i) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.minkowski_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the edges from vertex zero as rows of the edge matrix E. For each other vertex use the corresponding inverse column multiplied by minus the absolute determinant. The normal at vertex zero is minus the sum of those columns. Their sum over all vertices is zero.

**Theorem 1.2 (Outward facet normals).**

$$\forall d\in \mathbb{N}, \forall v\in \operatorname{Fin}(d+1) \to \mathbb{R}^{d}, \forall k\in \operatorname{Fin}(d+1), \operatorname{det}(\operatorname{E}(v)) \neq 0 \implies (\forall i\in \operatorname{Fin}(d+1), \forall j\in \operatorname{Fin}(d+1), (i \neq k) \land (j \neq k) \implies \langle \operatorname{N}(v, k), \operatorname{v}(j)-\operatorname{v}(i)\rangle  = 0) \land (\forall j\in \operatorname{Fin}(d+1), j \neq k \implies (\langle \operatorname{N}(v, k), \operatorname{v}(k)-\operatorname{v}(j)\rangle  = -\lvert \operatorname{det}(\operatorname{E}(v))\rvert ) \land (\langle \operatorname{N}(v, k), \operatorname{v}(k)-\operatorname{v}(j)\rangle  < 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.outward_normal_orthogonality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse matrix pairs each inverse column with its own edge and annihilates the other edges. For every facet, the pairing with a difference of two facet vertices is zero. The pairing with the displacement from a facet vertex toward its opposite vertex equals minus the absolute determinant and is strictly negative.

**Theorem 1.3 (The hinge Gram determinant).**

$$\forall n\in \mathbb{N}, \forall v\in \operatorname{Fin}((n+2)+1) \to \mathbb{R}^{(n+2)}, \forall i\in \operatorname{Fin}((n+2)+1), \forall j\in \operatorname{Fin}((n+2)+1), (\operatorname{det}(\operatorname{E}(v)) \neq 0) \land (i \neq j) \implies (\lvert \langle \operatorname{u}(v, i), \operatorname{u}(v, j)\rangle \rvert  < 1) \land (\Vert \operatorname{N}(v, i)\Vert  \cdot \Vert \operatorname{N}(v, j)\Vert  \cdot \sin (\operatorname{theta}(v, i, j)) = \lvert \operatorname{det}(\operatorname{E}(v))\rvert  \cdot \sqrt{\operatorname{hingeGramDet}(v, i, j)})$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.gram_normal_hinge_sine_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the Euclidean norm and take the interior dihedral angle to be the arccosine of the negative dot product of the unit outward normals. For distinct opposite vertices the absolute dot product is strictly less than one. The two normal lengths times the sine of the angle equal the absolute edge determinant times the square root of the hinge Gram determinant. Rebase at a hinge vertex and apply the complementary principal minor relation to the edge Gram matrix.

**Theorem 1.4 (The volume-normalized hinge identity).**

$$\forall n\in \mathbb{N}, \forall v\in \operatorname{Fin}((n+2)+1) \to \mathbb{R}^{(n+2)}, \forall i\in \operatorname{Fin}((n+2)+1), \forall j\in \operatorname{Fin}((n+2)+1), (\operatorname{det}(\operatorname{E}(v)) \neq 0) \land (i \neq j) \implies \operatorname{V}(v, i) \cdot \operatorname{V}(v, j) \cdot \sin (\operatorname{theta}(v, i, j)) = \frac{n+2}{n+1} \cdot \operatorname{Vol}(v) \cdot \operatorname{A}(v, i, j)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.facet_volume_hinge_sine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Divide the normal lengths by the facet factorial and the full determinant by the simplex factorial. This gives a ratio of the simplex dimension to the facet dimension, equal to four thirds in dimension four.

**Theorem 1.5 (Differentiating the normal pairing).**

$$\forall I\in \operatorname{FiniteLinearOrder}(), \forall X\in \operatorname{RealInnerProductSpace}(), \forall u\in I \to \mathbb{R} \to X, \forall du\in I \to X, \forall V\in I \to \mathbb{R}, \forall t\in \mathbb{R}, (\forall i\in I, (\operatorname{HasDerivAt}((s\mapsto \operatorname{u}(i, s)), \operatorname{du}(i), t)) \land (\operatorname{EventuallyAt}(t, (s\mapsto \Vert \operatorname{u}(i, s)\Vert  = 1)))) \land ((\forall i\in I, \forall j\in I, i \neq j \implies \lvert \langle \operatorname{u}(i, t), \operatorname{u}(j, t)\rangle \rvert  < 1) \land (\sum_{i \in I} \operatorname{V}(i) \cdot \operatorname{u}(i, t) = 0)) \implies (\sum_{i \in I} \sum_{j \in I} \operatorname{V}(i) \cdot \operatorname{V}(j) \cdot \langle \operatorname{u}(i, t), \operatorname{du}(j)\rangle  = 0) \land ((\forall i\in I, \forall j\in I, i \neq j \implies \operatorname{HasDerivAt}((s\mapsto \operatorname{arccos}(-\langle \operatorname{u}(i, s), \operatorname{u}(j, s)\rangle )), \frac{\langle \operatorname{u}(i, t), \operatorname{du}(j)\rangle +\langle \operatorname{u}(j, t), \operatorname{du}(i)\rangle }{\sin (\operatorname{arccos}(-\langle \operatorname{u}(i, t), \operatorname{u}(j, t)\rangle ))}, t)) \land (\sum_{i < j} \operatorname{V}(i) \cdot \operatorname{V}(j) \cdot \sin (\operatorname{arccos}(-\langle \operatorname{u}(i, t), \operatorname{u}(j, t)\rangle )) \cdot \operatorname{deriv}((s\mapsto \operatorname{arccos}(-\langle \operatorname{u}(i, s), \operatorname{u}(j, s)\rangle )), t) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.normal_closure_schlafli_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unit length near the evaluation point makes each diagonal normal derivative vanish. Weighted closure at the evaluation point kills the full double sum. The derivative of each off-diagonal arccosine is the symmetrized pairing divided by its positive sine. The sum over increasing pairs of this derivative weighted by the two normal weights and the sine is zero.

**Theorem 1.6 (Euclidean Schläfli identity).**

$$\forall n\in \mathbb{N}, \forall v\in \mathbb{R} \to \operatorname{Fin}((n+2)+1) \to \mathbb{R}^{(n+2)}, \forall t\in \mathbb{R}, (\operatorname{det}(\operatorname{E}(\operatorname{v}(t))) \neq 0) \land (\forall i\in \operatorname{Fin}((n+2)+1), \operatorname{DifferentiableAt}((s\mapsto \operatorname{v}(s, i)), t)) \implies (\forall i\in \operatorname{Fin}((n+2)+1), \forall j\in \operatorname{Fin}((n+2)+1), i \neq j \implies \operatorname{HasDerivAt}((s\mapsto \operatorname{theta}(\operatorname{v}(s), i, j)), \operatorname{deriv}((s\mapsto \operatorname{theta}(\operatorname{v}(s), i, j)), t), t)) \land (\sum_{i < j} \operatorname{A}(\operatorname{v}(t), i, j) \cdot \operatorname{deriv}((s\mapsto \operatorname{theta}(\operatorname{v}(s), i, j)), t) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.euclidean_simplex_schlafli` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin; Jean-Marc Schlenker (2000). *On the Schläfli differential formula*. URL: <https://arxiv.org/abs/math/0001176v2>.

*Commentary.*

The vertices are differentiable at the evaluation point and the edge determinant there is nonzero. Every dihedral angle for a distinct pair has the stated derivative. The hinge area is the square root of its Gram determinant divided by the factorial of its dimension. Multiplying the area-weighted sum by the common determinant and factorial recovers the zero sum from differential closure.

**Theorem 1.7 (The ten triangle hinges).**

$$\forall v\in \mathbb{R} \to \operatorname{Fin}(4+1) \to \mathbb{R}^{4}, \forall t\in \mathbb{R}, (\operatorname{det}(\operatorname{E}(\operatorname{v}(t))) \neq 0) \land (\forall i\in \operatorname{Fin}(4+1), \operatorname{DifferentiableAt}((s\mapsto \operatorname{v}(s, i)), t)) \implies \sum_{i < j} \frac{\sqrt{\operatorname{hingeGramDet}(\operatorname{v}(t), i, j)}}{2} \cdot \operatorname{deriv}((s\mapsto \operatorname{theta}(\operatorname{v}(s), i, j)), t) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.regge_schlafli_4d` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin; Jean-Marc Schlenker (2000). *On the Schläfli differential formula*. URL: <https://arxiv.org/abs/math/0001176v2>.

*Commentary.*

In dimension four the five opposite-vertex labels give ten increasing pairs. Each area is one half of the square root of the two-edge Gram determinant. The sum of triangle areas times the corresponding angle derivatives vanishes.

**Theorem 1.8 (Regge action variation).**

$$\forall H\in \operatorname{FiniteType}(), \forall C\in \operatorname{FiniteType}(), \forall K\in \operatorname{ReggeComplex}(H, C), \forall A\in H \to \mathbb{R} \to \mathbb{R}, \forall theta\in H \to C \to \mathbb{R} \to \mathbb{R}, \forall dA\in H \to \mathbb{R}, \forall dtheta\in H \to C \to \mathbb{R}, \forall t\in \mathbb{R}, (\forall h\in H, \operatorname{HasDerivAt}((s\mapsto \operatorname{A}(h, s)), \operatorname{dA}(h), t)) \land (\forall q\in C, (\forall h\in H, \operatorname{Inc}(K, h, q) \implies \operatorname{HasDerivAt}((s\mapsto \operatorname{theta}(h, q, s)), \operatorname{dtheta}(h, q), t)) \land (\sum_{h \in H, \operatorname{Inc}(K, h, q)} \operatorname{A}(h, t) \cdot \operatorname{dtheta}(h, q) = 0)) \implies \operatorname{HasDerivAt}(\operatorname{S}(K, A, theta), \sum_{h \in H} \operatorname{dA}(h) \cdot \operatorname{epsilon}(K, theta, h, t), t)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.regge_action_palatini_variation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A hinge deficit is two pi minus the sum of its incident simplex angles. The action sums area times deficit over the included hinges. The product rule generates an angle variation. Changing the order of the incidence sum gives a sum of local Schläfli terms over the included incidences, each zero by hypothesis. The derivative is the sum of area derivatives times the original deficits. When boundary hinges are omitted, the local cancellation hypothesis applies to the retained incidences of each simplex.

**Theorem 1.9 (Cosmological volume variation).**

$$\forall H\in \operatorname{FiniteType}(), \forall C\in \operatorname{FiniteType}(), \forall K\in \operatorname{ReggeComplex}(H, C), \forall A\in H \to \mathbb{R} \to \mathbb{R}, \forall theta\in H \to C \to \mathbb{R} \to \mathbb{R}, \forall dA\in H \to \mathbb{R}, \forall dtheta\in H \to C \to \mathbb{R}, \forall Vol\in C \to \mathbb{R} \to \mathbb{R}, \forall dVol\in C \to \mathbb{R}, \forall L\in \mathbb{R}, \forall t\in \mathbb{R}, ((\forall h\in H, \operatorname{HasDerivAt}((s\mapsto \operatorname{A}(h, s)), \operatorname{dA}(h), t)) \land (\forall q\in C, (\forall h\in H, \operatorname{Inc}(K, h, q) \implies \operatorname{HasDerivAt}((s\mapsto \operatorname{theta}(h, q, s)), \operatorname{dtheta}(h, q), t)) \land (\sum_{h \in H, \operatorname{Inc}(K, h, q)} \operatorname{A}(h, t) \cdot \operatorname{dtheta}(h, q) = 0))) \land (\forall q\in C, \operatorname{HasDerivAt}((s\mapsto \operatorname{Vol}(q, s)), \operatorname{dVol}(q), t)) \implies \operatorname{HasDerivAt}(\operatorname{SLambda}(K, A, theta, Vol, L), \sum_{h \in H} \operatorname{dA}(h) \cdot \operatorname{epsilon}(K, theta, h, t)-L \cdot \sum_{q \in C} \operatorname{dVol}(q), t)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.regge_action_lambda_variation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting a constant cosmological coefficient times the sum of differentiable simplex volumes adds the negative coefficient times the sum of volume derivatives.

**Theorem 1.10 (Stationarity at zero deficit).**

$$\forall H\in \operatorname{FiniteType}(), \forall C\in \operatorname{FiniteType}(), \forall K\in \operatorname{ReggeComplex}(H, C), \forall A\in H \to \mathbb{R} \to \mathbb{R}, \forall theta\in H \to C \to \mathbb{R} \to \mathbb{R}, \forall dA\in H \to \mathbb{R}, \forall dtheta\in H \to C \to \mathbb{R}, \forall t\in \mathbb{R}, ((\forall h\in H, \operatorname{HasDerivAt}((s\mapsto \operatorname{A}(h, s)), \operatorname{dA}(h), t)) \land (\forall q\in C, (\forall h\in H, \operatorname{Inc}(K, h, q) \implies \operatorname{HasDerivAt}((s\mapsto \operatorname{theta}(h, q, s)), \operatorname{dtheta}(h, q), t)) \land (\sum_{h \in H, \operatorname{Inc}(K, h, q)} \operatorname{A}(h, t) \cdot \operatorname{dtheta}(h, q) = 0))) \land (\forall h\in H, \operatorname{epsilon}(K, theta, h, t) = 0) \implies \operatorname{HasDerivAt}(\operatorname{S}(K, A, theta), 0, t)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.flat_regge_stationarity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a configuration with zero deficit at every included hinge, any differentiable variation satisfying the local angle cancellation has zero action derivative.

**Theorem 1.11 (First-order edge holonomy).**

$$\forall H\in \operatorname{Type}(), \forall L\in \operatorname{List}(H), \forall epsilon\in H \to \mathbb{R}, \forall B\in H \to \operatorname{Mat}(4, 4, \mathbb{R}), (\operatorname{HasDerivAt}(\operatorname{edgeHolonomy}(L, epsilon, B), \sum_{h \in L} \operatorname{epsilon}(h) \cdot \operatorname{B}(h), 0)) \land (\operatorname{HasDerivAt}(\operatorname{edgeHolonomy}(L, epsilon, B), 0, 0) \iff \sum_{h \in L} \operatorname{epsilon}(h) \cdot \operatorname{B}(h) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.discrete_bianchi_edge_holonomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write the generators in one common frame and multiply the exponentials in the chosen list order. Every factor is the identity at zero, so the derivative there is the list sum of the deficit-weighted generators. First-order triviality is equivalent to the vanishing of that sum. A simplicial application requires a geometric transport relation that yields first-order triviality in the common frame.

**Theorem 1.12 (Spherical triangle area variation).**

$$\forall t\in \mathbb{R}, (\frac{\pi}{3} < t) \land (t < \pi) \implies (\forall i\in \operatorname{Fin}(3), \Vert \operatorname{p}(t, i)\Vert  = 1) \land ((\forall i\in \operatorname{Fin}(3), \forall j\in \operatorname{Fin}(3), \forall k\in \operatorname{Fin}(3), (i \neq j) \land ((i \neq k) \land (j \neq k)) \implies \operatorname{HasDerivAt}((s\mapsto \operatorname{alpha}(s, i, j, k)), 1, t)) \land ((\operatorname{HasDerivAt}(area, 3, t)) \land ((\sum_{i \in \operatorname{Fin}(3)} \operatorname{deriv}((s\mapsto \operatorname{alpha}(s, i, i+1, i+2)), t) = \operatorname{deriv}(area, t)) \land (\operatorname{deriv}(area, t) \neq 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.spherical_triangle_schlafli_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin; Jean-Marc Schlenker (2000). *On the Schläfli differential formula*. URL: <https://arxiv.org/abs/math/0001176v2>.

*Commentary.*

At parameters between pi over three and pi, the equal-distance unit vertices have three angles equal to the parameter. Each angle derivative is one. The area function in the identity is three times the parameter minus pi. Girard's theorem identifies this spherical excess with the intrinsic area of the triangle. The sum of angle derivatives equals the nonzero derivative of spherical excess, with unit weights at the vertices.

## References

- Truth anchor: `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.discrete_bianchi_edge_holonomy`
- Truth anchor: `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.euclidean_simplex_schlafli`
- Truth anchor: `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.facet_volume_hinge_sine`
- Truth anchor: `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.flat_regge_stationarity`
- Truth anchor: `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.gram_normal_hinge_sine_identity`
- Truth anchor: `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.minkowski_closure`
- Truth anchor: `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.normal_closure_schlafli_core`
- Truth anchor: `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.outward_normal_orthogonality`
- Truth anchor: `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.regge_action_lambda_variation`
- Truth anchor: `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.regge_action_palatini_variation`
- Truth anchor: `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.regge_schlafli_4d`
- Truth anchor: `D5/S3/Geometry/DiscreteGravity/ReggeSchlafli4D.spherical_triangle_schlafli_counterexample`
