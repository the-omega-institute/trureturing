# The original exclusion ellipsoids and metric range bundles

## Abstract

Unique continuous affine ellipsoids and actual metric range bundles of the entire original Q1 family.

V is an arbitrary nonzero finite dimensional real normed space. C is the entire closed pointed generating convex cone, u is strictly positive away from zero on C, K is the entire section u equal to one, and P is the entire extreme locus of K. Exclusion uses every effect between zero and u on the original cone and every state, including mixed states. Q1 means that every original pure label has an injective affine parametrization of its entire exclusion by the Euclidean closed three-ball and that every such exclusion has original whole-effect width one.

**Definition 1.1 (The whole compact exclusion).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallBundle.wholeExclusion`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionBallBundle.wholeExclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is the original exclusion subset of V, equipped with its derived compactness and nonemptiness. Its hyperspace topology is the Hausdorff topology of nonempty compact subsets of the original normed carrier. No pure-only replacement or selected zero set is used.

**Theorem 1.2 (Q1 implies whole-family continuity).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallBundle.whole_exclusion_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionBallBundle.whole_exclusion_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mapping from every original pure label to its entire exclusion is continuous. Its only premises are the cone and unit assumptions and Q1. Pure closedness follows because all labels lie in the compact saturated-label locus. The positive lower bound for every direction of every chart is reused directly from ExclusionUniformNoncollapse.all_label_uniform_noncollapse.

Choose an entire affine three-ball chart at each label without asserting that the choice is continuous. Compactness of K bounds all centers and all chart operators. Along any convergent label sequence and any subsequence, a further subsequence of center and operator pairs converges. The paid uniform lower estimate passes to the limit and makes its linear part injective. Closedness of P puts its entire sphere in the extreme locus of K. Original upper incidence puts its entire mixed ball inside the exclusion of the limiting label. AffineBallRigidity.eq_of_subset_of_extreme_sphere upgrades this containment to equality because both balls have the same injective three-dimensional source. Continuous images in the compact hyperspace then give the desired limit for each subsequence, hence continuity.

This continuity statement does not assume Pair, weakPair, PR, edge lifting, a continuous selection of charts, a common physical metric, or a matrix-model identification. Hausdorff continuity alone does not assert the shape-operator or vector-bundle conclusions.

**Definition 1.3 (The original affine center).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallBundle.chartCenter`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionBallBundle.chartCenter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value at zero of an entire affine ball chart is regarded as a point of V. Its unit reading is one. It is not a vector in the kernel of u; only differences from this center are kernel vectors.

**Theorem 1.4 (Continuous chart-independent centers).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_center_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_center_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same original cone assumptions and Q1, the centers vary continuously, lie in K, and agree with the value at zero of every entire affine ball chart of the corresponding exclusion. Equality of compact affine balls gives equality of their centers by AffineBallRigidity.center_eq_of_ball_eq. Once whole-ball convergence is known, ExclusionIncidence.parameter_subsequence extracts convergent chart parameters with precisely that compact limit. Every resulting center limit is therefore the center at the limiting label. This establishes continuity without choosing charts continuously.

Only differences from the affine center are transported to the actual kernel. The auxiliary Euclidean realization below is supplied by a typed linear equivalence; its norm and topology correspondence is derived by finite dimensional automatic continuity.

**Definition 1.5 (The typed actual kernel inclusion).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallBundle.kernelInclusion`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionBallBundle.kernelInclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any Euclidean realization e from the actual kernel of u to H, this is the actual subtype inclusion composed with the inverse of e. The affine center remains a V-valued point of the unit plane.

**Definition 1.6 (Every chart in the auxiliary metric).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallBundle.auxiliaryLinear`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionBallBundle.auxiliaryLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The linear part of every original affine chart has unit reading zero. It therefore lands in the actual kernel and is transported through e.

**Theorem 1.7 (Metric-dependent uniform bounds).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallBundle.auxiliary_metric_uniform_charts`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionBallBundle.auxiliary_metric_uniform_charts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original and auxiliary norms induce the same topology by finite dimensional automatic continuity of e and its inverse. For each fixed e there are common positive constants eta at most R, before every original pure label and every entire three-ball chart. Every source direction has auxiliary image norm between eta and R times its norm. The same constants bound every one of the three singular semiaxes, using the existing right singular basis and Gram orthogonality owner directly. The original frozen noncollapse bound is applied directly, and compactness of K gives the upper bound. No metric-independent constants are asserted under rescaling.

**Definition 1.8 (The auxiliary positive shape).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallBundle.shapeOperator`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionBallBundle.shapeOperator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An arbitrary original entire three-ball chart gives A A adjoint in the chosen Euclidean realization. The subsequent theorem proves that the result is independent of every original chart.

**Definition 1.9 (The actual kernel endomorphism).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallBundle.actualKernelShape`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionBallBundle.actualKernelShape` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The auxiliary shape is conjugated through the explicitly supplied e to an endomorphism of the actual kernel of u. This transport does not move the affine center into the kernel.

**Theorem 1.10 (Continuous actual rank-three shape).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_shape_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_shape_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the unchanged original cone assumptions and Q1, the positive shape is continuous, has actual image dimension three, and agrees with the Gram operator of every original chart. Uniform boundedness extracts convergent chart operators along subsequences. Whole-exclusion continuity and actual affine-center continuity identify their entire limiting balls. Ball-image shape uniqueness then identifies the operator limit.

**Definition 1.11 (The actual Moore-Penrose inverse).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallBundle.shapeDagger`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionBallBundle.shapeDagger` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is exactly the frozen FiniteMoorePenroseInverse of the actual positive shape, converted to a continuous linear map.

**Definition 1.12 (The inverse-shape form).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallBundle.fiberMetric`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionBallBundle.fiberMetric` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The form is inner(v,Q dagger w) in the chosen auxiliary metric. Its positive definiteness belongs to the actual range of Q.

**Theorem 1.13 (Continuous inverse, projection and form).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_inverse_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_inverse_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common metric-dependent lower bound controls the actual inverse norm. The actual inverse family is continuous. Q composed with its inverse is the actual auxiliary orthogonal projection onto its image, so those projections are continuous. Evaluation and the inner product give joint continuity of the form.

**Theorem 1.14 (The actual disc and its boundary).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_metric_disc`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_metric_disc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse-shape form is positive definite on the actual image. Center plus actual kernel inclusion of v belongs to the entire original exclusion exactly when v belongs to that image and its metric square is at most one. Membership in the actual intrinsic frontier is exactly image membership and metric square equal to one. Thus an ambient semidefinite cylinder is excluded.

**Definition 1.15 (The whole ambient square root).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallBundle.shapeSqrt`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionBallBundle.shapeSqrt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the unique positive square root of the positive shape on all H, including its kernel.

**Theorem 1.16 (Unique actual affine ellipsoid).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_ellipsoid_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_ellipsoid_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual affine center has unit reading one. The shape is positive of rank three, its full ambient positive square root is continuous, and its entire ambient closed-ball image translated by that actual center is exactly the original exclusion. Any affine center and positive operator with the same entire representation equal these values. The center is compared in V, and the shape comparison takes place only after the typed kernel identification.

**Theorem 1.17 (The actual real rank-three vector bundle).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_range_bundle`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_range_bundle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the original Q1 telescope, the actual images of the shape operators form a genuine real VectorPrebundle with Euclidean three-space model. Its generated VectorBundle topology is exactly the topology induced by the range graph in P times H. Projection continuity and rank are derived outputs, not new assumptions. The conjugated endomorphism on the literal kernel has continuous operator family, rank three, and self-adjoint positive form for the pulled-back auxiliary inner product. Its actual range graph is homeomorphic, preserving the original label and via the supplied e, to the displayed Euclidean realization. The fiber identification is an actual linear equivalence of the ranges.

**Theorem 1.18 (Actual normalized local disc and sphere products).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_normalized_local_products`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_normalized_local_products` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every original pure label there is a continuous local linear chart of the actual image bundle that preserves the actual inverse-shape metric. Its neighborhood of the entire original centered exclusions is homeomorphic to the neighborhood times the closed Euclidean three-ball. The actual intrinsic boundaries have the sphere product. Both inverse maps are continuous and both directions of every overlap transition are continuous. No global frame or continuous choice of the original ball charts is assumed.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallBundle.actualKernelShape`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallBundle.auxiliaryLinear`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallBundle.auxiliary_metric_uniform_charts`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallBundle.chartCenter`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallBundle.fiberMetric`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallBundle.kernelInclusion`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_center_continuous`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_ellipsoid_unique`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_inverse_continuous`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_metric_disc`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_normalized_local_products`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_range_bundle`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallBundle.original_shape_continuous`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallBundle.shapeDagger`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallBundle.shapeOperator`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallBundle.shapeSqrt`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallBundle.wholeExclusion`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionBallBundle.whole_exclusion_continuous`
- Dependency: [D5/S3/Geometry/AffineBallRigidity](../../Geometry/AffineBallRigidity.md)
- Dependency: [D5/S3/Geometry/ContinuousRangeBundle](../../Geometry/ContinuousRangeBundle.md)
- Dependency: [D5/S3/Geometry/EllipsoidShape](../../Geometry/EllipsoidShape.md)
- Dependency: [D5/S3/Geometry/MetricRangeChart](../../Geometry/MetricRangeChart.md)
- Dependency: [D5/S3/Quantum/Foundation/ExclusionIncidence](ExclusionIncidence.md)
- Dependency: [D5/S3/Quantum/Foundation/ExclusionUniformNoncollapse](ExclusionUniformNoncollapse.md)
- Dependency: [D5/S3/Quantum/Foundation/SingleLabelNormalBody](SingleLabelNormalBody.md)
