# Fixed-basepoint Riemannian chart comparison

## Abstract

Intrinsic metric and uniform pairwise chart comparison.

Let E be any finite-dimensional real inner-product space, including dimension zero, and M a connected Hausdorff smooth manifold modeled on E, with its given continuous Riemannian bundle. The canonical metric is constructed from this Riemannian data. Finite-dimensional charts give local compactness; Hausdorffness then gives the separation needed for the intrinsic emetric. Connectedness makes every intrinsic edistance finite: the infinite-radius ball is nonempty and clopen. EMetricSpace.toMetricSpace preserves the original topology definitionally. No completeness, minimizer, positive dimension or independently supplied metric is assumed.

**Theorem 1.1 (Canonical intrinsic edistance).**

$$\forall x \in M,\; \forall y \in M,\; \operatorname{canonicalEdist}\left(x, y\right) = \operatorname{riemannianEDist}\left(x, y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Riemannian/ChartComparison.canonicalMetric_edist` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

canonicalEdist is edist after installing Original172.canonicalMetric. This definitional bridge is consumed by the pairwise comparison below.

**Theorem 1.2 (One neighborhood for all pairs).**

$$\forall p \in M,\; \forall epsilon \in Real,\; \operatorname{Implies}\left(\operatorname{And}\left(\operatorname{LT}\left(0, epsilon\right), \operatorname{LT}\left(epsilon, 1\right)\right), \operatorname{ExistsOpenNeighborhoodInChartSource}\left(p, \operatorname{ForAllPairsInNeighborhood}\left(x, y, \operatorname{LE}\left(\left(1 - epsilon\right) \cdot \operatorname{NpChartChord}\left(x, y\right), \operatorname{canonicalDist}\left(x, y\right)\right), \operatorname{LE}\left(\operatorname{canonicalDist}\left(x, y\right), \left(1 + epsilon\right) \cdot \operatorname{NpChartChord}\left(x, y\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Riemannian/ChartComparison.canonical_pairwise_local_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here phi=extChartAt p and Np(w) is the original g-norm of the actual differential of phi inverse at phi(p), applied to w. The source explicitly transports the dependent fiber norm along phi inverse(phi(p))=p. For each p and 0<epsilon<1, one open U containing p inside the chart source works for every x,y in U. The inequalities use canonicalMetric.

The live intermediate intrinsic_pairwise supplies the uniform fixed-Np comparison. Relative tangent transport bounds give forward and inverse chart differential estimates on a neighborhood V. Choose an intrinsic c-ball inside V, a convex chart ball whose inverse lies in V, and shrink U so d(p,x)<c/4 and Np(phi(x)-phi(p))<c/(4(1-epsilon)). A competitor shorter than the proposed lower bound has length<c/2; the triangle inequality and subpath monotonicity put every point of it within intrinsic distance 3c/4 of p, hence inside V. Integrating the fixed-norm forward differential estimate contradicts its shortness. Competitors may leave U. The inverse image of the straight chart segment proves the upper bound. The public theorem consumes this intermediate, the edistance bridge, and the explicit base-norm transport.

This is C0/C1 of the original section 17.2 program: a formal synthesis using the pinned Mathlib Riemannian interfaces, without a literature novelty claim. C2-C6, R3, R5 and the full section 17.2 remain unfinished. Escape registration requires separate faithful source reconstruction and compiled variation/sensitivity evidence; this document makes no registration claim.

## References

- Truth anchor: `D5/S3/Geometry/Riemannian/ChartComparison.canonicalMetric_edist`
- Truth anchor: `D5/S3/Geometry/Riemannian/ChartComparison.canonical_pairwise_local_comparison`
