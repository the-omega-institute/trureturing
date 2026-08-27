# Closed Convex Distance-Witness Duality

## Abstract

Distance to a compact convex behavior image equals its optimal witness violation.

**Theorem 1.1 (Distance equals the supremum of normalized support-witness violations).**

$$\forall E \in Type, I \in \operatorname{Set}\left(E\right), y \in E,\; \left(\operatorname{NormedAddCommGroup}\left(E\right) \land \left(\operatorname{NormedSpace}\left(\mathbb{R}, E\right) \land \left(\operatorname{IsCompact}\left(I\right) \land \left(\operatorname{Convex}\left(\mathbb{R}, I\right) \land \operatorname{Nonempty}\left(I\right)\right)\right)\right)\right) \Rightarrow \operatorname{infDist}\left(y, I\right) = \operatorname{sup}_{c: \operatorname{StrongDual}\left(\mathbb{R}, E\right), \left\lVert c \right\rVert \leq 1} {c\left(y\right) - \operatorname{sup}_{z\in I} c\left(z\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometryLaws/ClosedConvexDistanceWitnessDuality.closed_convex_distance_witness_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be a real normed vector space and I a nonempty compact convex subset. Compactness is the inherited behavior-image condition and makes every real support value finite.

For a continuous real linear witness c, the support value is the supremum of c on I. The public supremum ranges over the complete dual unit ball.

The upper bound follows from the operator norm inequality. The reverse bound normalizes a Hahn-Banach separator between I and each ball whose radius is strictly below the distance.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/ClosedConvexDistanceWitnessDuality.closed_convex_distance_witness_duality`
