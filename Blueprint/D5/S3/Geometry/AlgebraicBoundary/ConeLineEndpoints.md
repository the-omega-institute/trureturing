# Off-axis lines through a salient cone

## Abstract

Separated actual boundary endpoints in every interior cone direction.

Let C be a closed salient convex cone in a real normed vector space, e an interior point, and x a vector outside the real span of e. There are real numbers a<b such that te-x belongs to the negative cone exactly when t is at most a, and belongs to C exactly when t is at least b. The points -(ae-x) and be-x belong to the entire topological boundary of C. No normalization functional, finite-dimensional coordinate system or polynomial is assumed.

**Theorem 1.1 (Two strictly separated finite boundary endpoints).**

$$\forall E \in RealNormedVectorSpace,\; \forall C \in ConvexCone\left(Real, E\right),\; \forall e \in E,\; \forall x \in E,\; \left(IsClosed\left(C\right) \land \left(Salient\left(C\right) \land \left(e \in interior\left(C\right) \land \left(\forall s \in Real,\; NotEqual\left(x, smul\left(s, e\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists a \in Real,\; \exists b \in Real,\; a < b \land \left(\left(\forall t \in Real,\; neg\left(sub\left(smul\left(t, e\right), x\right)\right) \in C \Leftrightarrow t \le a\right) \land \left(\left(\forall t \in Real,\; sub\left(smul\left(t, e\right), x\right) \in C \Leftrightarrow b \le t\right) \land \left(neg\left(sub\left(smul\left(a, e\right), x\right)\right) \in frontier\left(C\right) \land sub\left(smul\left(b, e\right), x\right) \in frontier\left(C\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlgebraicBoundary/ConeLineEndpoints.off_axis_closed_rays` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Since e is interior, e-x/t belongs to C for sufficiently large positive t. Positive scaling gives te-x in C. Cone addition makes the set of such parameters an upper set. Applying the same observation to -x supplies a point in the negative cone. Salience and the off-axis condition prevent any point of the line from belonging to both cones, which bounds the upper set below. Closedness then identifies it with a closed ray starting at its infimum. The continuous preimage boundary inclusion places the endpoint on the actual cone boundary. Repeating the construction with -x gives the negative closed ray, and salience gives the strict gap.

This proves the geometric endpoint assertion for every interior direction and every off-axis translate. To obtain real-rootedness of a boundary polynomial, one must still prove that its restrictions have the claimed degree, vanish at these two endpoints, and account for every root with multiplicity. Axis translates require a separate homogeneous polynomial identity.

## References

- Truth anchor: `D5/S3/Geometry/AlgebraicBoundary/ConeLineEndpoints.off_axis_closed_rays`
