# Isometric intervals from compact midpoints

## Abstract

In a compact extended metric space, exact midpoints for finite-distance pairs yield endpoint-preserving isometric real intervals for those pairs.

Let Y be an extended metric space with its metric topology, and assume Y is compact. Its distance d takes values in ENNReal, the nonnegative reals together with infinity. A finite-distance midpoint means a point z with d(a,z)=d(z,b)=d(a,b)/2 whenever d(a,b) is finite. This hypothesis ranges over every finite-distance pair, including pairs of equal points.

**Theorem 1.1 (A real interval with the prescribed endpoints).**

$$\forall Y \in Types,\; [EMetricSpace\left(Y\right)] [CompactSpace\left(Y\right)] \left(\forall a \in Y,\; \forall b \in Y,\; edist\left(a, b\right) < \infty \Rightarrow \left(\exists z \in Y,\; edist\left(a, z\right) = \frac{edist\left(a, b\right)}{2} \land edist\left(z, b\right) = \frac{edist\left(a, b\right)}{2}\right)\right) \Rightarrow \left(\forall a \in Y,\; \forall b \in Y,\; edist\left(a, b\right) < \infty \Rightarrow \left(\exists f \in Icc\left(0, Real\left(edist\left(a, b\right)\right)\right) \to Y,\; Isometry\left(f\right) \land \left(f\left(0\right) = a \land f\left(Real\left(edist\left(a, b\right)\right)\right) = b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CompactMidpointInterval.compact_midpoints_isometric_interval` (`✓ std3`). ∎

*Citation.* Martin R. Bridson; André Haefliger (1999). *Metric Spaces of Non-Positive Curvature*. DOI: [10.1007/978-3-662-12494-9](https://doi.org/10.1007/978-3-662-12494-9). URL: <https://webhomes.maths.ed.ac.uk/~v1ranick/papers/bridsonhaefligerx.pdf>.

*Commentary.*

Types denotes the universe of Y. Real(d(a,b)) is the real value of the finite extended distance. The source interval Icc(0,L) is the closed real interval with its usual induced metric. Its start and finish are 0 and L as subtype elements, with their membership proofs. Isometry(f) means equality of extended distances for every pair in this interval, so continuity and injectivity follow from the conclusion.

Repeatedly insert exact midpoints into a finite chain of 2^n edges. The maximum edge length is L times (1/2)^n. These chains need not be coherent across n. At every real time t, use the point with index floor(t divided by the mesh). The resulting step map has the exact endpoints, and its distance between any two times s,t is at most their real distance plus twice the mesh. The simultaneous bound at every real time is essential.

In the compact product of copies of Y indexed by the entire interval, take the closed sets of maps having these endpoints and satisfying the all-time bound at level n. Each set is nonempty, and the geometric errors make them decreasing. Compactness gives a map in their intersection. Passing to the limit in the error proves the 1-Lipschitz bound. This uses closed-set intersection; it assumes neither sequential compactness of an uncountable product nor continuity of the step maps.

The endpoint distance is exactly L. For ordered times s at most t, apply the triangle inequality along 0,s,t,L. The outer distances are at most s and L-t. Their sum with the middle distance is at least L, so that middle distance is at least t-s. Together with the Lipschitz upper bound this proves isometry. A zero-length interval is handled separately by equality of the endpoints.

The space Y may be empty and may have several components at infinite mutual distance. The theorem is conditional on selected points a,b and their finite distance. It asserts no interval joining an infinite-distance pair, no finite global diameter, no uniqueness of the interval and no curvature bound.

Bridson and Haefliger, Metric Spaces of Non-Positive Curvature (1999), I.1.4(1), states the classical complete metric midpoint criterion. That remark states the criterion without a proof. The implementation here constructs intervals in a compact extended metric space by finite refinement, all-time rounding and compact product intersection. It makes no mathematical novelty claim and does not claim the complete noncompact version.

For the original gluing quotient, apply FiniteOrbitChainMidpoint.compact_original_quotient_midpoints first, retaining its single metric, original quotient topology and representative-distance equality. Compactness descends from the finite family of compact pieces to this same original quotient topology. The present theorem then constructs isometric intervals for each finite-distance pair in that metric. To obtain a specified geometric realization one must still identify its actual pieces, partial isometries, full finite orbits, splitting property and marked quotient with these data.

## References

- Truth anchor: `D5/S3/Topology/CompactMidpointInterval.compact_midpoints_isometric_interval`
