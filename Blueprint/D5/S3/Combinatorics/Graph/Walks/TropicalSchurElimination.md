# Tropical Schur elimination and pivot distances

## Abstract

Min-plus vertex elimination preserves finite-walk distances for arbitrary extended nonnegative edge weights.

Let V be any vertex type and W assign an extended nonnegative real weight to every ordered pair. Infinity represents an unavailable edge. Walks are mathlib quiver paths in the complete directed quiver, with one arrow for each ordered pair. Vertices and edges may repeat; the empty walk has weight zero. The function weight sums edge weights, and distance is the infimum over all finite walks between the specified endpoints. Neither finiteness of V nor attainment of the infimum is assumed.

Fix a vertex b and write Pivots(V,b) for the subtype of vertices different from b. The map val includes this subtype into V. For pivot vertices a and z, the reduced weight schur(W,b)(a,z) is the minimum of W(val(a),val(z)) and W(val(a),b)+W(b,val(z)). Thus reduced walks exclude b at every vertex, including their endpoints.

**Theorem 1.1 (Compression, exact expansion and equal distances).**

$$\forall V \in \mathrm{Type},\; \forall W \in V \to \left(V \to \mathrm{ENNReal}\right),\; \forall b \in V,\; \forall a \in \mathrm{Pivots}\left(V, b\right),\; \forall z \in \mathrm{Pivots}\left(V, b\right),\; (\forall p \in \mathrm{Walk}\left(\mathrm{val}\left(a\right), \mathrm{val}\left(z\right)\right),\; \exists q \in \mathrm{Walk}\left(a, z\right),\; \mathrm{weight}\left(\mathrm{schur}\left(W, b\right), q\right) \le \mathrm{weight}\left(W, p\right)) \land ((\forall q \in \mathrm{Walk}\left(a, z\right),\; \exists p \in \mathrm{Walk}\left(\mathrm{val}\left(a\right), \mathrm{val}\left(z\right)\right),\; \mathrm{weight}\left(W, p\right) = \mathrm{weight}\left(\mathrm{schur}\left(W, b\right), q\right)) \land (\mathrm{distance}\left(\mathrm{schur}\left(W, b\right), a, z\right) = \mathrm{distance}\left(W, \mathrm{val}\left(a\right), \mathrm{val}\left(z\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/TropicalSchurElimination.pivot_walks_and_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each original walk between pivots compresses to a reduced walk of no larger weight. Each reduced walk expands to an original walk of exactly the same weight. Consequently the two infima agree, including when either is infinite.

For expansion, choose a minimizing branch of each reduced edge: keep the original edge, or insert the two-edge detour through b. For compression, retain a walk ending at the most recent pivot. A visit to b is held as a pending final edge; the next pivot completes a reduced edge. Consecutive b-to-b loops can be discarded because their weights are nonnegative. Induction on the original quiver path gives the weight bound. Applying the two constructions to every walk gives the two inequalities between the infima.

The result is the path interpretation of the min-plus update used in Floyd-Warshall elimination. It treats arbitrary vertex types and extended nonnegative weights directly. It makes no assertion for unrestricted signed weights: a negative loop at the eliminated vertex can lower original walk weights through arbitrarily many repetitions.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/TropicalSchurElimination.pivot_walks_and_distance`
