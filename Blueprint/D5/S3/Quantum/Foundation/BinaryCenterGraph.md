# The center graph of a whole exclusion ball

## Abstract

Binary compatibility determines a unique affine center graph on each original exclusion ball.

Let C be a closed, generating pointed cone in a finite dimensional real normed space V, and let u be a linear functional positive on nonzero cone vectors. The normalized base K and the pure locus are the original ones. An exclusion chart b parametrizes the entire original exclusion ball of a pure point p by an injective affine map from its Euclidean closed unit ball. Binary compatibility compares the centers of all original pure endpoints at independent weights in the closed unit interval. The chart boundary consists of the original pure points on that ball. This is the whole-ball assertion of XI138.2.

**Theorem 1.1 (The unique affine graph on every whole source ball).**

Lean statement: `D5/S3/Quantum/Foundation/BinaryCenterGraph.whole_ball_center_affine`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/BinaryCenterGraph.whole_ball_center_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original domain described above, every proof B of exclusionBalls satisfying the complete original binaryCompatible law, every original pure p and every entire ExclusionChart b of D(p), there exists exactly one real affine map g from the Euclidean chart carrier to V with g(x)=center(B,chartPure(p,b,x)) for every unit vector x, and its entire closed unit ball image is contained in K. The unique map is on the source chart carrier, equivalently on the affine span of the whole original D(p). No uniqueness on all of V is asserted. Since b is injective and its whole closed ball image is D(p), g composed with the inverse chart defines the actual G_F on every point of F=D(p); the sphere is exactly all original pure points of F.

Coordinate reflections preserve the chart sphere. Comparing their original chords by BC gives the change in the center function when one coordinate is reversed. Telescoping over all coordinates and using the common antipodal midpoint determines an affine interpolant with explicit basis coefficients. This constructs the map on the whole chart carrier from the actual original centers. Sphere convex generation and convexity of K give its entire-ball range; affine spanning gives uniqueness.

**Theorem 1.2 (Repeated and singleton rank branches).**

Lean statement: `D5/S3/Quantum/Foundation/BinaryCenterGraph.whole_ball_center_graph`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/BinaryCenterGraph.whole_ball_center_graph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every same original domain, B, BC, pure p and entire chart b, there exists an affine g with all the preceding original boundary values and the whole closed-ball image contained in K, unique among all affine maps with those boundary values. If SingleLabel(C,u,p), g is injective and its linear range has dimension b.dim. If SingleLabel fails, g is constant on the entire chart carrier. Under the original three-ball hypothesis, OriginalExclusionLimits.ballHyp supplies the chart with dimension three. On that chart a singleton label therefore has rank three.

A nonzero kernel vector would give two distinct antipodal source sphere points with the same original center. Their exclusions share this nonpure point; the original extreme-face intersection and two-point rigidity force equality of their whole exclusions. Singleton-label propagation on the original sphere then identifies the two pure points, a contradiction. In the repeated case, zero symmetry and two-point rigidity identify every sphere label's entire exclusion with the opposite ball. Whole-ball center uniqueness and sphere affine spanning force g to be constant.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/BinaryCenterGraph.whole_ball_center_affine`
- Truth anchor: `D5/S3/Quantum/Foundation/BinaryCenterGraph.whole_ball_center_graph`
- Dependency: [D5/S3/Quantum/Foundation/BinaryCenterNoncollapse](BinaryCenterNoncollapse.md)
