# Occupancy means on a finite path

## Abstract

The occupancy means of binary words with no adjacent ones form the polytope defined by coordinate bounds and adjacent-sum inequalities. In three coordinates this is a square-based pyramid.

**Theorem 1.1 (The path stable set polytope).**

$$\operatorname{conv}\left(W_{n}\right) = P_{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/PathStableSetPolytope.convexHull_vertices` (`✓ std3`). ∎

*Citation.* Vaclav Chvatal (1975). *On certain polytopes associated with graphs*. URL: <https://doi.org/10.1016/0095-8956(75)90041-6>.

*Commentary.*

For every natural number n, a vector is a convex mixture of admissible binary words exactly when each coordinate lies in [0,1] and each adjacent pair sums to at most one. The empty path is included. For a single vertex, the coordinate upper bound is essential.

**Theorem 1.2 (The three-coordinate pyramid).**

$$x = (1-t) (u,0,v) + t (0,1,0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/PathStableSetPolytope.convexHull_three_pyramid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For three coordinates, nonnegativity and the two adjacent-sum inequalities already imply the coordinate upper bounds. Every point is a mixture of (u,0,v), with u and v in [0,1], and the apex (0,1,0). The mixing coefficient t is the middle occupancy x1. Thus the base is the unit square in the plane x1=0 and the apex has x1=1.

The induction keeps the entire tail mixture. On each tail word it prepends either zero or the complement of the first tail bit. At the level of means these are the affine maps y mapped to (0,y) and (1-y0,y). If x1 is below one, their mixture with coefficient x0/(1-x1) has the prescribed mean x. If x1 is one, x0 is zero and the first map suffices. A tail component of weight p therefore gives two components of weights (1-t)p and tp, preserving all tail correlations.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/PathStableSetPolytope.convexHull_three_pyramid`
- Truth anchor: `D5/S1/Words/AdmissibleWords/PathStableSetPolytope.convexHull_vertices`
- Dependency: [D5/S1/Words/AdmissibleWords/AdmissibleCount](AdmissibleCount.md)
