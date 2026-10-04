# The finite vertices of the same common body

## Abstract

The common six-length cut simplex is exactly the convex hull of twelve labeled endpoints.

Let l be six strictly positive lengths in the order (01,02,03,23,13,12), with all six coordinates free to vary. Write G for the symmetric matrix with diagonal one and off-diagonal minus cosh of the corresponding length. C is the same nonnegative unit-sum simplex cut by Gv<=0. For different labels i,j, define p(i,j)=(-Gij*ei+ej)/(1-Gij), with ei the standard coordinate vector. L is the set of ordered pairs of distinct labels in Fin 4; P sends a label (i,j) to p(i,j), and V is its range. R6 and R4 denote the real six- and four-coordinate spaces. row(l,r,v) denotes the r-th row of G times v.

**Theorem 1.1 (No additional extreme points).**

$$\forall l \in R6,\; \left(\forall k \in Fin\left(6\right),\; 0 < coord\left(l, k\right)\right) \Rightarrow \left(extremePoints\left(Real, C\left(l\right)\right) = V\left(l\right) \land \left(convexHull\left(Real, V\left(l\right)\right) = C\left(l\right) \land \left(Injective\left(P\left(l\right)\right) \land \left(\forall i \in Fin\left(4\right),\; \forall j \in Fin\left(4\right),\; distinct\left(i, j\right) \Rightarrow \left(p\left(l, i, j\right) \in C\left(l\right) \land \left(0 < coord\left(p\left(l, i, j\right), i\right) \land \left(0 < coord\left(p\left(l, i, j\right), j\right) \land \left(\left(\forall k \in Fin\left(4\right),\; \left(distinct\left(k, i\right) \land distinct\left(k, j\right)\right) \Rightarrow coord\left(p\left(l, i, j\right), k\right) = 0\right) \land \left(row\left(l, i, p\left(l, i, j\right)\right) = 0 \land \left(\forall r \in Fin\left(4\right),\; distinct\left(r, i\right) \Rightarrow row\left(l, r, p\left(l, i, j\right)\right) < 0\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LengthGramPolytope.cut_body_polytope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A tight truncation inequality forces its coordinate to exceed one half, so two truncations cannot be tight together. A feasible point has at least two positive coordinates. With no tight truncation, transfer a small amount of mass between two positive coordinates in both directions. With one tight truncation and at least three positive coordinates, a nonzero three-coordinate direction preserves both the coordinate sum and that tight row. Continuity preserves all remaining strict inequalities for a sufficiently small perturbation in either direction. Each case gives a nontrivial open segment through the point, excluding extremality.

Thus an extreme point has precisely two positive coordinates and one tight truncation. These two equalities determine p(i,j). Conversely, any strict convex combination equal to p(i,j) forces its two terms to have the same support and tight row, and therefore to equal p(i,j). The compact convex body is the closed convex hull of its extreme points by Krein-Milman. The hull of the finite endpoint set is closed, giving the stated exact hull.

The support recovers the original edge, while the unique tight row recovers its ordered endpoint. Hence the twelve labels produce twelve distinct points. This classifies the coefficient body used by the common radial normalization and actual Lorentz frame. Identification with the eight geometric halfspaces, interior, complete hyperbolic face and edge incidence, prescribed distances, angles, rigidity, volume and gluing remain separate geometric claims. Zero-length degenerations are outside the strict positive-length domain of this statement.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/LengthGramPolytope.cut_body_polytope`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramBody](LengthGramBody.md)
