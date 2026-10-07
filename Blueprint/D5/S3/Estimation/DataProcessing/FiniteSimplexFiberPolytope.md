# Finite Convex Hulls for Declared Probability Constraints

## Abstract

Finite real probability coordinates with exact label, joint-source and support constraints form a finite convex hull, including the empty case.

**Theorem 1.1 (The exact coordinate class is a polytope).**

$$\exists V\in\operatorname{Finset}\left(\operatorname{MassVector}\left(W\right)\right),\operatorname{convexHull}\left(V\right) = F$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope.declaredCoordinateClass_isPolytope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

W, Z and U are finite types. The label and source maps have domains W and codomains Z and U. A is any subset of W. Q and nu are arbitrary real coordinate vectors; they need not themselves satisfy probability constraints, and the resulting feasible class may be empty.

For every choice of these types, maps, set and vectors, define F to contain exactly the nonnegative vectors x on W with total sum one, label pushforward equal to Q, source pushforward equal to nu, and every coordinate outside A equal to zero. A pushforward coordinate is the sum over the full inverse image of that label or source value. The source constraint retains the entire specified joint law.

IsPolytope means that some finite set V of real mass vectors has convex hull exactly F. It does not merely mean compact and convex. Zero masses and arbitrary real masses are allowed, and no carrier symbol is deleted.

For a linear slice of the standard simplex, if an extreme feasible x and another feasible y have the positive support of y contained in that of x, choose a sufficiently small positive t. The vector z=(x-t y)/(1-t) is feasible and x lies in the open segment from y to z. Extremality forces y=x. Thus positive supports distinguish extreme points; there are only finitely many such supports.

The slice is compact and convex. Krein-Milman expresses it as the closure of the convex hull of its extreme points, and the convex hull of a finite set is closed. The concrete label, source and support equations are one combined linear map, so this argument applies directly.

The theorem concerns real mass coordinates. Relating it to a native ProbabilityMeasure feasible class requires the singleton-mass coordinate equivalence and its exact constraint-image equality. That native interface is not asserted by this coordinate theorem.

## References

- Truth anchor: `D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope.declaredCoordinateClass_isPolytope`
