# Strict Curvature of Normalized Cardinal Splines

## Abstract

The normalized cardinal spline has strictly negative curvature on its shifted closed central core in every order at least five.

The proof is an induction on the spline order built entirely on the single finite positive-part representation and the recurrences recorded in the preceding module. Its private invariant carries five simultaneous facts: support outside [0,m], reflection D_m(m-x)=-D_m(x), global Q_m(u)>=0 for every u>=0, strict positivity Q_m(1/2)>0, and strict decrease of D_m on [s_m,m-s_m]. These are proof-local facts, not additional public declarations.

**Theorem 1.1 (Strict negativity on the closed core).**

$$\begin{aligned}\forall m \in \mathbb{N}, 5 \leq m,\\\forall x \in \mathbb{R}, x \in [\operatorname{s}\left(m\right), m - \operatorname{s}\left(m\right)] \implies \operatorname{C}\left(m, x\right) < 0.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Curvature/CardinalSplineStrictCurvature.cardinalSpline_strict_curvature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural order m>=5 and every x in the closed interval [s_m,m-s_m], the curvature specialization C_m(x) is strictly negative. The closed endpoints are part of the assertion.

At order four, direct piecewise evaluation establishes the support and reflection laws, global nonnegativity of Q_4, Q_4(1/2)=1/18, and strict decrease of D_4 on its closed core. The associated C_4 is negative only in the core interior and is zero at 4/3 and 8/3; therefore the public strict-curvature theorem deliberately begins at order five.

For the induction step, the centered integral recurrence preserves global Q nonnegativity. When the centered window crosses zero, oddness cancels the symmetric part and leaves an integral over a nonnegative interval. Continuity plus the positive value at 1/2 makes the next half-offset integral strictly positive. The left half of the next core is split into t=1/2, 1/2<t<1, and 1<=t<=7/6. The half-offset Q inequality and strict decrease of D give negativity in these branches; reflection gives the right half. Differentiating D then propagates strict decrease and closes the invariant.

## References

- Truth anchor: `D5/S3/Analytic/Curvature/CardinalSplineStrictCurvature.cardinalSpline_strict_curvature`
- Dependency: [D5/S3/Analytic/Curvature/CardinalSplineRecurrence](CardinalSplineRecurrence.md)
