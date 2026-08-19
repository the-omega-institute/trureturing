# Rational Rays of Golden Exponents

## Abstract

Rational golden-exponent rays are exactly rational coordinate rays.

**Theorem 1.1 (Golden-power values and exponent vectors have the same rational rays).**

$$\forall a, b, c, d\in \mathbb{N},\ \left(\exists p, q\in \mathbb{N},\ q>0 \land q\cdot g(a,b)=p\cdot g(c,d)\right) \equiv \left(\exists p, q\in \mathbb{N},\ q>0 \land qa=pc \land qb=pd\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/GoldenExponentRays.golden_exponent_rational_ray_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write g(a,b) = a phi^2 + b phi^3. For natural exponent vectors (a,b) and (c,d), there are naturals p and positive q with q g(a,b) = p g(c,d) exactly when the same p and q satisfy qa = pc and qb = pd. Thus the real golden-power values and their exponent vectors determine the same nonnegative rational rays.

The forward implication rewrites the scaled values as golden-power coordinates and applies the existing repository theorem GoldenPowerCoordinates.golden_power_coordinates_unique directly. The reverse implication substitutes the two coordinate equalities. That reused theorem already rests on Mathlib's exact irrationality theorem for the golden ratio, so no second irrationality proof is made.

Repository search found the coordinate-uniqueness theorem but no prior rational-ray declaration. Pinned Mathlib source and skill search found no exact ray theorem; online Loogle returned zero matches for the formula-shaped irrational-linear-form query.

This node closes only the ray-classification sentence in observation 6.167, in its positive-denominator natural-coordinate form. It does not formalize the finite shell census, the listed ratios, Euler-product natural boundaries, zero cancellation, or any linear-independence hypothesis about zeta zeros.

## References

- Truth anchor: `D5/S1/Eigenstructure/GoldenExponentRays.golden_exponent_rational_ray_iff`
