# Strict downward transitions

## Abstract

A positive multiplier transfers polynomial sign boundaries to strict signed neighborhoods.

**Theorem 1.1 (Opposite endpoint signs give an isolated downward transition).**

Lean statement: `D5/S3/Analytic/Interpolation/PolynomialStrictTransition.strict_downward_of_polynomial_multiplier`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/PolynomialStrictTransition.strict_downward_of_polynomial_multiplier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be any real polynomial, g and w arbitrary functions from the real numbers to the real numbers, and l<r real endpoints. Assume w(x)>0 and w(x)g(x)=p(x) for every x in the closed interval [l,r], together with g(l)>0 and g(r)<0. There exist real xi and delta>0 such that the closed interval [xi-delta,xi+delta] is contained in (l,r), g(xi)=0, g(x)>0 for every xi-delta<x<xi, and g(x)<0 for every xi<x<xi+delta.

The supremum of the positive polynomial evaluations in [l,r] lies strictly between the endpoints and is a zero. Finiteness of the zero set gives a punctured neighborhood without other zeros. A negative value on its left would force another zero before a positive value approaching the supremum, by the intermediate value theorem. No positive value can lie to the right of the supremum. The positive multiplier transfers both strict signs and the zero to g. Neither a simple root nor continuity of w is assumed.

For a curvature represented as a polynomial divided by a positive multiplier, this result supplies the strict neighborhoods after the polynomial identity, multiplier positivity, and opposite endpoint signs have been established. It supplies no fractional weak-space membership, fractional integral identity, approximation estimate, or common forcing construction.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/PolynomialStrictTransition.strict_downward_of_polynomial_multiplier`
