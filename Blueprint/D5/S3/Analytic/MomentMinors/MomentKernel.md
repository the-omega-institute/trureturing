# Integrated supporting tangents

## Abstract

Positive semidefinite midpoint moment gaps.

**Theorem 1.1 (The finite family theorem).**

Lean statement: `D5/S3/Analytic/MomentMinors/MomentKernel.momentKernel_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MomentMinors/MomentKernel.momentKernel_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a Borel probability law be concentrated on strictly positive real values, with integrable first moment. Let I be an interval on which every power moment exists, with the logarithmic limiting moments at zero and one. For any finite family of parameters t(i) in I, the real matrix with entries lambda((t(i)+t(j))/2) is positive semidefinite.

For s different from zero and one, use the generating function f(s,x)=(x^s-sx+s-1)/(s(s-1)); the two remaining functions are x-1-log(x) and x log(x)-x+1. Their Jensen gaps are exactly lambda(s), and each has second derivative x^(s-2) on the positive half-line.

For arbitrary real coefficients c(i), form F(x)=sum over i,j of c(i)c(j)f((t(i)+t(j))/2,x). Its second derivative is the square of the sum of c(i)x^(t(i)/2-1). Thus F is convex. The mean m is strictly positive, and the supporting tangent at m lies below F at every positive value. Integrating this pointwise inequality gives the nonnegative quadratic form. Every generating function is integrable by the moment assumptions; no integration of the derivative or of the second derivative is required.

## References

- Truth anchor: `D5/S3/Analytic/MomentMinors/MomentKernel.momentKernel_posSemidef`
- Dependency: [D5/S3/Analytic/MomentMinors/Defs](Defs.md)
