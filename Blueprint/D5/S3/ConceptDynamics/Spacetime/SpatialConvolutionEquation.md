# Equations in the Finite Spatial Convolution Ring

## Abstract

Spatial convolution equations have principal-multiple and uniqueness criteria.

**Theorem 1.1 (Solvability, uniqueness, and the zero factor).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/SpatialConvolutionEquation.spatial_convolution_equation_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/SpatialConvolutionEquation.spatial_convolution_equation_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier consists of finitely supported integer functions on the three-dimensional integer lattice. Its convolution ring has no zero divisors by the unique-sums instance. The equation f * g = h therefore has a solution exactly when h belongs to the principal multiples of f, and a nonzero f has at most one solution. The principal multiples contain zero and are closed under subtraction and right multiplication. For f = 0, a solution exists exactly when h = 0, in which case every finitely supported g is a solution. Computing a solution is a separate question.

**Theorem 1.2 (The carrier and the convolution formula).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/SpatialConvolutionEquation.coefficient_multiplication`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/SpatialConvolutionEquation.coefficient_multiplication` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient equivalence identifies the additive carrier with finitely supported integer functions. At r, multiplication sums f(p) * g(q) over pairs with p + q = r. Both sums range over finite supports. The multiplicative unit is the unit point mass at the origin.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/SpatialConvolutionEquation.coefficient_multiplication`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/SpatialConvolutionEquation.spatial_convolution_equation_criterion`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/SpatialEquationCriterion](SpatialEquationCriterion.md)
