# Arcsine moments for qubit tangent profiles

## Abstract

Two exact moments of the arcsine density on the open interval from minus one to one.

**Theorem 1.1 (Even moment).**

Lean statement: `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentArcsine.arcsine_even_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentArcsine.arcsine_even_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x > 0, the arcsine average of kₓ(z) = 1/(1 − (1 − x²)z²) is 1/x. The density is 1/(π sqrt(1 − z²)) with respect to Lebesgue measure on (−1, 1). Fold the even integrand to the positive half and substitute z = 1/sqrt(1 + t²). The resulting Cauchy integral is evaluated by arctangent.

**Theorem 1.2 (Moment of the product of two kernels).**

Lean statement: `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentArcsine.arcsine_odd_node_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentArcsine.arcsine_odd_node_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x, g > 0, g times the arcsine average of z² kₓ(z) k_g(z) equals 1/(x(x + g)). The same substitution gives a product of two quadratic reciprocals on the positive half-line. Use partial fractions at distinct nodes. At equal nodes, positive rescaling and inversion exchange the two terms obtained by splitting 1 + t² over the squared denominator.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentArcsine.arcsine_even_moment`
- Truth anchor: `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentArcsine.arcsine_odd_node_moment`
