# Persistent phase ambiguity in the CFMP return observation

## Abstract

The cyclic CFMP return observation has a persistent phase congruence modulo 5k.

**Theorem 1.1 (Discriminant square and Fibonacci conjugacy).**

Lean statement: `D5/S3/Geometry/Hyperideal/FibonacciObservation.discriminant_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FibonacciObservation.discriminant_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For integer pairs, D(x,y)=(-x+2y,2x+y), C(x,y)=(2x-y,x+2y), F(x,y)=(y,x+y), and J(x,y)=(y,x). The exact identities are D^2=5I, C=D followed by J, and C followed by JFJ equals F followed by C.

These identities identify the cyclic CFMP return observation with the golden discriminant after a coordinate swap, and show that the Fibonacci evolution preserves its observation fibres.

**Theorem 1.2 (Persistent phase indistinguishability).**

Lean statement: `D5/S3/Geometry/Hyperideal/FibonacciObservation.observe_phase_indistinguishable`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FibonacciObservation.observe_phase_indistinguishable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write modEq_m(a,b) for m dividing b-a. For k,t in the natural numbers, the phase shift s(k,t)=(kt,2kt) changes the first observed coordinate by zero and the second by 5kt.

For positive k, the exact congruence kernel has the form (k*t,2*k*t+5*k*s), and the dual image condition is 2*r+s equal to zero modulo five. These are the FibonacciObservation.kernel_phase_characterization and FibonacciObservation.image_condition statements.

At the concrete modulus 5040=5*1008, the phase-five congruence persists. The factor seven does not enter the displayed kernel generator; no broader arithmetic conclusion is claimed here.

The obstruction is scoped to the framed return-parameter observation. It does not claim five distinct unmarked manifolds, a general hyperbolic realization, or a solution of the minimum-six CFMP problem.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/FibonacciObservation.discriminant_sq`
- Truth anchor: `D5/S3/Geometry/Hyperideal/FibonacciObservation.observe_phase_indistinguishable`
