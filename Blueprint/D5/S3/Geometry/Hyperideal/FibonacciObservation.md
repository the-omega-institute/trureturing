# Persistent Five-Phase Ambiguity in the CFMP Return Observation

## Abstract

The cyclic CFMP return observation has an exact five-phase modular kernel. This is a finite obstruction to recovering framed gluing parameters from the Fibonacci return readout alone.

**Theorem 1.1 (Discriminant square and Fibonacci conjugacy).**

For integer pairs, define
[
D(x,y)=(-x+2y,,2x+y),quad
C(x,y)=(2x-y,,x+2y),quad
F(x,y)=(y,,x+y),quad
J(x,y)=(y,x).
]
Then
[
D^2=5I,qquad C=Dcirc J,qquad Ccirc JFJ=Fcirc C.
]

*Proof.* Machine-checked in Lean as
`D5.S3.Geometry.Hyperideal.FibonacciObservation.discriminant_sq`,
`...observe_eq_discriminant_swap`, and
`...observe_fibonacci_conjugacy` (`✓ std3`). ∎

**Theorem 1.2 (Persistent phase indistinguishability).**

Write (operatorname{modEq}_m(a,b)) for (mmid(b-a)). For (k,tinmathbb N), let
[
s_{k,t}=(kt,2kt).
]
For every integer pair (z), both coordinates of (C(z+s_{k,t})) are congruent modulo (5k) to the corresponding coordinates of (C(z)).

*Proof.* Machine-checked in Lean as
`D5.S3.Geometry.Hyperideal.FibonacciObservation.observe_phase_indistinguishable`
(`✓ std3`). The first coordinate is unchanged exactly; the second changes by (5kt). ∎

## Commentary

The written Sections 133–139 of `CFMP_GEOMETRIC_REALIZATION_OBSERVATION_DYNAMICS.md` identify (C) with multiplication by the golden discriminant after a coordinate swap and exhibit five actual framed gluing phases when the modulus is divisible by five. The theorem above formalizes the algebraic core that every such geometric family must satisfy. Repeating the conjugated Fibonacci readout cannot remove this phase ambiguity because of Theorem 1.1.

This is a scoped obstruction about the framed return-parameter observation. It does not claim five distinct unmarked manifolds, does not construct a general hyperbolic realization, and does not solve the minimum-six CFMP problem.
