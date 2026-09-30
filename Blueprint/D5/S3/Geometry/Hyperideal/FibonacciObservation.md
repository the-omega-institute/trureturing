# Persistent Phase Ambiguity in the CFMP Return Observation

## Abstract

The cyclic CFMP return observation has a checkable modular kernel. This is a finite obstruction to recovering framed gluing parameters from the Fibonacci return readout alone.

**Theorem 1.1 (Discriminant square and Fibonacci conjugacy).**

For integer pairs, define
\[
D(x,y)=(-x+2y,\,2x+y),\quad
C(x,y)=(2x-y,\,x+2y),\quad
F(x,y)=(y,\,x+y),\quad
J(x,y)=(y,x).
\]
Then
\[
D^2=5I,\qquad C=D\circ J,\qquad C\circ JFJ=F\circ C.
\]

The Lean declarations are
\`D5.S3.Geometry.Hyperideal.FibonacciObservation.discriminant_sq\`,
\`observe_eq_discriminant_swap\`, and \`observe_fibonacci_conjugacy\`.

**Theorem 1.2 (Persistent phase indistinguishability).**

Write \(\operatorname{modEq}_m(a,b)\) for \(m\mid(b-a)\). For \(k,t\in\mathbb N\), let
\[
s_{k,t}=(kt,2kt).
\]
For every integer pair \(z\), both coordinates of \(C(z+s_{k,t})\) are congruent modulo \(5k\) to the corresponding coordinates of \(C(z)\).

The formal declaration is
\`D5.S3.Geometry.Hyperideal.FibonacciObservation.observe_phase_indistinguishable\`.

**Theorem 1.3 (Exact integer kernel normal form).**

For \(k>0\) and \(x,y\in\mathbb Z\), the two congruences \(C(x,y)\equiv(0,0)\pmod{5k}\) hold exactly when there are \(t,s\in\mathbb Z\) with
\[
x=kt,\qquad y=2kt+5ks.
\]
This is the congruence-level normal form behind the phase obstruction.

The formal declaration is
\`D5.S3.Geometry.Hyperideal.FibonacciObservation.kernel_phase_characterization\`.

**Theorem 1.4 (Image obstruction).**

For \(k>0\), a residue pair \((r,s)\) occurs as \(C(x,y)\pmod{5k}\) for some integer pair if and only if \(2r+s\equiv0\pmod5\).

The formal declaration is
\`D5.S3.Geometry.Hyperideal.FibonacciObservation.image_condition\`.

**Corollary 1.5 (The 5040 specialization).**

Since \(5040=5\cdot1008\), the phase shift gives coordinatewise congruence modulo \(5040\):
\[
\operatorname{modEq}_{5040}(C(z+s_{1008,t}),C(z)).
\]
This records the factor-five obstruction at the concrete modulus used by Robin-side arithmetic. It makes no claim that the factor seven creates or removes phases.

The formal declaration is
\`D5.S3.Geometry.Hyperideal.FibonacciObservation.observe_phase_indistinguishable_5040\`.

## Commentary

The identities \(D^2=5I\) and the discriminant interpretation are classical matrix algebra. The CFMP-specific content is the return-parameter interface and its framed congruence obstruction. The written Sections 133–139 of \`CFMP_GEOMETRIC_REALIZATION_OBSERVATION_DYNAMICS.md\` provide geometric context and finite checks.

This is a scoped obstruction about framed return parameters. It does not claim five distinct unmarked manifolds, a general hyperbolic realization, a Robin criterion, RH, or a solution of the minimum-six CFMP problem.
