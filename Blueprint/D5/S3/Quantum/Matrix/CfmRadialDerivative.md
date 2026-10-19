# Resolvent derivatives and radial distance

## Abstract

The derivative of the three-resolvent map and trace duality reduce radial convexity to endpoint positivity.

**Definition 1.1 (The matrix space).**

Lean statement: `D5/S3/Quantum/Matrix/CfmRadialDerivative.Mat`

*Formalization.* `D5/S3/Quantum/Matrix/CfmRadialDerivative.Mat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Complex n×n matrices carry the Loewner order and their usual finite-dimensional topology.

**Definition 1.2 (The Cayley interval).**

Lean statement: `D5/S3/Quantum/Matrix/CfmRadialDerivative.cayleyDomain`

*Formalization.* `D5/S3/Quantum/Matrix/CfmRadialDerivative.cayleyDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Hermitian interval −I<X<I is expressed by positive definiteness of I+X and I−X.

**Definition 1.3 (The sandwich derivative).**

Lean statement: `D5/S3/Quantum/Matrix/CfmRadialDerivative.resolventDerivative`

*Formalization.* `D5/S3/Quantum/Matrix/CfmRadialDerivative.resolventDerivative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The derivative at X of R_s(X)=(sI−X)⁻¹ is K↦R_s(X)KR_s(X).

**Definition 1.4 (The three-resolvent map).**

Lean statement: `D5/S3/Quantum/Matrix/CfmRadialDerivative.resolventSum`

*Formalization.* `D5/S3/Quantum/Matrix/CfmRadialDerivative.resolventSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map is g(X)=R_2(X)+R_3(X)−εR_4(X), with ε any real parameter.

**Definition 1.5 (The derivative of g).**

Lean statement: `D5/S3/Quantum/Matrix/CfmRadialDerivative.resolventSumDerivative`

*Formalization.* `D5/S3/Quantum/Matrix/CfmRadialDerivative.resolventSumDerivative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual derivative is K↦R_2KR_2+R_3KR_3−εR_4KR_4. The final negative term is retained.

**Definition 1.6 (Positivity at both endpoints).**

Lean statement: `D5/S3/Quantum/Matrix/CfmRadialDerivative.EndpointPositive`

*Formalization.* `D5/S3/Quantum/Matrix/CfmRadialDerivative.EndpointPositive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every ordered pair U≤V in the Cayley interval, both Dg_U(g(V)−g(U)) and Dg_V(g(V)−g(U)) are positive semidefinite.

**Theorem 1.7 (Positive endpoint derivatives imply radial convexity).**

Lean statement: `D5/S3/Quantum/Matrix/CfmRadialDerivative.radial_of_endpoint_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CfmRadialDerivative.radial_of_endpoint_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every ordered U≤V in the Cayley interval, suppose both Dg_U(g(V)−g(U)) and Dg_V(g(V)−g(U)) are positive semidefinite. Then every ordered triple A≤C≤B in that interval satisfies both Frobenius radial distance inequalities.

Matrix inversion is differentiated at invertible shifts by the normed-algebra inverse derivative. All shifts sI−X for s=2,3,4 are positive definite. Cyclicity of trace gives tr(H Dg_X(K))=tr(Dg_X(H) K), and the trace product of positive semidefinite matrices is nonnegative. Vectorization identifies this trace pairing with the real Hilbert inner product. The general endpoint derivative criterion then applies. No commutation between distinct endpoints is required.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CfmRadialDerivative.EndpointPositive`
- Truth anchor: `D5/S3/Quantum/Matrix/CfmRadialDerivative.Mat`
- Truth anchor: `D5/S3/Quantum/Matrix/CfmRadialDerivative.cayleyDomain`
- Truth anchor: `D5/S3/Quantum/Matrix/CfmRadialDerivative.radial_of_endpoint_positive`
- Truth anchor: `D5/S3/Quantum/Matrix/CfmRadialDerivative.resolventDerivative`
- Truth anchor: `D5/S3/Quantum/Matrix/CfmRadialDerivative.resolventSum`
- Truth anchor: `D5/S3/Quantum/Matrix/CfmRadialDerivative.resolventSumDerivative`
- Dependency: [D5/S3/Quantum/Matrix/CayleyResolvent](CayleyResolvent.md)
- Dependency: [D5/S3/Quantum/Matrix/RadialConvexity](RadialConvexity.md)
