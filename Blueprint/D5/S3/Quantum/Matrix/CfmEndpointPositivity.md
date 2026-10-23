# Positivity at both endpoints

## Abstract

The sandwich derivative applied to a resolvent increment is positive at both endpoints.

**Theorem 1.1 (The two endpoint derivatives are positive semidefinite).**

Lean statement: `D5/S3/Quantum/Matrix/CfmEndpointPositivity.endpoint_derivatives_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CfmEndpointPositivity.endpoint_derivatives_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For ordered complex Hermitian 3 by 3 matrices U≤V with −I<U,V<I, set ε=1/20000 and g(X)=R_2(X)+R_3(X)−εR_4(X). Then Dg_U(g(V)−g(U)) and Dg_V(g(V)−g(U)) are positive semidefinite.

Factor every increment at the selected endpoint C as R_s(C) Z_s R_s(C), with H/3≤Z_s≤3H and H=V−U. Expand the nine terms of Dg_C(g(V)−g(U)). The four positive terms indexed by 2 and 3 contribute at least one third of the three unmixed H-quadratic forms. The 4,4 term is nonnegative. The four negative mixed terms are bounded below by −6ε times the two mixed forms. The three-node estimate bounds those by 54 times the unmixed forms. The remaining coefficient is 1/3−324ε=4757/15000>0. Singular H and repeated eigenvalues are included.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CfmEndpointPositivity.endpoint_derivatives_positive`
- Dependency: [D5/S3/Quantum/Matrix/CfmRadialDerivative](CfmRadialDerivative.md)
- Dependency: [D5/S3/Quantum/Matrix/CfmResolventInterpolation](CfmResolventInterpolation.md)
