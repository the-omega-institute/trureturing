# Full Role-Invariance Orbit Factorization

## Abstract

Full role invariance is canonical orbit factorization for any role carrier.

**Theorem 1.1 (Full invariance is orbit factorization without finiteness).**

$$\begin{gathered}\forall X, U, I: Type,\\{}T: X \to \left(U \to \left(I \to \left(I \to Prop\right)\right)\right),\\{}(\forall \sigma: \operatorname{Perm}(I), \operatorname{RoleInvariant}(T, \sigma)) \iff \operatorname{FactorsThrough}(((x, u, (i, j)): X \times U \times I \times I \mapsto T(x, u, i, j)), \operatorname{roleOrbitProjection}(X, U, I)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/NormativeOrbits/FullRoleInvarianceOrbitFactorization.full_role_invariance_iff_orbit_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A role permutation fixes the state and action coordinates and acts simultaneously on the actor and recipient coordinates.

For an arbitrary role carrier, invariance under every role permutation is equivalent to factorization through the canonical role-orbit projection.

The proof uses orbit equivalence and quotient soundness only. No finite generation premise is required.

## References

- Truth anchor: `D5/S3/ConceptDynamics/NormativeOrbits/FullRoleInvarianceOrbitFactorization.full_role_invariance_iff_orbit_factorization`
- Dependency: [D5/S3/ConceptDynamics/NormativeOrbits/RoleSwapOrbitFactorization](RoleSwapOrbitFactorization.md)
