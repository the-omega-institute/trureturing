# Role-Swap Orbit Factorization

## Abstract

Pairwise role swaps generate full role invariance and canonical orbit factorization.

**Theorem 1.1 (Role swaps generate full invariance and orbit factorization).**

$$\begin{gathered}\forall X, U, I: Type,\\{}T: X \to \left(U \to \left(I \to \left(I \to Prop\right)\right)\right),\\{}\operatorname{Finite}(I) \Rightarrow\\{}(((\forall i, j: I, \operatorname{RoleInvariant}(T, \operatorname{swap}(i, j))) \iff (\forall \sigma: \operatorname{Perm}(I), \operatorname{RoleInvariant}(T, \sigma))) \land\\{}((\forall \sigma: \operatorname{Perm}(I), \operatorname{RoleInvariant}(T, \sigma)) \iff \operatorname{FactorsThrough}(((x, u, (i, j)): X \times U \times I \times I \mapsto T(x, u, i, j)), \operatorname{roleOrbitProjection}(X, U, I)))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/NormativeOrbits/RoleSwapOrbitFactorization.role_swap_full_invariance_orbit_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier of roles is finite. A role permutation fixes the state and action coordinates and acts simultaneously on the actor and recipient.

The first public equivalence states that invariance under every pairwise role swap is exactly invariance under every role permutation. The forward implication uses the pinned permutation-generation theorem.

The second public equivalence uses the canonical quotient projection of the complete state-action-role tuple. Thus the factorization clause retains state and action while forgetting only role names.

Pinned-library search supplied the swap-generation, orbit-quotient, and fiber-factorization primitives. Repository searches found no frozen declaration combining these two equivalences for an admission predicate.

## References

- Truth anchor: `D5/S3/ConceptDynamics/NormativeOrbits/RoleSwapOrbitFactorization.role_swap_full_invariance_orbit_factorization`
