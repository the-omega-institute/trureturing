# Unit-Jordan Representation Separation

## Abstract

The identity and unit-Jordan generator actions have distinct minimal polynomials but the same two trivial graded factors.

**Theorem 1.1 (The representations differ while their graded factors agree).**

$$\begin{aligned}\forall K, \operatorname{Field}\left(K\right) \Rightarrow\\I_{K} = \operatorname{identityEnd}\left(K^{2}\right), U_{K}(x, y) = (x + y, y),\\N_{K} = U_{K} - I_{K},\\\operatorname{minpoly}\left(K, I_{K}\right) = t - 1 \land \left(\left(\neg N_{K} = 0\right) \land \left(N_{K}^{2} = 0 \land \left(\operatorname{minpoly}\left(K, U_{K}\right) = {t - 1}^{2} \land \left(\left(\neg \left(\exists e \in \operatorname{LinearEquiv}\left(K, K^{2}, K^{2}\right),\; e \circ I_{K} = U_{K} \circ e\right)\right) \land \left(\left(\neg \operatorname{RepresentationEquiv}\left(\operatorname{trivialRepresentation}\left(K, \operatorname{Multiplicative}\left(Z\right), K^{2}\right), \operatorname{unitJordanRepresentation}\left(K\right)\right)\right) \land \left(\operatorname{gr}\left(I_{K}\right) = I_{K} \land \operatorname{gr}\left(U_{K}\right) = I_{K}\right)\right)\right)\right)\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/UnitJordanRepresentationSeparation.unit_jordan_representation_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary field K, the identity generator is the identity linear endomorphism of K times K. The unipotent generator is constructed from the canonical unit-Jordan action (x,y) maps to (x+y,y).

The nilpotent part is the difference between those generator actions. It is nonzero, its square vanishes, and linear independence of the identity and the unipotent action gives the exact quadratic minimal polynomial.

Here gr(T) is the action on the direct sum of the invariant first-axis factor and the quotient read by the second coordinate: its value at (x,y) is ((T(x,0)).first,(T(0,y)).second). Both displayed graded actions are therefore the direct sum of two trivial factors.

Pinned Mathlib supplies the generic minimal-polynomial uniqueness result. Repository search found the canonical Jordan action but no theorem combining minimal polynomials, non-conjugacy, and graded factors.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Representation/UnitJordanRepresentationSeparation.unit_jordan_representation_separation`
- Dependency: [D5/S1/Eigenstructure/UnitJordanDrift](../../../S1/Eigenstructure/UnitJordanDrift.md)
