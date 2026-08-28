# Identity and Jordan Generator Contrast

## Abstract

The identity and a rational Jordan action are nonisomorphic but have the same semisimple characteristic data.

**Theorem 1.1 (The identity generator has a linear minimal polynomial).**

$$\operatorname{minpolyQ}\left(\operatorname{act}\left(rhoZero, g\right)\right) = X - 1$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast.rho_zero_minpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the free cyclic group Multiplicative integers and rational two-by-two matrices. The first action sends every group element to the identity matrix, so its generator has minimal polynomial X minus one.

**Theorem 1.2 (The Jordan generator has a quadratic minimal polynomial).**

$$\operatorname{minpolyQ}\left(\operatorname{act}\left(rhoUnipotent, g\right)\right) = (X - 1)^2$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast.rho_unipotent_minpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Jordan generator is not a scalar matrix, so the minimal polynomial has degree at least two. Cayley-Hamilton makes it divide the quadratic characteristic polynomial, forcing equality with the square of X minus one.

**Theorem 1.3 (The cyclic representations are not isomorphic).**

$$\neg \operatorname{IsConj}\left(\operatorname{act}\left(rhoZero, g\right), \operatorname{act}\left(rhoUnipotent, g\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast.representations_not_isomorphic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a free cyclic representation, an isomorphism conjugates the generator matrices. Unit conjugation preserves the minimal polynomial, while the two computed polynomials have different degrees. Hence no conjugating unit exists.

**Theorem 1.4 (Both actions have the same semisimple characteristic data).**

$$\operatorname{charpoly}\left(\operatorname{act}\left(rhoZero, g\right)\right) = (X - 1)^2 \land \operatorname{charpoly}\left(\operatorname{act}\left(rhoUnipotent, g\right)\right) = (X - 1)^2$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast.same_semisimplification_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pinned Mathlib has no semisimplification interface. This module records the source contrast by proving that both characteristic polynomials are the square of X minus one. Over the rationals in dimension two, that split polynomial records two trivial composition factors.

**Theorem 1.5 (Conjugacy is necessary for minimal-polynomial invariance).**

$$\neg \operatorname{IsConj}\left(\operatorname{act}\left(rhoZero, g\right), \operatorname{act}\left(rhoUnipotent, g\right)\right) \land \operatorname{minpolyQ}\left(\operatorname{act}\left(rhoZero, g\right)\right) \ne \operatorname{minpolyQ}\left(\operatorname{act}\left(rhoUnipotent, g\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast.conjugacy_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two concrete generator matrices supply the required hypothesis counterexample. They are not conjugate, and their minimal polynomials have degrees one and two. Thus the conjugacy premise in the private invariance lemma cannot be removed.

**Theorem 1.6 (Jordan powers grow linearly and degenerate at zero).**

$$\forall n, \operatorname{act}\left(rhoUnipotent, g^n\right) = \operatorname{matrix2}\left(1, n, 0, 1\right) \land \operatorname{act}\left(rhoUnipotent, g^0\right) = \operatorname{act}\left(rhoZero, g\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast.generator_power_degenerate_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The upper-right entry of the nth positive generator power is n. At n equal to zero this entry vanishes, and the whole action is the identity action.

**Theorem 1.7 (The identity action is self-conjugate and zero is not invertible).**

$$\operatorname{IsConj}\left(\operatorname{act}\left(rhoZero, g\right), \operatorname{act}\left(rhoZero, g\right)\right) \land \forall z, \operatorname{act}\left(rhoZero, z\right) = \operatorname{identityMatrix}\left(2\right) \land \neg \operatorname{IsUnit}\left(\operatorname{zeroMatrix}\left(2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast.trivial_action_degenerate_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first representation is self-conjugate and explicitly constant at the identity. The zero two-by-two matrix has zero determinant and is not a unit, so it cannot be a cyclic group generator image.

**Theorem 1.8 (Empty and one-dimensional carriers collapse the contrast).**

$$\operatorname{zeroMatrix}\left(Empty\right) = \operatorname{identityMatrix}\left(Empty\right) \land rhoZeroGeneratorOne = rhoUnipotentGeneratorOne$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast.low_dimension_degenerate_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the empty matrix carrier, zero and identity are the same empty function. In dimension one there is no off-diagonal coordinate, so the identity and would-be Jordan generators coincide. The two-dimensional carrier is therefore essential.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast.conjugacy_hypothesis_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast.generator_power_degenerate_audit`
- Truth anchor: `D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast.low_dimension_degenerate_audit`
- Truth anchor: `D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast.representations_not_isomorphic`
- Truth anchor: `D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast.rho_unipotent_minpoly`
- Truth anchor: `D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast.rho_zero_minpoly`
- Truth anchor: `D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast.same_semisimplification_charpoly`
- Truth anchor: `D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast.trivial_action_degenerate_audit`
