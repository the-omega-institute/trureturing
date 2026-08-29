# Identity-Jordan Generator Contrast Package

## Abstract

The two minimal polynomials, nonconjugacy, and both characteristic-polynomial equalities are exposed by one declaration.

**Theorem 1.1 (The full identity-Jordan contrast is packaged together).**

$$\operatorname{minpolyQ}\left(\operatorname{act}\left(rhoZero, cycleGenerator\right)\right) = X - 1 \land \operatorname{minpolyQ}\left(\operatorname{act}\left(rhoUnipotent, cycleGenerator\right)\right) = (X - 1)^2 \land \neg \operatorname{IsConj}\left(\operatorname{act}\left(rhoZero, cycleGenerator\right), \operatorname{act}\left(rhoUnipotent, cycleGenerator\right)\right) \land (\operatorname{charpoly}\left(\operatorname{act}\left(rhoZero, cycleGenerator\right)\right) = (X - 1)^2 \land \operatorname{charpoly}\left(\operatorname{act}\left(rhoUnipotent, cycleGenerator\right)\right) = (X - 1)^2)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrastPackage.identity_jordan_generator_contrast_package` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The declaration conjoins the imported minimal-polynomial equalities, the generator nonconjugacy result, and the two imported characteristic-polynomial equalities. Pinned Mathlib has semisimplicity predicates and Jordan-Chevalley decomposition, but no operation constructing a representation's semisimplification. In this fixed rational two-dimensional example, the split characteristic polynomial records two copies of eigenvalue one. The package does not construct semisimplified representations, assert an isomorphism between them, or claim that characteristic-polynomial equality detects semisimplification in general.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrastPackage.identity_jordan_generator_contrast_package`
- Dependency: [D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast](IdentityJordanGeneratorContrast.md)
