/- GID: D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrastPackage
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrastPackage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Packages the identity-Jordan minimal, conjugacy, and characteristic data. -/

import D5.S3.ConceptDynamics.Representation.IdentityJordanGeneratorContrast

/- Library-search audit trail (2026-08-28):
   * The imported module is the sole repository hit for the four exact declarations.
   * Pinned Mathlib has predicates for semisimple representations and endomorphisms, and a
     Jordan-Chevalley decomposition, but no representation-semisimplification constructor.
   * Loogle, LeanSearch, and GitHub Lean-code searches found no exact semisimplification API.
   * Therefore the package reuses the imported characteristic-polynomial carrier verbatim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Representation.IdentityJordanGeneratorContrastPackage

open Matrix Polynomial
open D5.S3.ConceptDynamics.Representation.IdentityJordanGeneratorContrast

/-- The identity and unipotent cyclic actions have the two stated minimal polynomials and are not
conjugate, while both generator characteristic polynomials are `(X - 1)^2`.

The final nested conjunction deliberately reuses the imported characteristic-polynomial carrier.
Pinned Mathlib has predicates for representations that are already semisimple, but no operation
constructing a representation's semisimplification. Over `ℚ` in this fixed two-dimensional
example, the split characteristic polynomial records two copies of the sole eigenvalue `1`, the
semisimple data `1 ⊕ 1`.

This theorem does not define or construct semisimplified representations, assert an isomorphism
between such objects, or claim that characteristic-polynomial equality identifies
semisimplification in general. -/
theorem identity_jordan_generator_contrast_package :
    minpoly ℚ (rhoZero cycleGenerator) = X - 1 ∧
      minpoly ℚ (rhoUnipotent cycleGenerator) = (X - 1) ^ 2 ∧
        ¬ IsConj (rhoZero cycleGenerator) (rhoUnipotent cycleGenerator) ∧
          ((rhoZero cycleGenerator).charpoly = (X - 1) ^ 2 ∧
            (rhoUnipotent cycleGenerator).charpoly = (X - 1) ^ 2) := by
  exact ⟨rho_zero_minpoly, rho_unipotent_minpoly, representations_not_isomorphic,
    same_semisimplification_charpoly⟩
#print axioms identity_jordan_generator_contrast_package

/- Reverse probe: every semantic leaf of the public package must project independently. -/
example :
    minpoly ℚ (rhoZero cycleGenerator) = X - 1 ∧
      minpoly ℚ (rhoUnipotent cycleGenerator) = (X - 1) ^ 2 ∧
        ¬ IsConj (rhoZero cycleGenerator) (rhoUnipotent cycleGenerator) ∧
          ((rhoZero cycleGenerator).charpoly = (X - 1) ^ 2 ∧
            (rhoUnipotent cycleGenerator).charpoly = (X - 1) ^ 2) := by
  have packaged := identity_jordan_generator_contrast_package
  exact ⟨packaged.1, packaged.2.1, packaged.2.2.1, packaged.2.2.2⟩

/- Trivialization probe: the one-dimensional substitution collapses the generator contrast. -/
example : rhoZeroGeneratorOne = rhoUnipotentGeneratorOne :=
  low_dimension_degenerate_audit.2

end D5.S3.ConceptDynamics.Representation.IdentityJordanGeneratorContrastPackage
