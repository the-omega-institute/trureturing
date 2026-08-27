/- GID: D5/S3/ConceptDynamics/Attribution/ClassicalChoiceNonnaturality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ClassicalChoiceNonnaturality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Classical choice supplies finite selectors, but the resulting family is not natural. -/

import D5.S3.ConceptDynamics.Attribution.NoNaturalFiniteChoice

/- Library-search audit trail (2026-08-28):
   * Current-tree name and body-shape searches found the canonical obstruction
     `no_natural_finite_choice`, but no theorem exposing the particular family
     supplied by `Classical.choice` and its failure of naturality.
   * Pinned Mathlib supplies `Classical.choice`, finite carriers, and
     equivalences, but no theorem stating this source-specific nonnaturality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.ClassicalChoiceNonnaturality

open D5.S3.ConceptDynamics.Attribution.NoNaturalFiniteChoice

/-- The selector family obtained from the choice axiom on every finite
nonempty carrier cannot commute with every equivalence. -/
theorem classical_choice_family_is_nonnatural :
    let choice : forall (alpha : Type) (_ : Fintype alpha) (_ : Nonempty alpha), alpha :=
      fun _ _ h => Classical.choice h
    Not (forall (alpha beta : Type) (fAlpha : Fintype alpha) (fBeta : Fintype beta)
      (hAlpha : Nonempty alpha) (hBeta : Nonempty beta) (e : alpha ≃ beta),
        e (choice alpha fAlpha hAlpha) = choice beta fBeta hBeta) := by
  dsimp only
  intro hNatural
  exact no_natural_finite_choice
    ⟨(fun _ _ h => Classical.choice h), hNatural⟩

#print axioms classical_choice_family_is_nonnatural

end D5.S3.ConceptDynamics.Attribution.ClassicalChoiceNonnaturality
