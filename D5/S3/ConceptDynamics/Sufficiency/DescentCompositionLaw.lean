/- GID: D5/S3/ConceptDynamics/Sufficiency/DescentCompositionLaw
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Sufficiency/DescentCompositionLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact descents through two successive readouts compose. -/

import D5.S3.ConceptDynamics.Sufficiency.FiniteWindowMinimalSufficiency

/- Library-search audit trail (2026-08-25):
   * Exact repository hit `descent_composes` states composition through the
     family's canonical `Semiconjugates` predicate and is applied directly.
   * That imported theorem directly applies the pinned-Mathlib exact hit
     `Function.Semiconj.trans` from `Mathlib.Logic.Function.Conjugate`.
   * Searches for this atom id, `descent_composition`, and composition/descent
     variants found no existing digestion receipt or public equation wrapper.
   * The Observer, ConceptDynamics, and Entropy families were searched before
     authoring. This module imports the canonical family result and introduces
     no replacement interface or residual definition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Sufficiency.DescentCompositionLaw

open D5.S3.ConceptDynamics.Sufficiency.FiniteWindowMinimalSufficiency

/-- If `q` intertwines `F` with `Fbar` and `r` intertwines `Fbar` with
`Ftilde`, their composite intertwines `F` with `Ftilde`. -/
theorem descent_composition_law
    {X B C : Type*} (F : X -> X) (Fbar : B -> B) (Ftilde : C -> C)
    (q : X -> B) (r : B -> C)
    (hq : q ∘ F = Fbar ∘ q) (hr : r ∘ Fbar = Ftilde ∘ r) :
    (r ∘ q) ∘ F = Ftilde ∘ (r ∘ q) := by
  have hqSemiconjugates : Semiconjugates q F Fbar := fun x => congrFun hq x
  have hrSemiconjugates : Semiconjugates r Fbar Ftilde := fun x => congrFun hr x
  exact Function.semiconj_iff_comp_eq.mp
    (descent_composes F Fbar Ftilde q r hqSemiconjugates hrSemiconjugates)

#print axioms descent_composition_law

end D5.S3.ConceptDynamics.Sufficiency.DescentCompositionLaw
