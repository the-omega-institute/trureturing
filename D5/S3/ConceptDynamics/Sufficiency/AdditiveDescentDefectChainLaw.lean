/- GID: D5/S3/ConceptDynamics/Sufficiency/AdditiveDescentDefectChainLaw
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Sufficiency/AdditiveDescentDefectChainLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Additive descent defects obey the composition chain law. -/

import D5.S3.ConceptDynamics.Sufficiency.DescentCompositionLaw
import Mathlib.Algebra.Group.Hom.Basic

/- Library-search audit trail (2026-08-30):
   * Searches for additive descent defects, residual composition, chain laws,
     and the expanded `q_E`/`q_D` function equation across ConceptDynamics
     found no public theorem stating the arbitrary-defect identity.
   * `descent_composition_law` is the exact zero-defect result. It is imported
     as the frozen family owner, but its hypotheses do not state this theorem's
     residual equation.
   * Pinned Mathlib has no exact descent-defect theorem. The proof directly
     applies `map_sub` and `sub_add_sub_cancel`.
   * `Concept` is reused from the family's `ConceptFiberDecomposition`; this
     module introduces no residual definition, carrier, or private lemma. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Sufficiency.AdditiveDescentDefectChainLaw

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- For successive processes, the additive defect of the composite is the
first defect transported through the second process plus the image of the
second defect under the additive macroscopic map. -/
theorem additive_descent_defect_chain_law
    {X Y Z B_C B_D B_E : Type*} [AddGroup B_D] [AddGroup B_E]
    (F : X -> Y) (G : Y -> Z)
    (q_C : Concept X B_C) (q_D : Concept Y B_D) (q_E : Concept Z B_E)
    (Fbar : B_C -> B_D) (Gbar : B_D →+ B_E) :
    (q_E ∘ G ∘ F) - ((Gbar : B_D -> B_E) ∘ Fbar ∘ q_C) =
      (((q_E ∘ G) - ((Gbar : B_D -> B_E) ∘ q_D)) ∘ F) +
        ((Gbar : B_D -> B_E) ∘ ((q_D ∘ F) - (Fbar ∘ q_C))) := by
  funext x
  change q_E (G (F x)) - Gbar (Fbar (q_C x)) =
    (q_E (G (F x)) - Gbar (q_D (F x))) +
      Gbar (q_D (F x) - Fbar (q_C x))
  rw [map_sub]
  exact (sub_add_sub_cancel _ _ _).symm

#print axioms additive_descent_defect_chain_law

end D5.S3.ConceptDynamics.Sufficiency.AdditiveDescentDefectChainLaw
