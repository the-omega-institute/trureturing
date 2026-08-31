/- GID: D5/S3/ConceptDynamics/Sufficiency/AdditiveDescentDefectChainLaw
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Sufficiency/AdditiveDescentDefectChainLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Additive descent defects obey the composition chain law. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Algebra.Group.Hom.Basic

/- Library-search audit trail (2026-08-30):
   * Searches for additive descent defects, residual composition, chain laws,
     and the expanded `q_E`/`q_D` function equation across ConceptDynamics
     found no public theorem stating the arbitrary-defect identity.
   * Pinned Mathlib has no exact descent-defect theorem. The proof directly
     applies `map_sub` and `sub_add_sub_cancel`.
   * `Concept` is reused directly from `ConceptFiberDecomposition`.
   * The source types both candidate macroscopic maps as ordinary functions,
     but its displayed equality needs the second one to preserve subtraction.
     The theorem records that repair by bundling it as an `AddMonoidHom`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Sufficiency.AdditiveDescentDefectChainLaw

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- The source's additive defect `epsilon_F = q_D o F - Fbar o q_C`. -/
def epsilonF
    {X Y B_C B_D : Type*} [Sub B_D]
    (F : X -> Y) (q_C : Concept X B_C) (q_D : Concept Y B_D)
    (Fbar : B_C -> B_D) : X -> B_D :=
  (q_D ∘ F) - (Fbar ∘ q_C)

/-- The source's additive defect `epsilon_G = q_E o G - Gbar o q_D`. -/
def epsilonG
    {Y Z B_D B_E : Type*} [Sub B_E]
    (G : Y -> Z) (q_D : Concept Y B_D) (q_E : Concept Z B_E)
    (Gbar : B_D -> B_E) : Y -> B_E :=
  (q_E ∘ G) - (Gbar ∘ q_D)

/-- The source's composite additive defect
`epsilon_GF = q_E o G o F - Gbar o Fbar o q_C`. -/
def epsilonGF
    {X Y Z B_C B_D B_E : Type*} [Sub B_E]
    (F : X -> Y) (G : Y -> Z) (q_C : Concept X B_C)
    (q_E : Concept Z B_E) (Fbar : B_C -> B_D) (Gbar : B_D -> B_E) :
    X -> B_E :=
  (q_E ∘ G ∘ F) - (Gbar ∘ Fbar ∘ q_C)

/-- For successive processes, the additive defect of the composite is the
second-process defect pulled back along the first process plus the first-process
defect transported by the additive second macroscopic map. -/
theorem additive_descent_defect_chain_law
    {X Y Z B_C B_D B_E : Type*} [AddGroup B_D] [AddGroup B_E]
    (F : X -> Y) (G : Y -> Z)
    (q_C : Concept X B_C) (q_D : Concept Y B_D) (q_E : Concept Z B_E)
    (Fbar : B_C -> B_D) (Gbar : B_D →+ B_E) :
    epsilonGF F G q_C q_E Fbar (Gbar : B_D -> B_E) =
      (epsilonG G q_D q_E (Gbar : B_D -> B_E)) ∘ F +
        (Gbar : B_D -> B_E) ∘ epsilonF F q_C q_D Fbar := by
  funext x
  simp only [epsilonGF, epsilonG, epsilonF, Function.comp_apply,
    Pi.sub_apply, Pi.add_apply]
  rw [map_sub]
  exact (sub_add_sub_cancel _ _ _).symm

#print axioms additive_descent_defect_chain_law

end D5.S3.ConceptDynamics.Sufficiency.AdditiveDescentDefectChainLaw
