/- GID: D5/S3/ConceptDynamics/ExistenceNotionSeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ExistenceNotionSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Existence notions are represented by distinct predicates. -/

import Mathlib.Logic.IsEmpty.Basic

/-!
Dependent type theory represents several notions commonly called existence by
different types and predicates. Concrete positive and negative witnesses keep
those notions separate without selecting a philosophical doctrine.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ExistenceNotionSeparation

/-- A model exists when the externally supplied model predicate has a witness. -/
def HasModel {Model : Type} (isModel : Model → Prop) : Prop :=
  ∃ model, isModel model

/-- Realization is an externally supplied relation between a model and a
constructed object. -/
def Realized {Model X : Type} (realizes : Model → X → Prop)
    (model : Model) (x : X) : Prop :=
  realizes model x

/-- Formability need not provide a proof or construction; construction gives
`Nonempty`, while model existence and realization still depend on their
separately supplied predicates. Both sides of the latter distinctions have
explicit witnesses. -/
theorem mathematical_existence_notions_separate :
    (∃ P : Prop, ¬ P) ∧
    (∃ X : Type, IsEmpty X) ∧
    (∀ (X : Type), X → Nonempty X) ∧
    (∃ (Model : Type) (isModel : Model → Prop), HasModel isModel) ∧
    (∃ (Model : Type) (isModel : Model → Prop), ¬ HasModel isModel) ∧
    (∃ (Model X : Type) (model : Model) (x : X)
      (realizes : Model → X → Prop), ¬ Realized realizes model x) ∧
    (∃ (Model X : Type) (model : Model) (x : X)
      (realizes : Model → X → Prop), Realized realizes model x) := by
  refine ⟨⟨False, by simp⟩, ⟨Empty, inferInstance⟩,
    (fun X x => ⟨x⟩), ?_, ?_, ?_, ?_⟩
  · exact ⟨Unit, fun _ => True, (), trivial⟩
  · refine ⟨Empty, fun _ => True, ?_⟩
    simpa [HasModel] using
      (not_nonempty_iff.mpr (inferInstance : IsEmpty Empty))
  · exact ⟨Unit, Unit, (), (), fun _ _ => False, by simp [Realized]⟩
  · exact ⟨Unit, Unit, (), (), fun _ _ => True, trivial⟩

#print axioms mathematical_existence_notions_separate

end D5.S3.ConceptDynamics.ExistenceNotionSeparation
