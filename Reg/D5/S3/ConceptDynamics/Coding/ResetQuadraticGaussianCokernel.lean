import D5.S3.ConceptDynamics.Coding.ResetQuadraticGaussianCokernel
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ConceptDynamics.Coding.ResetQuadraticGaussianCokernel
open D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy (VertexModule)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open private character_surjective from D5.S3.ConceptDynamics.Coding.ResetQuadraticGaussianCokernel
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.ResetQuadraticGaussianCokernel
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State m := VertexModule Sign (4 * m + 3)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ m := VertexModule Sign (4 * m + 3)
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (m : ℕ) (y : VertexModule Sign (4 * m + 3)),
    (∃ v, resetTwoStepDefect (4 * m + 3) v = r.readout () m y) ↔
      resetGaussianCharacter m y = 0

abbrev actual : Realization signature :=
  realize signature (fun _ _ y => y) (fun e => nomatch e)

abbrev bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private def positiveRow : VertexModule Sign 3 :=
  Classical.choose (character_surjective 0 (1, 0))

private theorem positive_character : resetGaussianCharacter 0 positiveRow = (1, 0) :=
  Classical.choose_spec (character_surjective 0 (1, 0))

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hz := (h 0 positiveRow).mp ⟨0, map_zero _⟩
  rw [positive_character] at hz
  have hh := congrArg Prod.fst hz
  norm_num at hh

def imageRegistration : Registration arena
    (∀ (m : ℕ) (y : VertexModule Sign (4 * m + 3)),
      (∃ v, resetTwoStepDefect (4 * m + 3) v = y) ↔ resetGaussianCharacter m y = 0) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨reset_two_step_three_mod_four_image, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨0, 0, positiveRow, ?_⟩
    intro h
    have hh := congrArg (resetGaussianCharacter 0) h
    change resetGaussianCharacter 0 0 = resetGaussianCharacter 0 positiveRow at hh
    rw [map_zero, positive_character] at hh
    have hz := congrArg Prod.fst hh
    norm_num at hz

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetQuadraticGaussianCokernel.reset_two_step_three_mod_four_image)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetQuadraticGaussianCokernel.image_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetQuadraticGaussianCokernel.imageRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨imageRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ y => y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetQuadraticGaussianCokernel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.ConceptDynamics.Coding.ResetQuadraticGaussianCokernel
