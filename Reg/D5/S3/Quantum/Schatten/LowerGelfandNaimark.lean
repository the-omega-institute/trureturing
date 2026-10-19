import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Schatten.LowerGelfandNaimark
import Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm

namespace Reg.D5.S3.Quantum.Schatten.LowerGelfandNaimark
open _root_.D5.S3.Quantum.Schatten
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
open Matrix
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev arena : Arena where
  signature := relationSignature
  Law R := ∀ {n : ℕ} (C D : Matrix (Fin n) (Fin n) ℂ),
    IsUnit C.det → IsUnit D.det → ∀ I : Finset (Fin (Fintype.card (Fin n))),
    R.readout () ()
      (∏ i ∈ I, singularValuesSorted (C * D) i / singularValuesSorted D i)
      (∏ j : Fin I.card, singularValuesSorted C ⟨j.val, by
        have := Finset.card_le_card (Finset.subset_univ I)
        simp only [Finset.card_univ, Fintype.card_fin] at this ⊢
        omega⟩)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 0 1 1 (by simp) (by simp) ∅

def source_registration : Registration arena (type_of% @lower_gelfand_naimark_ratio) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@lower_gelfand_naimark_ratio, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law orderActual rejected
    rejected_law
  dependence := order_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@lower_gelfand_naimark_ratio) (Realization relationSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Schatten.LowerGelfandNaimark.unit
  realizationName := `Reg.D5.S3.Quantum.Schatten.LowerGelfandNaimark.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize relationSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.LowerGelfandNaimark
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Schatten.LowerGelfandNaimark
