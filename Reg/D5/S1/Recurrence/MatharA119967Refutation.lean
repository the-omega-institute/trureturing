import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.MatharA119967Refutation
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S1.Recurrence.MatharA119967Refutation
open _root_.D5.S1.Recurrence.MatharA119967Refutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ n => residual n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 4 ≤ n → 0 < R.readout () () n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 4 (by decide)
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% @residual_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨residual_pos, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 4, 5, ?_⟩
    norm_num [actual, realize, residual, a, Finset.sum_range_succ, Nat.choose]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@residual_pos) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.MatharA119967Refutation.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.MatharA119967Refutation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => residual n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.MatharA119967Refutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Recurrence.MatharA119967Refutation
