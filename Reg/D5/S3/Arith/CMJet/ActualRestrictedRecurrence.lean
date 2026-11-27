import D5.S3.Arith.CMJet.ActualRestrictedRecurrence
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Observation of the section jet as the column varies. -/

noncomputable section

namespace Reg.D5.S3.Arith.CMJet.ActualRestrictedRecurrence

open LeanInformationAudit
open _root_.D5.S3.Arith.CMJet.ActualRestricted
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

abbrev readoutSignature : Signature :=
  signature ℕ (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization readoutSignature :=
  realize readoutSignature (fun _ h j => jet h 0 j) (fun e => nomatch e)

def rejected : Realization readoutSignature :=
  realize readoutSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := readoutSignature
  Law R := ∀ (h j : ℕ), R.readout () h j = if j = 0 then 1 else 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 0 0
  norm_num [rejected, realize] at hbad

def family : Registration arena (type_of% @jet_zero_order) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@jet_zero_order, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    change ∃ (h : ℕ) (l r : ℕ), jet h 0 l ≠ jet h 0 r
    refine ⟨0, 0, 1, ?_⟩
    simp [jet_zero_order]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@jet_zero_order) (Realization readoutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.CMJet.ActualRestrictedRecurrence.unit
  realizationName := `Reg.D5.S3.Arith.CMJet.ActualRestrictedRecurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize readoutSignature
    (fun _ h j => jet h 0 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.CMJet.ActualRestrictedRecurrence
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.CMJet.ActualRestrictedRecurrence
