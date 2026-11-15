import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.Admissibility.MurthyA077739Classification
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S1.Digit.Admissibility.MurthyA077739Classification
open _root_.D5.S1.Digit.Admissibility.MurthyA077739Classification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 1 ≤ n →
    (R.readout () () n = 0 ↔ n = 11 ∨ n = 17 ∨ n = 19)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by decide)
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 11, 1, ?_⟩
    change a 11 ≠ a 1
    have hz : a 11 = 0 := (result 11 (by decide)).mpr (Or.inl rfl)
    have hn : a 1 ≠ 0 := by
      intro h
      have hh := (result 1 (by decide)).mp h
      omega
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Digit.Admissibility.MurthyA077739Classification.auditUnit
  realizationName := `Reg.D5.S1.Digit.Admissibility.MurthyA077739Classification.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Digit.Admissibility.MurthyA077739Classification
    definition := some {
      owner := `D5.S1.Digit.Admissibility.MurthyA077739Classification
      name := `D5.S1.Digit.Admissibility.MurthyA077739Classification.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S1.Digit.Admissibility.MurthyA077739Classification
