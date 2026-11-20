import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.CommonBlockWeights
import Reg.Support.SingleDependentReadout

/-! The universal grouped allocation law observes the digit capacity. -/

namespace Reg.D5.S3.Combinatorics.Partitions.CommonBlockWeights
open _root_.D5.S3.Combinatorics.Partitions.CommonBlockWeights
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ k n => (k + 1)^n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k n q : ℕ}, 0 < k → k*q+1 ≤ R.readout () k n →
    ∃ w : Fin n → ℕ, (∑ j, w j = q) ∧ CoversAllocations k q w

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨w, total, _⟩ := h (k := 1) (n := 0) (q := 1) (by decide) (by decide)
  simpa using total

def family : Registration arena (type_of% (@common_weights_for_allocations)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨common_weights_for_allocations, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    exact (by decide : (1 : ℕ) ≠ 2)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@common_weights_for_allocations) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Partitions.CommonBlockWeights.information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.CommonBlockWeights.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k n => (k + 1)^n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.CommonBlockWeights
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Partitions.CommonBlockWeights
