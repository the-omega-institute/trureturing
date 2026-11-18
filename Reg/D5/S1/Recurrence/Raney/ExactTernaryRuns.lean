import D5.S1.Recurrence.Raney.ExactTernaryRuns
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! # Source-bound readout for the complete ternary Raney theorem -/

namespace Reg.D5.S1.Recurrence.Raney.ExactTernaryRuns

open TrureTuring.Raney
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Nat) (fun _ => ZMod 3)

def actual : Realization signature :=
  realize signature (fun _ _ n => (raneyNumber 3 1 n : ZMod 3)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

open Classical in
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ n : Nat, R.readout () () n =
      if ∃ m : Nat, 2 * n + 1 = 3 ^ m then 1 else 0) ∧
    (∀ first last : Nat,
      IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod 3)) first last ↔
        ∃ m : Nat, 1 ≤ m ∧ first = (3 ^ m + 1) / 2 ∧
          last = (3 ^ (m + 1) - 3) / 2) ∧
    (∀ m : Nat, 1 ≤ m →
      (3 ^ (m + 1) - 3) / 2 + 1 - (3 ^ m + 1) / 2 = 3 ^ m - 1) ∧
    StrictMono (fun m : Nat => 3 ^ m - 1) ∧
    (∀ m : Nat, 1 ≤ m → ∀ first last : Nat,
      IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod 3)) first last →
      first ≤ (3 ^ m + 1) / 2 → last + 1 - first ≤ 3 ^ m - 1) ∧
    (∀ m : Nat, 1 ≤ m → ∀ first last : Nat,
      IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod 3)) first last →
      last + 1 - first = 3 ^ m - 1 →
        first = (3 ^ m + 1) / 2 ∧ last = (3 ^ (m + 1) - 3) / 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h.1 0
  have hex : ∃ m : Nat, 2 * 0 + 1 = 3 ^ m := ⟨0, by decide⟩
  simp [rejected, realize, hex] at hzero

def family : Registration arena (type_of% @raney_three_exact_zero_runs) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨raney_three_exact_zero_runs, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 2, ?_⟩
    change (raneyNumber 3 1 0 : ZMod 3) ≠ (raneyNumber 3 1 2 : ZMod 3)
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@raney_three_exact_zero_runs) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Raney.ExactTernaryRuns.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Raney.ExactTernaryRuns.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (raneyNumber 3 1 n : ZMod 3))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Raney.ExactTernaryRuns
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S1.Recurrence.Raney.ExactTernaryRuns
