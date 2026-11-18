import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Raney.ExactBinaryRuns
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S1.Recurrence.Raney.ExactBinaryRuns

open TrureTuring.Raney
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Nat) (fun _ => ZMod 2)

def actual : Realization signature :=
  realize signature (fun _ _ n => (raneyNumber 3 1 n : ZMod 2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ZMod 2)) (fun e => nomatch e)

/-- One varying literal-sequence observation, shared by every interval clause. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ first last : Nat,
      IsMaximalDeltaInterval {0} (fun n => R.readout () () n) first last →
      ∃ m : Nat, 2 ≤ m ∧ last + 1 - first = 2 ^ m / 3 ∧
        (2 ^ (m + 1) + 2) / 3 ≤ first) ∧
    (∀ m : Nat, 2 ≤ m →
      IsMaximalDeltaInterval {0} (fun n => R.readout () () n)
        ((2 ^ (m + 1) + 2) / 3) (2 ^ m - 1) ∧
      (2 ^ m - 1) + 1 - ((2 ^ (m + 1) + 2) / 3) = 2 ^ m / 3 ∧
      ∀ first last : Nat,
        IsMaximalDeltaInterval {0} (fun n => R.readout () () n) first last →
        first < (2 ^ (m + 1) + 2) / 3 → last + 1 - first < 2 ^ m / 3) ∧
    (∀ m k : Nat, 2 ≤ m → m < k → 2 ^ m / 3 < 2 ^ k / 3)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h.2.1 2 (by decide)).1
  change IsMaximalDeltaInterval {0} (fun _ : Nat => (1 : ZMod 2)) 3 3 at hb
  have hz : (1 : ZMod 2) = 0 := Finset.mem_singleton.mp (hb.2.1 3 le_rfl le_rfl)
  exact one_ne_zero hz

def family : Registration arena (type_of% @raney_binary_exact_zero_run_spectrum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨raney_binary_exact_zero_run_spectrum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 3, ?_⟩
    change (raneyNumber 3 1 0 : ZMod 2) ≠ (raneyNumber 3 1 3 : ZMod 2)
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@raney_binary_exact_zero_run_spectrum) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Raney.ExactBinaryRuns.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Raney.ExactBinaryRuns.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (raneyNumber 3 1 n : ZMod 2))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Raney.ExactBinaryRuns
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "domain", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S1.Recurrence.Raney.ExactBinaryRuns
