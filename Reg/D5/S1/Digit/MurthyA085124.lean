import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.MurthyA085124
import Reg.Support.SingleDependentReadout

set_option autoImplicit false

namespace Reg.D5.S1.Digit.MurthyA085124

open _root_.D5.S1.Digit.MurthyA085124
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a085124 n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The full source telescope; the positivity observation is the selected occurrence. -/
def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 0 < n →
    ((∃ N, admissible n N) ↔
      (∀ p : ℕ, Nat.Prime p → p ∣ n → p ≤ 7) ∧ ¬ 10 ∣ n) ∧
    (0 < R.readout () () n ↔
      (∀ p : ℕ, Nat.Prime p → p ∣ n → p ≤ 7) ∧ ¬ 10 ∣ n) ∧
    (a085124 n = 0 ↔ ¬ ∃ N, admissible n N) ∧
    (0 < a085124 n → admissible n (a085124 n) ∧
      ∀ N, admissible n N → a085124 n ≤ N)

private theorem one_qualifies : admissible 1 1 := by
  norm_num [admissible, _root_.D5.S1.Digit.DigitProductSlices.digitProduct]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := (result 1 (by decide)).1.mp ⟨1, one_qualifies⟩
  have hf := (h 1 (by decide)).2.1.mpr hc
  change 0 < (0 : ℕ) at hf
  omega

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (1 : ℕ), (10 : ℕ), ?_⟩
    change a085124 1 ≠ a085124 10
    have hc := (result 1 (by decide)).1.mp ⟨1, one_qualifies⟩
    have hp := (result 1 (by decide)).2.1.mpr hc
    have hz : a085124 10 = 0 := (result 10 (by decide)).2.2.1.mpr (by
      intro h
      exact ((result 10 (by decide)).1.mp h).2 dvd_rfl)
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Digit.MurthyA085124.auditUnit
  realizationName := `Reg.D5.S1.Digit.MurthyA085124.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a085124 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Digit.MurthyA085124
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S1.Digit.MurthyA085124
