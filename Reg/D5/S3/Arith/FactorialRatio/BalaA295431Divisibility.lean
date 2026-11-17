import D5.S3.Arith.FactorialRatio.BalaA295431Divisibility
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FactorialRatio.BalaA295431Divisibility
open _root_.D5.S3.Arith.FactorialRatio.BalaA295431Divisibility
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℚ)
def actual : Realization signature :=
  realize signature (fun _ _ n => ratio n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law X :=
    (∀ n : ℕ,
        (∃ z : ℤ, (z : ℚ) = 385 * X.readout () () n / (n + 1)) ∧
        (∃ z : ℤ, (z : ℚ) = 5 * X.readout () () n / (2 * n + 1)) ∧
        (∃ z : ℤ, (z : ℚ) = X.readout () () n / (3 * n + 1)) ∧
        (∃ z : ℤ, (z : ℚ) = 770 * X.readout () () n / ((n + 1) * (2 * n + 1) * (3 * n + 1))) ∧
        (∃ z : ℤ, (z : ℚ) = X.readout () () n / (12 * (n : ℚ) - 1)) ∧
        (∀ R : ℕ, 1 ≤ R → ∀ k : ℕ, 1 ≤ k ∧ k ≤ 3 →
          rising_denominator k n R ≠ 0 ∧
          ∃ z : ℤ, (z : ℚ) = (first_constant R : ℚ) * X.readout () () n / rising_denominator k n R) ∧
        (∀ R : ℕ, 1 ≤ R → signed_denominator n R ≠ 0 ∧
          ∃ z : ℤ, (z : ℚ) = (second_constant R : ℚ) * X.readout () () n / signed_denominator n R)) ∧
        X.readout () () 0 / (12 * (0 : ℚ) - 1) = -1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h.2
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change ratio 0 ≠ ratio 1
  norm_num [ratio]

def family : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@result) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Arith.FactorialRatio.BalaA295431Divisibility.result.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.BalaA295431Divisibility.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => ratio n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.BalaA295431Divisibility
    definition := some {
      owner := `D5.S3.Arith.FactorialRatio.BalaA295431Divisibility
      name := `D5.S3.Arith.FactorialRatio.BalaA295431Divisibility.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Arith.FactorialRatio.BalaA295431Divisibility
