import D5.S3.Arith.Recurrence.MandalMohanFibonacciPowerMean
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The exact rational quotient readout, with the exponent as parameter and the
prefix length as state. The law retains both directions and both lower bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Recurrence.MandalMohanFibonacciPowerMean

open _root_.D5.S3.Arith.Recurrence.MandalMohanFibonacciPowerMean
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℚ)

def actual : Realization signature :=
  realize signature (fun _ k n => quotient k n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n k : ℕ, 1 ≤ n → 3 ≤ k →
    ((∃ q : ℕ, R.readout () k n = (q : ℚ)) ↔ n = 1 ∨ n = 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 3 3 (by decide) (by decide)).mp ⟨1, rfl⟩
  exact (by decide : ¬ (3 = 1 ∨ 3 = 2)) bad

def family : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨3, 1, 2, ?_⟩
    change quotient 3 1 ≠ quotient 3 2
    norm_num [quotient, show Finset.Icc (1 : ℕ) 1 = {1} by decide,
      show Finset.Icc (1 : ℕ) 2 = {1, 2} by decide]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    result (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Recurrence.MandalMohanFibonacciPowerMean.result.__information_unit
  realizationName := `Reg.D5.S3.Arith.Recurrence.MandalMohanFibonacciPowerMean.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k n => quotient k n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Recurrence.MandalMohanFibonacciPowerMean
    definition := some {
      owner := `D5.S3.Arith.Recurrence.MandalMohanFibonacciPowerMean
      name := `D5.S3.Arith.Recurrence.MandalMohanFibonacciPowerMean.claim
      path := #[] }
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Arith.Recurrence.MandalMohanFibonacciPowerMean
