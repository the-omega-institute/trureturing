import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Finite.RobinRow01
import Reg.Support.DependentFamily

/-! The finite Robin inequality with a variable outer logarithm in its capacity. -/

namespace Reg.D5.S3.Arith.Robin.Finite.RobinRow01

open _root_.D5.S3.Arith.Robin.Finite.RobinRow01
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

/-- The outer logarithm varies while the divisor sum, integer multiplier,
and inner logarithm stay fixed. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 5040 < n → n ≤ 321253732800 →
    (ArithmeticFunction.sigma 1 n : ℝ) <
      Real.exp Real.eulerMascheroniConstant * n * R.readout () () (Real.log (n : ℝ))

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)

def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem zero_readout_fails : ¬ arena.Law zeroReadout := by
  intro h
  have hbad := h (n := 5041) (by norm_num) (by norm_num)
  change (ArithmeticFunction.sigma 1 5041 : ℝ) <
    Real.exp Real.eulerMascheroniConstant * (5041 : ℕ) * 0 at hbad
  rw [mul_zero] at hbad
  exact (not_lt_of_ge (Nat.cast_nonneg _)) hbad

def finiteRegistration : Registration arena (type_of% (@original_robin_through_row01)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@original_robin_through_row01, zeroReadout, zero_readout_fails⟩
  sensitivity := ⟨fun i => ⟨zeroReadout, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, zero_readout_fails⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    refine ⟨(), 1, 2, ?_⟩
    change Real.log 1 ≠ Real.log 2
    rw [Real.log_one]
    exact (Real.log_pos (by norm_num)).ne

def finiteAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_robin_through_row01)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.Finite.RobinRow01.original_robin_through_row01.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Finite.RobinRow01.finiteRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨finiteRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Finite.RobinRow01
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.Robin.Finite.RobinRow01
