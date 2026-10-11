import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ElevenSmooth
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.ElevenSmooth

open _root_.D5.S3.Arith.Robin.ElevenSmooth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

/-- One role: the outer logarithm of the Robin capacity `exp γ · log (log n)`. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The capacity's outer logarithm varies; the divisor ratio and the inner logarithm stay. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c d e : ℕ), 5040 < 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e →
    (ArithmeticFunction.sigma 1 (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e) : ℝ) /
        (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e : ℕ) <
      Real.exp Real.eulerMascheroniConstant *
        R.readout () () (Real.log (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e : ℕ))

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)

/-- The constant readout `0` replaces the outer logarithm. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 13 0 0 0 0 (by norm_num)
  change (ArithmeticFunction.sigma 1 (2 ^ 13 * 3 ^ 0 * 5 ^ 0 * 7 ^ 0 * 11 ^ 0) : ℝ) /
      ((2 ^ 13 * 3 ^ 0 * 5 ^ 0 * 7 ^ 0 * 11 ^ 0 : ℕ) : ℝ) <
    Real.exp Real.eulerMascheroniConstant * 0 at hbad
  rw [mul_zero] at hbad
  have hn : (0 : ℝ) < ((2 ^ 13 * 3 ^ 0 * 5 ^ 0 * 7 ^ 0 * 11 ^ 0 : ℕ) : ℝ) := by positivity
  have hs : (0 : ℝ) ≤ (ArithmeticFunction.sigma 1 (2 ^ 13 * 3 ^ 0 * 5 ^ 0 * 7 ^ 0 * 11 ^ 0) : ℝ) :=
    Nat.cast_nonneg _
  have := div_nonneg hs hn.le
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 1, 2, ?_⟩
  change Real.log 1 ≠ Real.log 2
  rw [Real.log_one]
  exact (Real.log_pos (by norm_num)).ne

def registration : Registration arena
    (∀ (a b c d e : ℕ), 5040 < 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e →
      (ArithmeticFunction.sigma 1 (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e) : ℝ) /
          (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e : ℕ) <
        Real.exp Real.eulerMascheroniConstant *
          Real.log (Real.log (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e : ℕ))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨robin_eleven_smooth, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

/-- The record binds the outer logarithm of the capacity through its raw source path,
with the dependent-family law and its four kernel obligations. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@robin_eleven_smooth)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.ElevenSmooth.robin_eleven_smooth.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ElevenSmooth.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ElevenSmooth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end

end Reg.D5.S3.Arith.Robin.ElevenSmooth
