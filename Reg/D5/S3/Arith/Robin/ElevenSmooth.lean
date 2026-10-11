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

/-- The two-bracket lower bound: the outer logarithm of the conclusion is the varied readout. -/
abbrev loglogOfArena : Arena where
  signature := signature
  Law R := ∀ (t mid lo y₁ y₂ : Real) (k₁ k₂ : Nat),
    t = (2 : Real) ^ k₁ * y₁ → 1 <= k₁ → 1 <= y₁ → y₁ < 2 →
    mid < (k₁ : Real) * (6931471803 / 10000000000 : Real) +
      D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial ((y₁ - 1) / (y₁ + 1)) 4 →
    mid = (2 : Real) ^ k₂ * y₂ → 1 <= k₂ → 1 <= y₂ → y₂ < 2 →
    lo < (k₂ : Real) * (6931471803 / 10000000000 : Real) +
      D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial ((y₂ - 1) / (y₂ + 1)) 4 →
    0 < mid → lo < R.readout () () (Real.log t)

theorem rejected_loglogOf_law : ¬ loglogOfArena.Law rejected := by
  intro h
  have hbad := h 5040 (341 / 40) (1071 / 500) (315 / 256) (341 / 320) 12 3 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ])
    (by norm_num)
  change (1071 / 500 : Real) < 0 at hbad
  norm_num at hbad

def loglogOfRegistration : Registration loglogOfArena
    (∀ (t mid lo y₁ y₂ : Real) (k₁ k₂ : Nat),
      t = (2 : Real) ^ k₁ * y₁ → 1 <= k₁ → 1 <= y₁ → y₁ < 2 →
      mid < (k₁ : Real) * (6931471803 / 10000000000 : Real) +
        D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial ((y₁ - 1) / (y₁ + 1)) 4 →
      mid = (2 : Real) ^ k₂ * y₂ → 1 <= k₂ → 1 <= y₂ → y₂ < 2 →
      lo < (k₂ : Real) * (6931471803 / 10000000000 : Real) +
        D5.S3.Arith.GoldenResource.RobinRationalBasis.atanhPartial ((y₂ - 1) / (y₂ + 1)) 4 →
      0 < mid → lo < Real.log (Real.log t)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨loglog_of, rejected, rejected_loglogOf_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_loglogOf_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

/-- One interval of the table: the outer logarithm of the conclusion is the varied readout. -/
abbrev finishArena : Arena where
  signature := signature
  Law R := ∀ {n t K : Nat} {l : Real}, 1 < t → t ≤ n → 0 < l →
    l < Real.log (Real.log (t : Real)) → (K : Real) / 100 ≤ 89 / 50 * l →
    100 * ArithmeticFunction.sigma 1 n ≤ K * n →
    (ArithmeticFunction.sigma 1 n : Real) / n <
      Real.exp Real.eulerMascheroniConstant * R.readout () () (Real.log (n : Real))

theorem rejected_finish_law : ¬ finishArena.Law rejected := by
  intro h
  have hs : ArithmeticFunction.sigma 1 8192 = 16383 := by decide +kernel
  have hbad := h (n := 8192) (t := 5040) (K := 381) (l := 1071 / 500) (by norm_num)
    (by norm_num) (by norm_num) (by exact_mod_cast loglog_5040) (by norm_num)
    (by rw [hs]; norm_num)
  change (ArithmeticFunction.sigma 1 8192 : Real) / (8192 : Nat) <
    Real.exp Real.eulerMascheroniConstant * 0 at hbad
  rw [mul_zero, hs] at hbad
  norm_num at hbad

def finishRegistration : Registration finishArena
    (∀ {n t K : Nat} {l : Real}, 1 < t → t ≤ n → 0 < l →
      l < Real.log (Real.log (t : Real)) → (K : Real) / 100 ≤ 89 / 50 * l →
      100 * ArithmeticFunction.sigma 1 n ≤ K * n →
      (ArithmeticFunction.sigma 1 n : Real) / n <
        Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : Real))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finish, rejected, rejected_finish_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_finish_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

/-- The two helper records bind the outer logarithm through its raw source path. -/
def loglogOfAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@loglog_of)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.ElevenSmooth.loglog_of.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ElevenSmooth.loglogOfRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨loglogOfArena⟩
  objectArena := .source ⟨loglogOfArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source loglogOfArena ⟨loglogOfRegistration⟩
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
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def finishAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@finish)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.ElevenSmooth.finish.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ElevenSmooth.finishRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨finishArena⟩
  objectArena := .source ⟨finishArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source finishArena ⟨finishRegistration⟩
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
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "arg", "fn"]
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
