import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.RoundedNormBoundedError
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S1.Recurrence.RoundedNormBoundedError

open _root_.D5.S0.Tower.Tribonacci.Values (tribonacciConstant)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Asymptotics Filter Real

set_option autoImplicit false
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℝ)
    (fun _ => (ℕ → ℝ) → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f g => f =O[atTop] g) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The original statement is retained; the readout observes the bounded error of the
two-term rounded norm. -/
abbrev arena : Arena where
  signature := signature
  Law Q :=
    (∀ x : ℕ → ℕ,
      (∀ n, (x (n + 2) : ℤ) = round (Real.sqrt ((x n : ℝ) ^ 2 + (x (n + 1) : ℝ) ^ 2))) →
      ((∃ C : ℝ, 0 < C ∧
        Q.readout () () (fun n => (x n : ℝ) - C * Real.sqrt goldenRatio ^ n)
          (fun _ => (1 : ℝ)) ∧
        (fun n => (x (n + 1) : ℝ) / x n - Real.sqrt goldenRatio) =O[atTop]
          (fun n => (Real.sqrt goldenRatio ^ n)⁻¹)) ↔ 2 ≤ max (x 0) (x 1))) ∧
    (∀ x : ℕ → ℕ,
      (∀ n, (x (n + 3) : ℤ) =
        round (Real.sqrt ((x n : ℝ) ^ 2 + (x (n + 1) : ℝ) ^ 2 + (x (n + 2) : ℝ) ^ 2))) →
      ((∃ C : ℝ, 0 < C ∧
        (fun n => (x n : ℝ) - C * Real.sqrt tribonacciConstant ^ n) =O[atTop]
          (fun _ => (1 : ℝ)) ∧
        (fun n => (x (n + 1) : ℝ) / x n - Real.sqrt tribonacciConstant) =O[atTop]
          (fun n => (Real.sqrt tribonacciConstant ^ n)⁻¹)) ↔ 0 < x 0 + x 1 + x 2))

/-- A two-term rounded-norm sequence with seed `(2, 2)`. -/
private def seq2 : ℕ → ℕ
  | 0 => 2
  | 1 => 2
  | n + 2 => (round (Real.sqrt ((seq2 n : ℝ) ^ 2 + (seq2 (n + 1) : ℝ) ^ 2))).toNat

private theorem seq2_rec (n : ℕ) :
    (seq2 (n + 2) : ℤ) = round (Real.sqrt ((seq2 n : ℝ) ^ 2 + (seq2 (n + 1) : ℝ) ^ 2)) := by
  set y := Real.sqrt ((seq2 n : ℝ) ^ 2 + (seq2 (n + 1) : ℝ) ^ 2) with hy
  have h := abs_sub_round y
  have h0 : 0 ≤ y := Real.sqrt_nonneg _
  have hr : (-1 : ℝ) < (round y : ℝ) := by
    linarith [(abs_le.mp h).1, (abs_le.mp h).2]
  have hr' : (-1 : ℤ) < round y := by exact_mod_cast hr
  have hnn : 0 ≤ round y := by omega
  show ((round y).toNat : ℤ) = round y
  exact Int.toNat_of_nonneg hnn

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hlaw
  have h := ((hlaw.1 seq2 seq2_rec).mpr (by simp [seq2]))
  obtain ⟨_, _, hF, _⟩ := h
  exact hF

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), fun _ => 0, fun _ => 1, ?_⟩
  intro h
  have hh := congrFun h (fun _ => 0)
  simp only [actual, realize] at hh
  have h0 : (fun _ : ℕ => (0 : ℝ)) =O[atTop] (fun _ : ℕ => (0 : ℝ)) := isBigO_zero _ _
  rw [hh, isBigO_zero_right_iff] at h0
  obtain ⟨n, hn⟩ := eventually_atTop.mp h0
  exact one_ne_zero (hn n le_rfl)

def family : Registration arena
    (type_of% (@_root_.D5.S1.Recurrence.RoundedNormBoundedError.result))
    where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S1.Recurrence.RoundedNormBoundedError.result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Recurrence.RoundedNormBoundedError.result)
    (Realization signature) Unit Unit where
  unitName := `D5.S1.Recurrence.RoundedNormBoundedError.result.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.RoundedNormBoundedError.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f g => f =O[atTop] g) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.RoundedNormBoundedError
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "fn", "arg", "arg", "body", "arg", "fn", "arg", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S1.Recurrence.RoundedNormBoundedError
