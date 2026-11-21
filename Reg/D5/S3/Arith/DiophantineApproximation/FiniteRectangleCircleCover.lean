import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Arith.DiophantineApproximation.FiniteRectangleCircleCover
import Mathlib.Tactic

/-! Source registration for the squared phase-window width in the joint resonance bound. -/

namespace Reg.D5.S3.Arith.DiophantineApproximation.FiniteRectangleCircleCover

open LeanInformationAudit
open _root_.D5.S3.Arith.DiophantineApproximation.FiniteRectangleCircleCover (finite_rectangle_inverse)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (sensitivity)

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ r => r ^ (2 : ℕ)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 4) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N M : ℕ) (hN : 2 ≤ N) (hM : 2 ≤ M)
    (theta phi t w : ℝ) (hw : 0 < w ∧ w < 1)
    (hmiss : ¬ ∃ b d : ℕ, ∃ a : ℤ,
      N ≤ b ∧ b ≤ 2 * N ∧ M ≤ d ∧ d ≤ 2 * M ∧
      t < (b : ℝ) * theta + (d : ℝ) * phi - (a : ℝ) ∧
      (b : ℝ) * theta + (d : ℝ) * phi - (a : ℝ) < t + w),
    ∃ h j k : ℤ, 1 ≤ h ∧
      (N : ℝ) ^ 2 * ((h : ℝ) * theta - (j : ℝ)) ^ 2 +
        (M : ℝ) ^ 2 * ((h : ℝ) * phi - (k : ℝ)) ^ 2 +
        R.readout () () w * (h : ℝ) ^ 2 ≤ 11 / 3

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hmiss : ¬ ∃ b d : ℕ, ∃ a : ℤ,
      2 ≤ b ∧ b ≤ 2 * 2 ∧ 2 ≤ d ∧ d ≤ 2 * 2 ∧
      (0 : ℝ) < (b : ℝ) * 0 + (d : ℝ) * 0 - (a : ℝ) ∧
      (b : ℝ) * 0 + (d : ℝ) * 0 - (a : ℝ) < 0 + (1 / 2 : ℝ) := by
    rintro ⟨b, d, a, _, _, _, _, ha0, ha1⟩
    simp only [mul_zero, add_zero, zero_sub] at ha0 ha1
    have ha0z : (0 : ℤ) < -a := by exact_mod_cast ha0
    have ha1z : (1 : ℤ) ≤ -a := by omega
    have ha1r : (1 : ℝ) ≤ -(a : ℝ) := by exact_mod_cast ha1z
    linarith only [ha1, ha1r]
  obtain ⟨q, j, k, hq, hbound⟩ :=
    h 2 2 (by norm_num) (by norm_num) 0 0 0 (1 / 2) (by norm_num) hmiss
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqSq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hqR 2
  change (2 : ℝ) ^ 2 * ((q : ℝ) * 0 - (j : ℝ)) ^ 2 +
    (2 : ℝ) ^ 2 * ((q : ℝ) * 0 - (k : ℝ)) ^ 2 + 4 * (q : ℝ) ^ 2 ≤ 11 / 3 at hbound
  simp only [mul_zero, zero_sub, neg_sq] at hbound
  nlinarith only [hbound, hqSq, sq_nonneg (j : ℝ), sq_nonneg (k : ℝ)]

def family : Registration arena (type_of% (@finite_rectangle_inverse)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_rectangle_inverse, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1 / 4, 1 / 2, ?_⟩
    change ((1 : ℝ) / 4) ^ (2 : ℕ) ≠ ((1 : ℝ) / 2) ^ (2 : ℕ)
    norm_num

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@finite_rectangle_inverse) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.DiophantineApproximation.FiniteRectangleCircleCover.finite_rectangle_inverse.__information_unit
  realizationName := `Reg.D5.S3.Arith.DiophantineApproximation.FiniteRectangleCircleCover.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r => r ^ (2 : ℕ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.DiophantineApproximation.FiniteRectangleCircleCover
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.DiophantineApproximation.FiniteRectangleCircleCover
