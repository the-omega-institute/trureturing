import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Arith.DiophantineApproximation.FiniteIntegerBoxThreeCircleCover
import Mathlib.Tactic

/-! Source registration for the squared phase-window width in the joint resonance bound. -/

namespace Reg.D5.S3.Arith.DiophantineApproximation.FiniteIntegerBoxThreeCircleCover

open LeanInformationAudit
open _root_.D5.S3.Arith.DiophantineApproximation.FiniteIntegerBoxThreeCircleCover
  (finite_integer_box_inverse_three)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (sensitivity)
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ w => w ^ (2 : ℕ)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 5) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N : Fin 3 → ℤ) (_hN : ∀ i, 1 ≤ N i)
    (θ : Fin 3 → ℝ) (t w : ℝ) (_hw : 0 < w)
    (hmiss : ¬ ∃ (b : Fin 3 → ℤ) (m : ℤ),
      (∀ i, N i ≤ b i ∧ b i ≤ 2 * N i) ∧
      t < (∑ i, (b i : ℝ) * θ i) - (m : ℝ) ∧
      (∑ i, (b i : ℝ) * θ i) - (m : ℝ) < t + w),
    ∃ (h : ℤ) (j : Fin 3 → ℤ), 1 ≤ h ∧
      (∑ i, ((N i : ℝ) + 2) ^ 2 * ((h : ℝ) * θ i - (j i : ℝ)) ^ 2) +
        R.readout () () w * (h : ℝ) ^ 2 ≤ 43 / 9

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let N : Fin 3 → ℤ := fun _ => 1
  let θ : Fin 3 → ℝ := fun _ => 0
  have hN (i : Fin 3) : 1 ≤ N i := le_rfl
  have hmiss : ¬ ∃ (b : Fin 3 → ℤ) (m : ℤ),
      (∀ i, N i ≤ b i ∧ b i ≤ 2 * N i) ∧
      (0 : ℝ) < (∑ i, (b i : ℝ) * θ i) - (m : ℝ) ∧
      (∑ i, (b i : ℝ) * θ i) - (m : ℝ) < 0 + (1 / 2 : ℝ) := by
    rintro ⟨b, m, _, hlo, hhi⟩
    simp only [θ, mul_zero, Finset.sum_const_zero, zero_sub, zero_add] at hlo hhi
    have hm : (0 : ℤ) < -m := by exact_mod_cast hlo
    have hmOne : (1 : ℤ) ≤ -m := by omega
    have hmReal : (1 : ℝ) ≤ -(m : ℝ) := by exact_mod_cast hmOne
    linarith only [hhi, hmReal]
  obtain ⟨h, j, hh, hbound⟩ := law N hN θ 0 (1 / 2) (by norm_num) hmiss
  change (∑ i, ((N i : ℝ) + 2) ^ 2 * ((h : ℝ) * θ i - (j i : ℝ)) ^ 2) +
    5 * (h : ℝ) ^ 2 ≤ (43 / 9 : ℝ) at hbound
  have hsum : 0 ≤ ∑ i, ((N i : ℝ) + 2) ^ 2 * ((h : ℝ) * θ i - (j i : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hhReal : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hhSq : (1 : ℝ) ≤ (h : ℝ) ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ (zero_le_one : (0 : ℝ) ≤ 1) hhReal 2
  have hlower : (5 : ℝ) ≤ 5 * (h : ℝ) ^ 2 := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hhSq (show (0 : ℝ) ≤ 5 by norm_num)
  have hupper : 5 * (h : ℝ) ^ 2 ≤ (43 / 9 : ℝ) :=
    (le_add_of_nonneg_left hsum).trans hbound
  exact (by norm_num : ¬ (5 : ℝ) ≤ 43 / 9) (hlower.trans hupper)

def family : Registration arena (type_of% (@finite_integer_box_inverse_three)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_integer_box_inverse_three, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℝ) ^ (2 : ℕ) ≠ (1 : ℝ) ^ (2 : ℕ)
    norm_num

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@finite_integer_box_inverse_three) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.DiophantineApproximation.FiniteIntegerBoxThreeCircleCover.finite_integer_box_inverse_three.__information_unit
  realizationName := `Reg.D5.S3.Arith.DiophantineApproximation.FiniteIntegerBoxThreeCircleCover.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => w ^ (2 : ℕ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.DiophantineApproximation.FiniteIntegerBoxThreeCircleCover
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Through the seven hypotheses and inputs, the two witnesses, and the
      -- right conjunct, select the left factor of the final summand.
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.DiophantineApproximation.FiniteIntegerBoxThreeCircleCover
