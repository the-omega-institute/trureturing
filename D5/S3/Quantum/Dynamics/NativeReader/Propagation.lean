/- GID: D5/S3/Quantum/Dynamics/NativeReader/Propagation
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/NativeReader/Propagation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full-carrier native pulse and fifteen-call propagation estimates. -/

import D5.S3.Quantum.Dynamics.NativeReader.Global
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Floor.Semiring

/-! Operator estimates use the Euclidean operator norm on all 610 coordinates. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.Quantum.Dynamics.NativeReader
open Matrix
open scoped Matrix.Norms.L2Operator
open D5.S3.Quantum.Measurement.OneSidedGoldenHistory (block block_mul block_star)

instance : Nonempty Extended := ⟨fullCarrierEquiv.symm ⟨readySource, readyTail (readySource.1 9)⟩⟩

private def fullCore (j : Fin 5) (t : ℝ) : Matrix Extended Extended ℂ :=
  1 + (unitPhase t - 1) • fullProjection j

private theorem fullCore_unitary (j : Fin 5) (t : ℝ) :
    fullCore j t ∈ unitary (Matrix Extended Extended ℂ) := by
  have core_unitary (P : Matrix Extended Extended ℂ) (hp : P * P = P)
      (hh : P.conjTranspose = P) :
      1 + (unitPhase t - 1) • P ∈ unitary (Matrix Extended Extended ℂ) := by
    have hz : (unitPhase t - 1) + (star (unitPhase t) - 1) +
        (star (unitPhase t) - 1) * (unitPhase t - 1) = 0 := by
      linear_combination unitPhase_star t
    have hu : (1 + (unitPhase t - 1) • P).conjTranspose *
        (1 + (unitPhase t - 1) • P) = 1 := by
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one,
        Matrix.conjTranspose_smul, hh, star_sub, star_one]
      calc
        _ = 1 + ((unitPhase t - 1) + (star (unitPhase t) - 1) +
            (star (unitPhase t) - 1) * (unitPhase t - 1)) • P := by
          rw [add_mul (1 : Matrix Extended Extended ℂ), one_mul,
            mul_add ((star (unitPhase t) - 1) • P), mul_one,
            Matrix.smul_mul (star (unitPhase t) - 1),
            Matrix.mul_smul P (unitPhase t - 1), hp, smul_smul]
          module
        _ = 1 := by rw [hz, zero_smul, add_zero]
    exact Unitary.mem_iff.mpr ⟨hu, mul_eq_one_comm.mp hu⟩
  exact core_unitary (fullProjection j) (fullProjection_laws j).2 (fullProjection_laws j).1

/-- Every full native pulse is unitary on the complete carrier. -/
theorem fullPulse_unitary (j : Fin 5) (t : ℝ) :
    fullPulse j t ∈ unitary (Matrix Extended Extended ℂ) := by
  exact Unitary.smul_mem_of_mem
    (Unitary.mem_iff.mpr ⟨unitPhase_star t, by rw [mul_comm]; exact unitPhase_star t⟩)
    (fullCore_unitary j t)

private theorem phase_norm (t : ℝ) : ‖unitPhase t‖ = 1 := by
  simp [unitPhase, Complex.norm_exp]

private theorem phase_difference (t u : ℝ) : ‖unitPhase t - unitPhase u‖ ≤ |t - u| := by
  have he : unitPhase t - unitPhase u = unitPhase u * (unitPhase (t - u) - 1) := by
    have h : unitPhase t = unitPhase u * unitPhase (t - u) := by
      simp only [unitPhase, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [h]
    ring
  rw [he, norm_mul, phase_norm, one_mul]
  simpa [unitPhase, mul_comm] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t - u))

private theorem projection_norm (j : Fin 5) : ‖fullProjection j‖ ≤ 1 := by
  exact IsStarProjection.norm_le (fullProjection j) ⟨(fullProjection_laws j).2, (fullProjection_laws j).1⟩

/-- A changed full pulse has operator error at most twice its angle change. -/
theorem fullPulse_difference_bound (j : Fin 5) (t u : ℝ) :
    ‖fullPulse j t - fullPulse j u‖ ≤ 2 * |t - u| := by
  have he : fullPulse j t - fullPulse j u =
      (unitPhase t - unitPhase u) • fullCore j t +
        unitPhase u • ((unitPhase t - unitPhase u) • fullProjection j) := by
    simp only [fullPulse, fullCore, smul_add, smul_sub, sub_smul, smul_smul]
    module
  rw [he]
  calc
    _ ≤ ‖(unitPhase t - unitPhase u) • fullCore j t‖ +
        ‖unitPhase u • ((unitPhase t - unitPhase u) • fullProjection j)‖ := norm_add_le _ _
    _ = ‖unitPhase t - unitPhase u‖ +
        ‖unitPhase t - unitPhase u‖ * ‖fullProjection j‖ := by
      rw [norm_smul, norm_smul, norm_smul, phase_norm,
        CStarRing.norm_of_mem_unitary (fullCore_unitary j t)]
      ring
    _ ≤ 2 * |t - u| := by
      have h := phase_difference t u
      have hn := projection_norm j
      nlinarith [norm_nonneg (unitPhase t - unitPhase u)]

/-- Chronological products include every original global phase and every extended coordinate. -/
def fullPrefixOperator (lam : ℝ) : ℕ → Matrix Extended Extended ℂ
  | 0 => 1
  | n + 1 => fullPulse (address n) (angle lam (address n)) * fullPrefixOperator lam n

def fullInternalOperator (lam : ℝ) (k : Fin 15) (s : ℝ) : Matrix Extended Extended ℂ :=
  fullPulse (address k) (angle lam (address k) * s) * fullPrefixOperator lam k

/-- Number of perturbed calls already executed, without changing their physical schedule. -/
def changedCount : ℕ → ℕ
  | 0 => 0
  | n + 1 => changedCount n + if address n = 1 ∨ address n = 3 then 1 else 0

private theorem prefix_unitary (lam : ℝ) (n : ℕ) :
    fullPrefixOperator lam n ∈ unitary (Matrix Extended Extended ℂ) := by
  induction n with
  | zero => exact (unitary _).one_mem
  | succ n ih => exact (unitary _).mul_mem (fullPulse_unitary _ _) ih

private theorem prefix_bound (lam : ℝ) (n : ℕ) :
    ‖fullPrefixOperator lam n - fullPrefixOperator alpha n‖ ≤
      2 * (changedCount n : ℝ) * |lam - alpha| := by
  induction n with
  | zero => simp [fullPrefixOperator, changedCount]
  | succ n ih =>
    have ht : fullPrefixOperator lam (n + 1) - fullPrefixOperator alpha (n + 1) =
        fullPulse (address n) (angle lam (address n)) *
          (fullPrefixOperator lam n - fullPrefixOperator alpha n) +
        (fullPulse (address n) (angle lam (address n)) -
          fullPulse (address n) (angle alpha (address n))) * fullPrefixOperator alpha n := by
      simp only [fullPrefixOperator, mul_sub, sub_mul]
      abel
    rw [ht]
    have hn := norm_add_le
      (fullPulse (address n) (angle lam (address n)) *
        (fullPrefixOperator lam n - fullPrefixOperator alpha n))
      ((fullPulse (address n) (angle lam (address n)) -
        fullPulse (address n) (angle alpha (address n))) * fullPrefixOperator alpha n)
    rw [CStarRing.norm_mem_unitary_mul _ (fullPulse_unitary _ _),
      CStarRing.norm_mul_mem_unitary _ (prefix_unitary _ _)] at hn
    by_cases hj : address n = 1 ∨ address n = 3
    · have hd := fullPulse_difference_bound (address n) lam alpha
      simp only [angle, if_pos hj] at hn ⊢
      simp only [changedCount, if_pos hj, Nat.cast_add, Nat.cast_one]
      nlinarith
    · simp only [angle, if_neg hj, sub_self, norm_zero, add_zero] at hn ⊢
      simpa only [changedCount, if_neg hj, add_zero] using hn.trans ih

/-- All internal physical times in the original fifteen calls satisfy the full-carrier bound. -/
theorem full_operator_bound (lam : ℝ) (k : Fin 15) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖fullInternalOperator lam k s - fullInternalOperator alpha k s‖ ≤ 12 * |lam - alpha| := by
  have ht : fullInternalOperator lam k s - fullInternalOperator alpha k s =
      fullPulse (address k) (angle lam (address k) * s) *
        (fullPrefixOperator lam k - fullPrefixOperator alpha k) +
      (fullPulse (address k) (angle lam (address k) * s) -
        fullPulse (address k) (angle alpha (address k) * s)) * fullPrefixOperator alpha k := by
    simp only [fullInternalOperator, mul_sub, sub_mul]
    abel
  rw [ht]
  have hn := norm_add_le
    (fullPulse (address k) (angle lam (address k) * s) *
      (fullPrefixOperator lam k - fullPrefixOperator alpha k))
    ((fullPulse (address k) (angle lam (address k) * s) -
      fullPulse (address k) (angle alpha (address k) * s)) * fullPrefixOperator alpha k)
  rw [CStarRing.norm_mem_unitary_mul _ (fullPulse_unitary _ _),
    CStarRing.norm_mul_mem_unitary _ (prefix_unitary _ _)] at hn
  have hp := prefix_bound lam k
  have hab := abs_nonneg (lam - alpha)
  by_cases hj : address k = 1 ∨ address k = 3
  · have hd := fullPulse_difference_bound (address k) (lam * s) (alpha * s)
    rw [← sub_mul, abs_mul, abs_of_nonneg hs.1] at hd
    simp only [angle, if_pos hj] at hn ⊢
    have hc : changedCount k ≤ 5 := by fin_cases k <;> norm_num [changedCount, address] at *
    have hcr : (changedCount k : ℝ) ≤ 5 := by exact_mod_cast hc
    nlinarith [mul_le_mul_of_nonneg_left hs.2 hab]
  · simp only [angle, if_neg hj, sub_self, norm_zero, add_zero] at hn ⊢
    have hc : changedCount k ≤ 6 := by fin_cases k <;> norm_num [changedCount, address]
    have hcr : (changedCount k : ℝ) ≤ 6 := by exact_mod_cast hc
    nlinarith

end D5.S3.Quantum.Dynamics.NativeReader
