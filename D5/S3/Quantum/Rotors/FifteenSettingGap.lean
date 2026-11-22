/- GID: D5/S3/Quantum/Rotors/FifteenSettingGap
   generality: G
   mirror-B: D5/B/S3/Quantum/Rotors/FifteenSettingGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Trace]
   utility: none
   digest: Five directions and ten midpoint settings separate four-dimensional rotor tables. -/

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A frame bound and a reverse triangle inequality give a quantitative fifteen-setting test. -/

@[expose] public section
namespace D5.S3.Quantum.Rotors.FifteenSettingGap
open Finset Matrix Real
open scoped InnerProductSpace
noncomputable section

/-- Sum one contribution for each of the ten unordered pairs of five base settings. -/
def pairSum (f : Fin 5 → Fin 5 → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then f i j else 0

private theorem gram_energy (q : Fin 5 → EuclideanSpace ℝ (Fin 4)) (hq : ∀ i, ‖q i‖ = 1) :
    5 / 8 ≤ pairSum (fun i j => ⟪q i, q j⟫_ℝ ^ 2) := by
  let A : Matrix (Fin 5) (Fin 4) ℝ := fun i k => q i k
  let G := A * A.transpose
  let C := A.transpose * A
  have g (i j : Fin 5) : G i j = ⟪q i, q j⟫_ℝ := by
    change (∑ k, (q i k) * (q j k)) = _
    simp [PiLp.inner_apply, mul_comm]
  have diag (i : Fin 5) : G i i = 1 := by rw [g, real_inner_self_eq_norm_sq, hq]; norm_num
  have symG (i j : Fin 5) : G i j = G j i := by rw [g, g, real_inner_comm]
  have symC (k l : Fin 4) : C k l = C l k := by simp [C, Matrix.mul_apply, mul_comm]
  have t : C.trace = 5 := by
    rw [show C.trace = G.trace from Matrix.trace_mul_comm _ _]
    simp [Matrix.trace, Matrix.diag, diag]
  have eqTrace : (G * G).trace = (C * C).trace := by
    calc
      _ = (A * (C * A.transpose)).trace := by simp [G, C, Matrix.mul_assoc]
      _ = ((C * A.transpose) * A).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp [C, Matrix.mul_assoc]
  have d := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin 4))) (f := fun k => C k k)
  change (∑ k, C k k) = 5 at t
  rw [t] at d
  have sub (k : Fin 4) : C k k ^ 2 ≤ ∑ l, C k l ^ 2 :=
    single_le_sum (f := fun l => C k l ^ 2) (fun l _ => sq_nonneg _) (mem_univ k)
  have ll : (∑ k, C k k ^ 2) ≤ (C * C).trace := by
    calc
      _ ≤ ∑ k, ∑ l, C k l ^ 2 := sum_le_sum fun k _ => sub k
      _ = _ := by
        apply sum_congr rfl
        intro k _
        change _ = ∑ l, C k l * C l k
        apply sum_congr rfl
        intro l _
        rw [← symC k l, sq]
  have htrace : (G * G).trace = 5 + 2 * pairSum (fun i j => ⟪q i, q j⟫_ℝ ^ 2) := by
    let f := fun i j : Fin 5 => if i < j then G i j ^ 2 else 0
    have e (i j : Fin 5) : G i j * G j i = (if i = j then 1 else 0) + f i j + f j i := by
      rcases lt_trichotomy i j with h | h | h
      · simp [f, h, ne_of_lt h, not_lt_of_gt h, ← symG i j, sq]
      · subst j; simp [f, diag]
      · simp [f, h, ne_of_gt h, not_lt_of_gt h, ← symG i j, sq]
    change (∑ i, ∑ j, G i j * G j i) = _
    simp_rw [e, sum_add_distrib]
    rw [show (∑ i, ∑ j, f j i) = ∑ i, ∑ j, f i j from sum_comm]
    simp [f, pairSum, g, two_mul, add_assoc]
  rw [← eqTrace, htrace] at ll
  norm_num at d
  linarith

private theorem pair_gap (x y z : EuclideanSpace ℝ (Fin 4))
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    4 * ⟪x, y⟫_ℝ ^ 2 ≤ (2 + √2) ^ 2 * ‖x + y - √2 • z‖ ^ 2 := by
  have hs : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have sr : 0 ≤ √2 := Real.sqrt_nonneg _
  have hn : ‖√2 • z‖ = √2 := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg sr, hz, mul_one]
  have hdiff := abs_norm_sub_norm_le (x + y) (√2 • z)
  rw [hn] at hdiff
  have ht := norm_add_le x y
  rw [hx, hy] at ht
  have hplus : ‖x + y‖ + √2 ≤ 2 + √2 := by linarith
  have hfactor : (‖x + y‖ - √2) * (‖x + y‖ + √2) = 2 * ⟪x, y⟫_ℝ := by
    nlinarith [norm_add_sq_real x y, hx, hy]
  have bound : |2 * ⟪x, y⟫_ℝ| ≤ ‖x + y - √2 • z‖ * (2 + √2) := by
    rw [← hfactor, abs_mul, abs_of_nonneg (show 0 ≤ ‖x + y‖ + √2 by positivity)]
    exact mul_le_mul hdiff hplus (by positivity) (norm_nonneg _)
  have hsq := pow_le_pow_left₀ (abs_nonneg _) bound 2
  rw [sq_abs] at hsq
  nlinarith only [hsq]

/-- The upper off-diagonal Gram energy is at least 5/8. Assigning a unit vector
to each midpoint setting incurs a strictly positive aggregate squared discrepancy. -/
theorem fifteen_setting_gap (q : Fin 5 → EuclideanSpace ℝ (Fin 4))
    (p : Fin 5 → Fin 5 → EuclideanSpace ℝ (Fin 4)) (hq : ∀ i, ‖q i‖ = 1)
    (hp : ∀ i j, i < j → ‖p i j‖ = 1) :
    5 / 8 ≤ pairSum (fun i j => ⟪q i, q j⟫_ℝ ^ 2) ∧
    5 / (4 * (1 + √2) ^ 2) ≤ pairSum (fun i j => ‖q i + q j - √2 • p i j‖ ^ 2) := by
  have g := gram_energy q hq
  refine ⟨g, ?_⟩
  have h : 4 * pairSum (fun i j => ⟪q i, q j⟫_ℝ ^ 2) ≤
      (2 + √2) ^ 2 * pairSum (fun i j => ‖q i + q j - √2 • p i j‖ ^ 2) := by
    simp only [pairSum, mul_sum, mul_ite, mul_zero]
    exact sum_le_sum fun i _ => sum_le_sum fun j _ => by
      split <;> rename_i h
      · exact pair_gap _ _ _ (hq i) (hq j) (hp i j h)
      · exact le_rfl
  apply (div_le_iff₀ (by positivity)).mpr
  have hcoeff : 4 * (1 + √2) ^ 2 = 2 * (2 + √2) ^ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hcoeff]
  linarith only [g, h]

end
end D5.S3.Quantum.Rotors.FifteenSettingGap
