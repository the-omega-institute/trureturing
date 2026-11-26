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

/-- The mean half-angle probability for two lists of rotor settings with a common weight array. -/
def comparison {n : ℕ} (w : Fin n → ℝ) (x y : Fin n → EuclideanSpace ℝ (Fin 4)) : ℝ :=
  (1 + ∑ t, w t * ⟪x t, y t⟫_ℝ) / 2

private theorem expand_loss (x y z : EuclideanSpace ℝ (Fin 4))
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    ‖x + y - √2 • z‖ ^ 2 =
    4 + 2 * ⟪x, y⟫_ℝ - 2 * √2 * (⟪x, z⟫_ℝ + ⟪y, z⟫_ℝ) := by
  rw [norm_sub_sq_real, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), hx, hy, hz, real_inner_smul_right, inner_add_left]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private theorem ten_pairs (c : ℝ) : pairSum (fun _ _ => c) = 10 * c := by
  have count : (∑ i : Fin 5, ∑ j : Fin 5, if i < j then 1 else 0 : ℕ) = 10 := by decide
  have rc : (∑ i : Fin 5, ∑ j : Fin 5, if i < j then (1 : ℝ) else 0) = 10 := by
    exact_mod_cast count
  rw [← rc]
  simp only [pairSum, sum_mul, ite_mul, one_mul, zero_mul]

/-- Any common probability error bound on the thirty indicated comparisons for a finite
fixed-weight mixture is at least the explicit positive constant on the left. -/
theorem fixed_mixture_probability_gap {n : ℕ} (w : Fin n → ℝ)
    (q : Fin 5 → Fin n → EuclideanSpace ℝ (Fin 4))
    (p : Fin 5 → Fin 5 → Fin n → EuclideanSpace ℝ (Fin 4))
    (hw : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t = 1) (hq : ∀ i t, ‖q i t‖ = 1)
    (hp : ∀ i j, i < j → ∀ t, ‖p i j t‖ = 1) (δ : ℝ)
    (errors : ∀ i j, i < j →
      |comparison w (q i) (q j) - 1 / 2| ≤ δ ∧
      |comparison w (q i) (p i j) - (1 + √2 / 2) / 2| ≤ δ ∧
      |comparison w (q j) (p i j) - (1 + √2 / 2) / 2| ≤ δ) :
    5 / (80 * (1 + √2) ^ 2 * (2 + 4 * √2)) ≤ δ := by
  let L := fun t i j => ‖q i t + q j t - √2 • p i j t‖ ^ 2
  have avgLB : 5 / (4 * (1 + √2) ^ 2) ≤ ∑ t, w t * pairSum (L t) := by
    calc
      _ = ∑ t, w t * (5 / (4 * (1 + √2) ^ 2)) := by rw [← sum_mul, hw1, one_mul]
      _ ≤ _ := sum_le_sum fun t _ => mul_le_mul_of_nonneg_left
        (fifteen_setting_gap (fun i => q i t) (fun i j => p i j t)
          (fun i => hq i t) (fun i j h => hp i j h t)).2 (hw t)
  have commute : (∑ t, w t * pairSum (L t)) = pairSum (fun i j => ∑ t, w t * L t i j) := by
    simp only [pairSum, mul_sum, mul_ite, mul_zero]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    split <;> simp_all only [sum_const_zero]
  have perPair (i j : Fin 5) (h : i < j) :
      (∑ t, w t * L t i j) ≤ (4 + 8 * √2) * δ := by
    have e : (∑ t, w t * L t i j) = 4 + 2 * (2 * comparison w (q i) (q j) - 1)
        - 2 * √2 * ((2 * comparison w (q i) (p i j) - 1) +
                     (2 * comparison w (q j) (p i j) - 1)) := by
      calc
        _ = ∑ t, (4 * w t + 2 * (w t * ⟪q i t, q j t⟫_ℝ) -
            (2 * √2) * (w t * ⟪q i t, p i j t⟫_ℝ + w t * ⟪q j t, p i j t⟫_ℝ)) := by
          apply sum_congr rfl
          intro t _
          dsimp [L]
          rw [expand_loss _ _ _ (hq i t) (hq j t) (hp i j h t)]
          ring
        _ = _ := by
          simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, hw1, comparison]
          ring
    rw [e]
    obtain ⟨hb, hl, hr⟩ := errors i j h
    have bs := (abs_le.mp hb).2
    have ls := (abs_le.mp hl).1
    have rs := (abs_le.mp hr).1
    have sl := mul_le_mul_of_nonneg_left ls (Real.sqrt_nonneg 2)
    have sr := mul_le_mul_of_nonneg_left rs (Real.sqrt_nonneg 2)
    nlinarith only [sl, sr, bs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have ub : pairSum (fun i j => ∑ t, w t * L t i j) ≤ 10 * ((4 + 8 * √2) * δ) := by
    rw [← ten_pairs]
    apply sum_le_sum
    intro i _
    apply sum_le_sum
    intro j _
    split <;> rename_i h
    · exact perPair i j h
    · rfl
  rw [commute] at avgLB
  have h := (div_le_iff₀ (by positivity)).mp (avgLB.trans ub)
  apply (div_le_iff₀ (by positivity)).mpr
  linarith only [h]

end
end D5.S3.Quantum.Rotors.FifteenSettingGap
