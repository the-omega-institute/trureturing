/- GID: D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth
   mirror-E: none
   anchors: []
   utility: none
   digest: Quantitative annealed Euclidean row growth for the four CZX transfer letters. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-! The normalized uniform average uses ordered products, including the empty word.
The growth factor is strictly between one and the second-moment bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators Matrix

namespace D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAnnealedGrowth

abbrev Row := EuclideanSpace ℝ (Fin 2)
abbrev Letter := Fin 2 × Fin 2

/-- The second coordinate selects the signs +1 and -1, respectively. -/
def letter (ρ : ℝ) (c : Letter) : Matrix (Fin 2) (Fin 2) ℝ :=
  let e : ℝ := if c.2 = 0 then 1 else -1
  if c.1 = 0 then !![1 + ρ, 2 * e * ρ; 0, 1 - ρ]
  else !![1 - ρ, 0; 2 * e * ρ, 1 + ρ]

def rowAction (v : Row) (M : Matrix (Fin 2) (Fin 2) ℝ) : Row :=
  WithLp.toLp 2 (WithLp.ofLp v ᵥ* M)

/-- Append the final letter on the right; hence indices increase from left to right. -/
def word (ρ : ℝ) : (k : ℕ) → (Fin k → Letter) → Matrix (Fin 2) (Fin 2) ℝ
  | 0, _ => 1
  | k + 1, w => word ρ k (Fin.init w) * letter ρ (w (Fin.last k))

def average (ρ : ℝ) (k : ℕ) (v : Row) : ℝ :=
  (4 : ℝ)⁻¹ ^ k * ∑ w : Fin k → Letter, ‖rowAction v (word ρ k w)‖

def growthFactor (ρ : ℝ) : ℝ :=
  Real.sqrt (1 + 3 * ρ ^ 2) - ρ ^ 2 * (1 - ρ) ^ 2 / (2 * (1 + 3 * ρ) ^ 3)

private lemma sqrt_remainder {K μ y : ℝ} (hK : 0 < K) (hμ : 0 < μ)
    (hμK : μ ≤ K ^ 2) (hy : 0 ≤ y) (hyK : y ≤ K ^ 2) :
    Real.sqrt y ≤ Real.sqrt μ + (y - μ) / (2 * Real.sqrt μ) -
      (y - μ) ^ 2 / (8 * K ^ 3) := by
  let u := Real.sqrt y
  let z := Real.sqrt μ
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hz : 0 < z := Real.sqrt_pos.2 hμ
  have hu2 : u ^ 2 = y := Real.sq_sqrt hy
  have hz2 : z ^ 2 = μ := Real.sq_sqrt hμ.le
  have huK : u ≤ K := by nlinarith
  have hzK : z ≤ K := by nlinarith
  have hbracket : 0 ≤ 4 * K ^ 3 - z * (u + z) ^ 2 := by
    have h₁ := mul_nonneg (by positivity : 0 ≤ 4 * K ^ 2) (sub_nonneg.2 hzK)
    have h₂ := mul_nonneg hz.le (mul_nonneg
      (by linarith : 0 ≤ 2 * K - u - z) (by positivity : 0 ≤ 2 * K + u + z))
    nlinarith
  have hid :
      (z + (y - μ) / (2 * z) - (y - μ) ^ 2 / (8 * K ^ 3) - u) *
        (8 * z * K ^ 3) = (u - z) ^ 2 * (4 * K ^ 3 - z * (u + z) ^ 2) := by
    rw [← hu2, ← hz2]
    field_simp
    ring
  have hden : 0 < 8 * z * K ^ 3 := by positivity
  have hmul := mul_nonneg (sq_nonneg (u - z)) hbracket
  rw [← hid] at hmul
  have := (mul_nonneg_iff_of_pos_right hden).1 hmul
  dsimp [u, z] at this
  linarith

private lemma row_sq (v : Row) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  simpa only [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq v

private lemma action_sq (ρ : ℝ) (v : Row) (c : Letter) :
    ‖rowAction v (letter ρ c)‖ ^ 2 =
      if c.1 = 0 then
        ((1 + ρ) * v 0) ^ 2 +
          (2 * (if c.2 = 0 then 1 else -1) * ρ * v 0 + (1 - ρ) * v 1) ^ 2
      else
        ((1 - ρ) * v 0 + 2 * (if c.2 = 0 then 1 else -1) * ρ * v 1) ^ 2 +
          ((1 + ρ) * v 1) ^ 2 := by
  rw [row_sq]
  rcases c with ⟨i, e⟩
  fin_cases i <;> fin_cases e <;>
    simp [rowAction, letter, Matrix.vecHead, Matrix.vecTail] <;> ring

private lemma support (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (v : Row) (c : Letter) :
    ‖rowAction v (letter ρ c)‖ ^ 2 ≤ (1 + 3 * ρ) ^ 2 * ‖v‖ ^ 2 := by
  rw [action_sq, row_sq]
  have hA : 0 ≤ 2 * ρ * (1 - ρ) := by positivity
  have hB : 0 ≤ 2 * ρ + 6 * ρ ^ 2 := by positivity
  have hC : 0 ≤ 6 * ρ + 10 * ρ ^ 2 := by positivity
  rcases c with ⟨i,e⟩
  fin_cases i <;> fin_cases e <;> norm_num <;>
    nlinarith [mul_nonneg hA (sq_nonneg (v 0 - v 1)),
      mul_nonneg hA (sq_nonneg (v 0 + v 1)),
      mul_nonneg hB (sq_nonneg (v 0)), mul_nonneg hB (sq_nonneg (v 1)),
      mul_nonneg hC (sq_nonneg (v 0)), mul_nonneg hC (sq_nonneg (v 1))]

private lemma moments (ρ : ℝ) (v : Row) :
    (∑ c : Letter, ‖rowAction v (letter ρ c)‖ ^ 2) =
      4 * (1 + 3 * ρ ^ 2) * ‖v‖ ^ 2 ∧
    (∑ c : Letter,
      (‖rowAction v (letter ρ c)‖ ^ 2 - (1 + 3 * ρ ^ 2) * ‖v‖ ^ 2) ^ 2) =
      16 * ρ ^ 2 * (1 - ρ) ^ 2 * ‖v‖ ^ 4 +
        64 * ρ ^ 3 * (v 0 ^ 2 - v 1 ^ 2) ^ 2 := by
  simp_rw [action_sq]
  rw [show ‖v‖ ^ 4 = (‖v‖ ^ 2) ^ 2 by ring, row_sq]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num
  constructor <;> ring

private lemma unit_step (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ < 1)
    (v : Row) (hv : ‖v‖ = 1) :
    (4 : ℝ)⁻¹ * ∑ c : Letter, ‖rowAction v (letter ρ c)‖ ≤ growthFactor ρ := by
  let μ := 1 + 3 * ρ ^ 2
  let K := 1 + 3 * ρ
  have hK : 0 < K := by dsimp [K]; positivity
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hμK : μ ≤ K ^ 2 := by dsimp [μ, K]; nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    sqrt_remainder hK hμ hμK (sq_nonneg ‖rowAction v (letter ρ c)‖)
      (by simpa only [hv, one_pow, mul_one] using support ρ hρ.le hρ₁.le v c))
  simp only [Real.sqrt_sq (norm_nonneg _)] at hsum
  have hm := moments ρ v
  simp only [hv, one_pow, mul_one] at hm
  have hmean : ∑ c : Letter, (‖rowAction v (letter ρ c)‖ ^ 2 - μ) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp [μ, hm.1]
    ring
  have hvar : 16 * ρ ^ 2 * (1 - ρ) ^ 2 ≤
      ∑ c : Letter, (‖rowAction v (letter ρ c)‖ ^ 2 - μ) ^ 2 := by
    rw [show μ = 1 + 3 * ρ ^ 2 from rfl, hm.2]
    have : 0 ≤ 64 * ρ ^ 3 * (v 0 ^ 2 - v 1 ^ 2) ^ 2 := by positivity
    linarith
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  simp_rw [← Finset.sum_div] at hsum
  rw [hmean] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Nat.reduceMul, nsmul_eq_mul, zero_div, add_zero] at hsum
  have hquot := div_le_div_of_nonneg_right hvar (by positivity : 0 ≤ 8 * K ^ 3)
  have hfrac : 16 * ρ ^ 2 * (1 - ρ) ^ 2 / (8 * K ^ 3) =
      4 * (ρ ^ 2 * (1 - ρ) ^ 2 / (2 * K ^ 3)) := by ring
  rw [hfrac] at hquot
  dsimp [growthFactor]
  dsimp [K, μ] at hsum hquot
  norm_num only at *
  nlinarith

private lemma factor_bounds (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ < 1) :
    0 < growthFactor ρ ∧ growthFactor ρ < Real.sqrt (1 + 3 * ρ ^ 2) ∧
      Real.sqrt (1 + 3 * ρ ^ 2) < 2 ∧ 1 < growthFactor ρ := by
  let z := Real.sqrt (1 + 3 * ρ ^ 2)
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hz2 : z ^ 2 = 1 + 3 * ρ ^ 2 := Real.sq_sqrt (by positivity)
  have hr2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hr2₁ : ρ ^ 2 < 1 := by nlinarith
  have hz₂ : z < 2 := by nlinarith
  have hz₁ : 1 + ρ ^ 2 < z := by
    nlinarith [mul_pos hr2 (sub_pos.2 hr2₁)]
  have hK : 1 ≤ (1 + 3 * ρ) ^ 3 := by
    nlinarith [sq_nonneg ρ, pow_pos hρ 3]
  have hden : 0 < 2 * (1 + 3 * ρ) ^ 3 := by positivity
  have heps : 0 < ρ ^ 2 * (1 - ρ) ^ 2 / (2 * (1 + 3 * ρ) ^ 3) := by positivity
  have heps₁ : ρ ^ 2 * (1 - ρ) ^ 2 / (2 * (1 + 3 * ρ) ^ 3) < ρ ^ 2 := by
    apply (div_lt_iff₀ hden).2
    have hs : (1 - ρ) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg hr2.le (sub_nonneg.2 hs),
      mul_nonneg hr2.le (sub_nonneg.2 hK)]
  dsimp [growthFactor]
  change 0 < z - _ ∧ z - _ < z ∧ z < 2 ∧ 1 < z - _
  exact ⟨by linarith, by linarith, hz₂, by linarith⟩

private lemma action_smul (c : ℝ) (v : Row) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    rowAction (c • v) M = c • rowAction v M := by
  change WithLp.toLp 2 ((c • WithLp.ofLp v) ᵥ* M) = _
  rw [Matrix.smul_vecMul]
  rfl

private lemma step (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ < 1) (v : Row) :
    (4 : ℝ)⁻¹ * ∑ c : Letter, ‖rowAction v (letter ρ c)‖ ≤ growthFactor ρ * ‖v‖ := by
  by_cases hv : v = 0
  · subst v
    simp [rowAction]
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  let u : Row := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    simp [u, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hn.le), hn.ne']
  have hvu : v = ‖v‖ • u := by
    simp [u, smul_smul, hn.ne']
  have h := mul_le_mul_of_nonneg_left (unit_step ρ hρ hρ₁ u hu) hn.le
  have heq (c : Letter) :
      ‖rowAction v (letter ρ c)‖ = ‖v‖ * ‖rowAction u (letter ρ c)‖ := by
    conv_lhs => rw [hvu, action_smul, norm_smul, Real.norm_of_nonneg hn.le]
  simp_rw [heq]
  rw [← Finset.mul_sum]
  nlinarith

private lemma action_mul (v : Row) (M N : Matrix (Fin 2) (Fin 2) ℝ) :
    rowAction v (M * N) = rowAction (rowAction v M) N := by
  simp only [rowAction, WithLp.ofLp_toLp, Matrix.vecMul_vecMul]

private lemma average_zero (ρ : ℝ) (v : Row) : average ρ 0 v = ‖v‖ := by
  simp [average, word, rowAction]

private lemma average_succ (ρ : ℝ) (k : ℕ) (v : Row) :
    average ρ (k + 1) v = (4 : ℝ)⁻¹ ^ k *
      ∑ p : Fin k → Letter, (4 : ℝ)⁻¹ *
        ∑ c : Letter, ‖rowAction (rowAction v (word ρ k p)) (letter ρ c)‖ := by
  have hs : (∑ w : Fin (k + 1) → Letter, ‖rowAction v (word ρ (k + 1) w)‖) =
      ∑ p : Fin k → Letter, ∑ c : Letter,
        ‖rowAction (rowAction v (word ρ k p)) (letter ρ c)‖ := by
    rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) => Letter)).sum_comp]
    change (∑ x : Letter × (Fin k → Letter),
      ‖rowAction v (word ρ (k + 1) (Fin.snoc x.2 x.1))‖) = _
    simp only [word, Fin.init_snoc, Fin.snoc_last, action_mul]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  rw [average, hs, pow_succ, ← Finset.mul_sum]
  ring

/-- Uniform four-letter Euclidean row growth, with an explicit strict root-moment gap.
The estimate includes every real row and the empty word. -/
theorem annealed_growth (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ < 1) (k : ℕ) (v : Row) :
    0 < growthFactor ρ ∧ growthFactor ρ < Real.sqrt (1 + 3 * ρ ^ 2) ∧
      Real.sqrt (1 + 3 * ρ ^ 2) < 2 ∧ 1 < growthFactor ρ ∧
      average ρ k v ≤ growthFactor ρ ^ k * ‖v‖ := by
  obtain ⟨hq, hgap, htwo, hone⟩ := factor_bounds ρ hρ hρ₁
  refine ⟨hq, hgap, htwo, hone, ?_⟩
  induction k with
  | zero => simp [average_zero]
  | succ k ih =>
    rw [average_succ]
    calc
      _ ≤ (4 : ℝ)⁻¹ ^ k * ∑ p : Fin k → Letter,
          growthFactor ρ * ‖rowAction v (word ρ k p)‖ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum fun p _ => step ρ hρ hρ₁ (rowAction v (word ρ k p))
      _ = growthFactor ρ * average ρ k v := by
        rw [← Finset.mul_sum, average]
        ring
      _ ≤ growthFactor ρ * (growthFactor ρ ^ k * ‖v‖) :=
        mul_le_mul_of_nonneg_left ih hq.le
      _ = growthFactor ρ ^ (k + 1) * ‖v‖ := by ring

end D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAnnealedGrowth
