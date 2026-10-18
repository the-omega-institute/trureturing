/- GID: D5/S3/Zeros/CriticalPoints/RankOneComplexPowers
   generality: G
   mirror-B: D5/B/S3/Zeros/CriticalPoints/RankOneComplexPowers
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Exponential]
   utility: none
   digest: Explicit complex powers of the identity plus the all-ones matrix. -/

import D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The constant-vector projection gives explicit entire matrix powers. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Zeros.CriticalPoints.RankOneComplexPowers

open Matrix Complex
open scoped ComplexConjugate
open TangZhangOrderMinusTwo (J J_sq J_conjTranspose)

/-- Powers of a positive real base, written as an entire function of the exponent. -/
def positivePower (x : ℝ) (s : ℂ) : ℂ := exp (s * (Real.log x : ℂ))

/-- The projection onto the constant vectors. -/
private def E (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := (n : ℂ)⁻¹ • J n

/-- Explicit powers of `I + J`; only positive dimensions are used. -/
def H (n : ℕ) (s : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + (positivePower ((n : ℝ) + 1) s - 1) • E n

theorem positivePower_add (x : ℝ) (s t : ℂ) :
    positivePower x (s + t) = positivePower x s * positivePower x t := by
  simp [positivePower, add_mul, Complex.exp_add]

private theorem positivePower_zero (x : ℝ) : positivePower x 0 = 1 := by
  simp [positivePower]

theorem positivePower_one {x : ℝ} (hx : 0 < x) : positivePower x 1 = x := by
  simp [positivePower, ← Complex.ofReal_exp, Real.exp_log hx]

private theorem positivePower_star (x : ℝ) (s : ℂ) :
    conj (positivePower x s) = positivePower x (conj s) := by
  simp [positivePower, ← Complex.exp_conj]

theorem positivePower_ofReal {x : ℝ} (hx : 0 < x) (s : ℝ) :
    positivePower x (s : ℂ) = (x ^ s : ℝ) := by
  rw [positivePower, Real.rpow_def_of_pos hx]
  push_cast
  congr 1
  ring

theorem norm_positivePower (x : ℝ) (s : ℂ) :
    ‖positivePower x s‖ = Real.exp (s.re * Real.log x) := by
  simp [positivePower, Complex.norm_exp, Complex.mul_re]

private theorem E_mul (n : ℕ) (hn : 0 < n) : E n * E n = E n := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [E, Matrix.smul_mul, Matrix.mul_smul, J_sq, smul_smul, smul_smul]
  congr 1
  field_simp

private theorem E_star (n : ℕ) : (E n)ᴴ = E n := by
  simp [E, Matrix.conjTranspose_smul, J_conjTranspose]

theorem H_add (n : ℕ) (hn : 0 < n) (s t : ℂ) : H n s * H n t = H n (s + t) := by
  simp only [H, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, E_mul n hn, smul_smul]
  rw [positivePower_add]
  module

theorem H_zero (n : ℕ) : H n 0 = 1 := by simp [H, positivePower_zero]

theorem H_one (n : ℕ) (hn : 0 < n) : H n 1 = 1 + J n := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [H, positivePower_one (by positivity), E, smul_smul]
  push_cast
  simp [hn0]

private theorem H_star (n : ℕ) (s : ℂ) : (H n s)ᴴ = H n (conj s) := by
  simp [H, Matrix.conjTranspose_smul, E_star, positivePower_star]

theorem H_unitary (n : ℕ) (hn : 0 < n) (y : ℝ) :
    H n ((y : ℂ) * I) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  apply Unitary.mem_iff.mpr
  have hs : conj ((y : ℂ) * I) = -((y : ℂ) * I) := by simp
  constructor
  · change (H n ((y : ℂ) * I))ᴴ * H n ((y : ℂ) * I) = 1
    rw [H_star, hs, H_add n hn, neg_add_cancel, H_zero]
  · change H n ((y : ℂ) * I) * (H n ((y : ℂ) * I))ᴴ = 1
    rw [H_star, hs, H_add n hn, add_neg_cancel, H_zero]

theorem H_apply (n : ℕ) (s : ℂ) (i j : Fin n) :
    H n s i j = (if i = j then 1 else 0) +
      (positivePower ((n : ℝ) + 1) s - 1) / n := by
  simp [H, E, TangZhangOrderMinusTwo.J, Matrix.one_apply, div_eq_mul_inv]

private theorem H_real_apply (n : ℕ) (s : ℝ) (i j : Fin n) :
    H n (s : ℂ) i j =
      (((if i = j then 1 else 0 : ℝ) + (((n : ℝ) + 1) ^ s - 1) / n : ℝ) : ℂ) := by
  rw [H_apply, positivePower_ofReal (by positivity)]
  push_cast
  split_ifs <;> rfl

private theorem H_gram (n : ℕ) (hn : 0 < n) (p : ℝ) :
    (H n ((p / 2 : ℝ) : ℂ))ᴴ * H n ((p / 2 : ℝ) : ℂ) = H n (p : ℂ) := by
  rw [H_star]
  simp only [Complex.conj_ofReal]
  rw [H_add n hn]
  congr 1
  push_cast
  ring

/-- The columns used in the rank-one boundary estimate. -/
def column (n : ℕ) (p : ℝ) (j : Fin n) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i => H n ((p / 2 : ℝ) : ℂ) i j)

private theorem column_inner (n : ℕ) (hn : 0 < n) (p : ℝ) (i j : Fin n) :
    inner ℂ (column n p i) (column n p j) = H n (p : ℂ) i j := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, ← H_gram n hn p]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, column,
    WithLp.ofLp_toLp, Pi.star_apply, Complex.star_def]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem column_norm_sq (n : ℕ) (hn : 0 < n) (p : ℝ) (j : Fin n) :
    ‖column n p j‖ ^ 2 = (((n : ℝ) + 1) ^ p + n - 1) / n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hi := column_inner n hn p j j
  rw [inner_self_eq_norm_sq_to_K, H_real_apply] at hi
  simp only [ite_true] at hi
  rw [← RCLike.ofReal_pow] at hi
  have h : ‖column n p j‖ ^ 2 = 1 + (((n : ℝ) + 1) ^ p - 1) / n := by
    exact RCLike.ofReal_injective hi
  rw [h]
  field_simp
  ring

theorem column_inner_ne_zero (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 0 < p)
    (i j : Fin n) : inner ℂ (column n p i) (column n p j) ≠ 0 := by
  have hbase : 1 < (n : ℝ) + 1 := by exact_mod_cast (by omega : 1 < n + 1)
  have hpow : 1 < ((n : ℝ) + 1) ^ p := Real.one_lt_rpow hbase hp
  have hquot : 0 < (((n : ℝ) + 1) ^ p - 1) / n :=
    div_pos (sub_pos.mpr hpow) (Nat.cast_pos.mpr hn)
  rw [column_inner n hn p, H_real_apply]
  apply Complex.ofReal_ne_zero.mpr
  split_ifs <;> linarith

theorem sandwich_eq_sum_columns (n : ℕ) (p : ℝ) (d : Fin n → ℂ) :
    H n ((p / 2 : ℝ) : ℂ) * diagonal d * H n ((p / 2 : ℝ) : ℂ) =
      ∑ j, d j • Matrix.vecMulVec (column n p j).ofLp (star (column n p j).ofLp) := by
  have hstar : (H n ((p / 2 : ℝ) : ℂ))ᴴ = H n ((p / 2 : ℝ) : ℂ) := by
    rw [H_star, Complex.conj_ofReal]
  ext i k
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.vecMulVec_apply, column, WithLp.ofLp_toLp, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hs := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M j k) hstar
  simp only [Matrix.conjTranspose_apply] at hs
  rw [hs]
  ring

end D5.S3.Zeros.CriticalPoints.RankOneComplexPowers
