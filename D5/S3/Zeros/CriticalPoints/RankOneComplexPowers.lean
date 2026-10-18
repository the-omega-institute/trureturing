/- GID: D5/S3/Zeros/CriticalPoints/RankOneComplexPowers
   generality: G
   mirror-B: D5/B/S3/Zeros/CriticalPoints/RankOneComplexPowers
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Exponential]
   utility: none
   digest: Schur moment interpolation, its spectral bound and strict-order rigidity. -/

import D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo
import D5.S3.Zeros.CriticalPoints.RankOneTraceBound
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring

/-! Private matrix-power and strip machinery for the spectral moment interface. -/

set_option autoImplicit false
noncomputable section

open Set Complex Matrix
open scoped BigOperators ComplexConjugate
namespace D5.S3.Zeros.CriticalPoints.RankOneComplexPowers

open Matrix Complex
open scoped ComplexConjugate
open TangZhangOrderMinusTwo (J J_sq J_conjTranspose)

/-- Powers of a positive real base, written as an entire function of the exponent. -/
private def positivePower (x : ℝ) (s : ℂ) : ℂ := exp (s * (Real.log x : ℂ))

/-- The projection onto the constant vectors. -/
private def E (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := (n : ℂ)⁻¹ • J n

/-- Explicit powers of `I + J`; only positive dimensions are used. -/
private def H (n : ℕ) (s : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + (positivePower ((n : ℝ) + 1) s - 1) • E n

private theorem positivePower_add (x : ℝ) (s t : ℂ) :
    positivePower x (s + t) = positivePower x s * positivePower x t := by
  simp [positivePower, add_mul, Complex.exp_add]

private theorem positivePower_zero (x : ℝ) : positivePower x 0 = 1 := by
  simp [positivePower]

private theorem positivePower_one {x : ℝ} (hx : 0 < x) : positivePower x 1 = x := by
  simp [positivePower, ← Complex.ofReal_exp, Real.exp_log hx]

private theorem positivePower_star (x : ℝ) (s : ℂ) :
    conj (positivePower x s) = positivePower x (conj s) := by
  simp [positivePower, ← Complex.exp_conj]

private theorem positivePower_ofReal {x : ℝ} (hx : 0 < x) (s : ℝ) :
    positivePower x (s : ℂ) = (x ^ s : ℝ) := by
  rw [positivePower, Real.rpow_def_of_pos hx]
  push_cast
  congr 1
  ring

private theorem norm_positivePower (x : ℝ) (s : ℂ) :
    ‖positivePower x s‖ = Real.exp (s.re * Real.log x) := by
  simp [positivePower, Complex.norm_exp, Complex.mul_re]

private theorem E_mul (n : ℕ) (hn : 0 < n) : E n * E n = E n := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [E, Matrix.smul_mul, Matrix.mul_smul, J_sq, smul_smul, smul_smul]
  congr 1
  field_simp

private theorem E_star (n : ℕ) : (E n)ᴴ = E n := by
  simp [E, Matrix.conjTranspose_smul, J_conjTranspose]

private theorem H_add (n : ℕ) (hn : 0 < n) (s t : ℂ) : H n s * H n t = H n (s + t) := by
  simp only [H, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, E_mul n hn, smul_smul]
  rw [positivePower_add]
  module

private theorem H_zero (n : ℕ) : H n 0 = 1 := by simp [H, positivePower_zero]

private theorem H_one (n : ℕ) (hn : 0 < n) : H n 1 = 1 + J n := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [H, positivePower_one (by positivity), E, smul_smul]
  push_cast
  simp [hn0]

private theorem H_star (n : ℕ) (s : ℂ) : (H n s)ᴴ = H n (conj s) := by
  simp [H, Matrix.conjTranspose_smul, E_star, positivePower_star]

private theorem H_unitary (n : ℕ) (hn : 0 < n) (y : ℝ) :
    H n ((y : ℂ) * I) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  apply Unitary.mem_iff.mpr
  have hs : conj ((y : ℂ) * I) = -((y : ℂ) * I) := by simp
  constructor
  · change (H n ((y : ℂ) * I))ᴴ * H n ((y : ℂ) * I) = 1
    rw [H_star, hs, H_add n hn, neg_add_cancel, H_zero]
  · change H n ((y : ℂ) * I) * (H n ((y : ℂ) * I))ᴴ = 1
    rw [H_star, hs, H_add n hn, add_neg_cancel, H_zero]

private theorem H_apply (n : ℕ) (s : ℂ) (i j : Fin n) :
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
private def column (n : ℕ) (p : ℝ) (j : Fin n) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i => H n ((p / 2 : ℝ) : ℂ) i j)

private theorem column_inner (n : ℕ) (hn : 0 < n) (p : ℝ) (i j : Fin n) :
    inner ℂ (column n p i) (column n p j) = H n (p : ℂ) i j := by
  change inner ℂ (WithLp.toLp 2 ((H n ((p / 2 : ℝ) : ℂ))ᵀ i))
    (WithLp.toLp 2 ((H n ((p / 2 : ℝ) : ℂ))ᵀ j)) = _
  rw [inner_matrix_col_col, H_gram n hn p]

private theorem column_norm_sq (n : ℕ) (hn : 0 < n) (p : ℝ) (j : Fin n) :
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

private theorem column_inner_ne_zero (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 0 < p)
    (i j : Fin n) : inner ℂ (column n p i) (column n p j) ≠ 0 := by
  have hbase : 1 < (n : ℝ) + 1 := by exact_mod_cast (by omega : 1 < n + 1)
  have hpow : 1 < ((n : ℝ) + 1) ^ p := Real.one_lt_rpow hbase hp
  have hquot : 0 < (((n : ℝ) + 1) ^ p - 1) / n :=
    div_pos (sub_pos.mpr hpow) (Nat.cast_pos.mpr hn)
  rw [column_inner n hn p, H_real_apply]
  apply Complex.ofReal_ne_zero.mpr
  split_ifs <;> linarith

private theorem sandwich_eq_sum_columns (n : ℕ) (p : ℝ) (d : Fin n → ℂ) :
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

namespace D5.S3.Zeros.CriticalPoints.ThreeLinesSchurMoment

open Complex.HadamardThreeLines

/-- Entire functions with an explicit uniform bound on the closed unit strip. -/
private structure StripData (f : ℂ → ℂ) : Prop where
  differentiable : Differentiable ℂ f
  norm_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ verticalClosedStrip 0 1, ‖f z‖ ≤ C

namespace StripData

private theorem const (c : ℂ) : StripData (fun _ : ℂ => c) :=
  ⟨differentiable_const c, ‖c‖, norm_nonneg _, fun _ _ => le_rfl⟩

private theorem add {f g : ℂ → ℂ} (hf : StripData f) (hg : StripData g) :
    StripData (fun z => f z + g z) := by
  rcases hf.norm_bound with ⟨C, hC, hfC⟩
  rcases hg.norm_bound with ⟨D, hD, hgD⟩
  exact ⟨hf.differentiable.add hg.differentiable, C + D, add_nonneg hC hD,
    fun z hz => (norm_add_le _ _).trans (add_le_add (hfC z hz) (hgD z hz))⟩

private theorem mul {f g : ℂ → ℂ} (hf : StripData f) (hg : StripData g) :
    StripData (fun z => f z * g z) := by
  rcases hf.norm_bound with ⟨C, hC, hfC⟩
  rcases hg.norm_bound with ⟨D, hD, hgD⟩
  refine ⟨hf.differentiable.mul hg.differentiable, C * D, mul_nonneg hC hD, ?_⟩
  intro z hz
  rw [norm_mul]
  exact mul_le_mul (hfC z hz) (hgD z hz) (norm_nonneg _) hC

private theorem sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, StripData (f i)) : StripData (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (0 : ℂ)
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem exp_real_slope (a : ℝ) (b : ℂ) :
    StripData (fun z : ℂ => exp (z * (a : ℂ) + b)) := by
  refine ⟨differentiable_exp.comp ((differentiable_id.mul_const _).add_const _),
    Real.exp (|a| + b.re), (Real.exp_pos _).le, ?_⟩
  intro z hz
  have hza : z.re * a ≤ |a| := by
    calc
      z.re * a ≤ |z.re * a| := le_abs_self _
      _ = z.re * |a| := by rw [abs_mul, abs_of_nonneg hz.1]
      _ ≤ 1 * |a| := mul_le_mul_of_nonneg_right hz.2 (abs_nonneg a)
      _ = |a| := one_mul _
  simp only [norm_exp, add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  exact Real.exp_le_exp.mpr (add_le_add hza le_rfl)

private theorem bddAbove {f : ℂ → ℂ} (hf : StripData f) :
    BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1) := by
  rcases hf.norm_bound with ⟨C, _, hC⟩
  refine ⟨C, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hC z hz

end StripData

end D5.S3.Zeros.CriticalPoints.ThreeLinesSchurMoment

namespace D5.S3.Zeros.CriticalPoints.SchurStripFunctions

open Matrix Complex
open scoped ComplexConjugate
open RankOneComplexPowers ThreeLinesSchurMoment

private def F (n : ℕ) (u : Fin n → ℂ) (t : Fin n → ℝ) (p : ℝ) (ζ : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  H n ((p : ℂ) * ζ / 2) * diagonal (fun j => u j * positivePower (t j) ((p : ℂ) * ζ)) *
    H n ((p : ℂ) * ζ / 2)

private def K (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ)
    (ρ : Fin n → ℝ) (p : ℝ) (ζ : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Q * diagonal (fun k => conj (v k) * positivePower (ρ k) ((p : ℂ) * (1 - ζ))) * Qᴴ

private def f (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ)
    (t ρ : Fin n → ℝ) (p : ℝ) (ζ : ℂ) : ℂ :=
  trace (K n Q v ρ p ζ * F n u t p ζ)

private theorem positive_power_strip (x a : ℝ) (b : ℂ) :
    StripData (fun ζ : ℂ => positivePower x (ζ * (a : ℂ) + b)) := by
  convert StripData.exp_real_slope (a * Real.log x) (b * (Real.log x : ℂ)) using 1
  funext ζ
  unfold positivePower
  congr 1
  push_cast
  ring

private theorem H_strip (n : ℕ) (a : ℝ) (b : ℂ) (i j : Fin n) :
    StripData (fun ζ : ℂ => H n (ζ * (a : ℂ) + b) i j) := by
  simpa only [H_apply, div_eq_mul_inv, sub_eq_add_neg] using
    (StripData.const (if i = j then (1 : ℂ) else 0)).add
      (((positive_power_strip ((n : ℝ) + 1) a b).add (StripData.const (-1))).mul
        (StripData.const ((n : ℂ)⁻¹)))

private theorem matrix_mul_strip {n : ℕ}
    {A B : ℂ → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ i j, StripData (fun ζ => A ζ i j))
    (hB : ∀ i j, StripData (fun ζ => B ζ i j)) (i j : Fin n) :
    StripData (fun ζ => (A ζ * B ζ) i j) := by
  exact StripData.sum Finset.univ (fun k ζ => A ζ i k * B ζ k j)
    (fun k _ => (hA i k).mul (hB k j))

private theorem F_strip (n : ℕ) (u : Fin n → ℂ) (t : Fin n → ℝ) (p : ℝ)
    (i j : Fin n) : StripData (fun ζ => F n u t p ζ i j) := by
  have hH : ∀ i j : Fin n, StripData (fun ζ => H n ((p : ℂ) * ζ / 2) i j) := by
    intro i j
    convert H_strip n (p / 2) 0 i j using 1
    funext ζ
    congr 2
    push_cast
    ring
  have hD : ∀ i j : Fin n, StripData (fun ζ =>
      diagonal (fun k => u k * positivePower (t k) ((p : ℂ) * ζ)) i j) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [diagonal_apply_eq]
      convert (StripData.const (u i)).mul (positive_power_strip (t i) p 0) using 1
      funext ζ
      simp only [add_zero, mul_comm]
    · simp only [diagonal_apply_ne _ hij]
      exact StripData.const 0
  exact matrix_mul_strip (fun i j => matrix_mul_strip hH hD i j) hH i j

private theorem K_strip (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ)
    (ρ : Fin n → ℝ) (p : ℝ) (i j : Fin n) :
    StripData (fun ζ => K n Q v ρ p ζ i j) := by
  have hD : ∀ i j : Fin n, StripData (fun ζ =>
      diagonal (fun k => conj (v k) * positivePower (ρ k) ((p : ℂ) * (1 - ζ))) i j) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [diagonal_apply_eq]
      convert (StripData.const (conj (v i))).mul
        (positive_power_strip (ρ i) (-p) (p : ℂ)) using 1
      funext ζ
      congr 2
      push_cast
      ring
    · simp only [diagonal_apply_ne _ hij]
      exact StripData.const 0
  exact matrix_mul_strip
    (fun i j => matrix_mul_strip (fun a b => StripData.const (Q a b)) hD i j)
    (fun a b => StripData.const (Qᴴ a b)) i j

private theorem f_strip (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ)
    (t ρ : Fin n → ℝ) (p : ℝ) : StripData (f n Q u v t ρ p) := by
  exact StripData.sum Finset.univ
    (fun i ζ => (K n Q v ρ p ζ * F n u t p ζ) i i)
    (fun i _ => matrix_mul_strip (K_strip n Q v ρ p) (F_strip n u t p) i i)

private theorem diagonal_unitary (n : ℕ) (d : Fin n → ℂ) (hd : ∀ i, ‖d i‖ = 1) :
    diagonal d ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  apply Matrix.diagonal_mem_unitary.mpr
  rw [Pi.mem_unitary_iff]
  intro i
  apply Unitary.mem_iff.mpr
  simp [Complex.star_def, Complex.mul_conj', Complex.conj_mul', hd]

private theorem F_unitary_left (n : ℕ) (hn : 0 < n) (u : Fin n → ℂ)
    (hu : ∀ i, ‖u i‖ = 1) (t : Fin n → ℝ) (p y : ℝ) :
    F n u t p ((y : ℂ) * I) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hH : H n ((p : ℂ) * ((y : ℂ) * I) / 2) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    have he : (p : ℂ) * ((y : ℂ) * I) / 2 = ((p * y / 2 : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [he]
    exact H_unitary n hn _
  have hD := diagonal_unitary n
    (fun i => u i * positivePower (t i) ((p : ℂ) * ((y : ℂ) * I))) (by
      intro i
      rw [norm_mul, hu, one_mul, norm_positivePower]
      simp [Complex.mul_re])
  exact (Matrix.unitaryGroup (Fin n) ℂ).mul_mem
    ((Matrix.unitaryGroup (Fin n) ℂ).mul_mem hH hD) hH

private theorem K_unitary_right (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (v : Fin n → ℂ)
    (hv : ∀ i, ‖v i‖ = 1) (ρ : Fin n → ℝ) (p y : ℝ) :
    K n Q v ρ p (1 + (y : ℂ) * I) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hD := diagonal_unitary n
    (fun i => conj (v i) * positivePower (ρ i) ((p : ℂ) * (1 - (1 + (y : ℂ) * I)))) (by
      intro i
      rw [norm_mul, Complex.norm_conj, hv, one_mul, norm_positivePower]
      simp [Complex.mul_re])
  have hQs : Qᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.star_mem hQ
  exact (Matrix.unitaryGroup (Fin n) ℂ).mul_mem
    ((Matrix.unitaryGroup (Fin n) ℂ).mul_mem hQ hD) hQs

private theorem unitary_diag_norm_le_one (n : ℕ) (V : Matrix (Fin n) (Fin n) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) (i : Fin n) : ‖V i i‖ ≤ 1 := by
  exact entry_norm_bound_of_unitary hV i i

private theorem left_bound (n : ℕ) (hn : 0 < n) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (u v : Fin n → ℂ)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1)
    (t ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i) (p : ℝ)
    (hmass : ∑ i, ρ i ^ p = 1) (y : ℝ) :
    ‖f n Q u v t ρ p ((y : ℂ) * I)‖ ≤ 1 := by
  let V := Qᴴ * F n u t p ((y : ℂ) * I) * Q
  let d : Fin n → ℂ := fun i =>
    conj (v i) * positivePower (ρ i) ((p : ℂ) * (1 - (y : ℂ) * I))
  have hQs : Qᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.star_mem hQ
  have hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    (Matrix.unitaryGroup (Fin n) ℂ).mul_mem
      ((Matrix.unitaryGroup (Fin n) ℂ).mul_mem hQs (F_unitary_left n hn u hu t p y)) hQ
  have hd (i : Fin n) : ‖d i‖ = ρ i ^ p := by
    dsimp only [d]
    rw [norm_mul, Complex.norm_conj, hv, one_mul, norm_positivePower,
      Real.rpow_def_of_pos (hρ i)]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      Complex.sub_re, Complex.one_re, sub_zero, Complex.I_re,
      Complex.I_im, mul_one]
    congr 1
    ring
  have htrace : f n Q u v t ρ p ((y : ℂ) * I) = trace (diagonal d * V) := by
    unfold f K
    change trace ((Q * diagonal d * Qᴴ) * F n u t p ((y : ℂ) * I)) = _
    rw [show (Q * diagonal d * Qᴴ) * F n u t p ((y : ℂ) * I) =
      Q * (diagonal d * (Qᴴ * F n u t p ((y : ℂ) * I))) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [V, Matrix.mul_assoc]
  rw [htrace, Matrix.trace]
  calc
    ‖∑ i, (diagonal d * V) i i‖ ≤ ∑ i, ‖(diagonal d * V) i i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ρ i ^ p := by
      apply Finset.sum_le_sum
      intro i _
      simp only [Matrix.diagonal_mul, norm_mul, hd]
      exact (mul_le_mul_of_nonneg_left (unitary_diag_norm_le_one n V hV i)
        (Real.rpow_nonneg (hρ i).le p)).trans_eq (mul_one _)
    _ = 1 := hmass

end D5.S3.Zeros.CriticalPoints.SchurStripFunctions

namespace D5.S3.Zeros.CriticalPoints.SchurStripBoundary

open RankOneComplexPowers RankOneTraceBound

private theorem boundary_factorization (n : ℕ) (hn : 0 < n)
    (u : Fin n → ℂ) (t : Fin n → ℝ) (ht : ∀ j, 0 < t j) (p y : ℝ) :
    H n ((p : ℂ) * (1 + (y : ℂ) * I) / 2) *
        diagonal (fun j => u j * positivePower (t j) ((p : ℂ) * (1 + (y : ℂ) * I))) *
        H n ((p : ℂ) * (1 + (y : ℂ) * I) / 2) =
      H n (((p * y / 2 : ℝ) : ℂ) * I) *
        (H n ((p / 2 : ℝ) : ℂ) *
          diagonal (fun j => ((t j ^ p : ℝ) : ℂ) *
            (u j * positivePower (t j) (((p * y : ℝ) : ℂ) * I))) *
          H n ((p / 2 : ℝ) : ℂ)) *
        H n (((p * y / 2 : ℝ) : ℂ) * I) := by
  have hleft : H n ((p : ℂ) * (1 + (y : ℂ) * I) / 2) =
      H n (((p * y / 2 : ℝ) : ℂ) * I) * H n ((p / 2 : ℝ) : ℂ) := by
    rw [H_add n hn]
    congr 1
    push_cast
    ring
  have hright : H n ((p : ℂ) * (1 + (y : ℂ) * I) / 2) =
      H n ((p / 2 : ℝ) : ℂ) * H n (((p * y / 2 : ℝ) : ℂ) * I) := by
    rw [H_add n hn]
    congr 1
    push_cast
    ring
  have hd : (fun j => u j * positivePower (t j) ((p : ℂ) * (1 + (y : ℂ) * I))) =
      fun j => ((t j ^ p : ℝ) : ℂ) *
        (u j * positivePower (t j) (((p * y : ℝ) : ℂ) * I)) := by
    funext j
    have he : (p : ℂ) * (1 + (y : ℂ) * I) =
        (p : ℂ) + (((p * y : ℝ) : ℂ) * I) := by push_cast; ring
    rw [he, positivePower_add, positivePower_ofReal (ht j)]
    ring
  conv_lhs => lhs; lhs; rw [hleft]
  conv_lhs => rhs; rw [hright]
  rw [hd]
  simp only [Matrix.mul_assoc]

/-- A unitary trace functional has the sharp right boundary bound, with common phases at equality.
The matrix expression is the value at `1 + y I` of the Schur strip interpolation family. -/
private theorem right_boundary_bound_and_phases (n : ℕ) (hn : 0 < n)
    (u : Fin n → ℂ) (hu : ∀ j, ‖u j‖ = 1)
    (t : Fin n → ℝ) (ht : ∀ j, 0 < t j) (p : ℝ) (hp : 0 < p)
    (y : ℝ) (K : Matrix (Fin n) (Fin n) ℂ)
    (hK : K ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    let A := H n ((p : ℂ) * (1 + (y : ℂ) * I) / 2) *
      diagonal (fun j => u j * positivePower (t j) ((p : ℂ) * (1 + (y : ℂ) * I))) *
      H n ((p : ℂ) * (1 + (y : ℂ) * I) / 2)
    let M := ((((n : ℝ) + 1) ^ p + n - 1) / n) * ∑ j, t j ^ p
    ‖Matrix.trace (K * A)‖ ≤ M ∧
      (‖Matrix.trace (K * A)‖ = M →
        ∀ i j, u i * positivePower (t i) (((p * y : ℝ) : ℂ) * I) =
          u j * positivePower (t j) (((p * y : ℝ) : ℂ) * I)) := by
  dsimp only
  let L := H n (((p * y / 2 : ℝ) : ℂ) * I)
  let V := L * K * L
  let a : Fin n → ℝ := fun j => t j ^ p
  let γ : Fin n → ℂ := fun j =>
    u j * positivePower (t j) (((p * y : ℝ) : ℂ) * I)
  let B := H n ((p / 2 : ℝ) : ℂ) *
    diagonal (fun j => (a j : ℂ) * γ j) * H n ((p / 2 : ℝ) : ℂ)
  have hL : L ∈ Matrix.unitaryGroup (Fin n) ℂ := H_unitary n hn _
  have hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    (Matrix.unitaryGroup (Fin n) ℂ).mul_mem
      ((Matrix.unitaryGroup (Fin n) ℂ).mul_mem hL hK) hL
  have ha : ∀ j, 0 < a j := fun j => Real.rpow_pos_of_pos (ht j) p
  have hγ : ∀ j, ‖γ j‖ = 1 := by
    intro j
    dsimp [γ]
    rw [norm_mul, hu j, one_mul, norm_positivePower]
    simp
  have htrace :
      Matrix.trace (K * (H n ((p : ℂ) * (1 + (y : ℂ) * I) / 2) *
        diagonal (fun j => u j * positivePower (t j) ((p : ℂ) * (1 + (y : ℂ) * I))) *
        H n ((p : ℂ) * (1 + (y : ℂ) * I) / 2))) =
      Matrix.trace (V * ∑ j, ((a j : ℂ) * γ j) •
        Matrix.vecMulVec (column n p j).ofLp (star (column n p j).ofLp)) := by
    rw [boundary_factorization n hn u t ht p y]
    change Matrix.trace (K * (L * B * L)) = _
    rw [show K * (L * B * L) = (K * L) * B * L by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_cycle]
    change Matrix.trace ((L * (K * L)) * B) = _
    rw [show L * (K * L) = V by simp only [V, Matrix.mul_assoc]]
    dsimp only [B]
    rw [sandwich_eq_sum_columns]
  have hmass : ∑ j, a j * ‖column n p j‖ ^ 2 =
      ((((n : ℝ) + 1) ^ p + n - 1) / n) * ∑ j, t j ^ p := by
    simp only [column_norm_sq n hn p]
    rw [← Finset.sum_mul, mul_comm]
  rw [htrace]
  constructor
  · exact (norm_trace_rank_one_sum_le (column n p) a γ (fun j => (ha j).le) hγ V hV).trans_eq
      hmass
  · intro heq
    exact phases_eq_of_norm_trace_rank_one_sum_eq (column n p) a γ ha hγ V hV
      (column_inner_ne_zero n hn p hp) (heq.trans hmass.symm)

end D5.S3.Zeros.CriticalPoints.SchurStripBoundary

namespace D5.S3.Zeros.CriticalPoints.SchurStripCenter

open Matrix Complex
open scoped ComplexConjugate
open RankOneComplexPowers SchurStripFunctions

/-- The trace at `1 / p` is the weighted diagonal sum in the same matrix basis. -/
private theorem center_identity (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (u v b μ : Fin n → ℂ) (t ρ : Fin n → ℝ) (p N : ℝ)
    (hp : 0 < p) (ht : ∀ j, 0 < t j) (hρ : ∀ k, 0 < ρ k)
    (hb : ∀ j, b j = u j * (t j : ℂ))
    (hμ : ∀ k, μ k =
      (Qᴴ * (H n (1 / 2) * diagonal b * H n (1 / 2)) * Q) k k)
    (hsum : (∑ k, (conj (v k) * ((ρ k ^ (p - 1) : ℝ) : ℂ)) * μ k) = (N : ℂ)) :
    f n Q u v t ρ p ((1 / p : ℝ) : ℂ) = (N : ℂ) := by
  have hp0 : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hp)
  have hcenter : (p : ℂ) * ((1 / p : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp [hp0]
  have hexp : (p : ℂ) * (1 - ((1 / p : ℝ) : ℂ)) = ((p - 1 : ℝ) : ℂ) := by
    push_cast
    field_simp [hp0] <;> ring
  let A : Matrix (Fin n) (Fin n) ℂ := H n (1 / 2) * diagonal b * H n (1 / 2)
  let d : Fin n → ℂ := fun k => conj (v k) * ((ρ k ^ (p - 1) : ℝ) : ℂ)
  have hF : F n u t p ((1 / p : ℝ) : ℂ) = A := by
    have hD : diagonal (fun j => u j * positivePower (t j) 1) = diagonal b := by
      congr 1
      funext j
      rw [positivePower_one (ht j), ← hb j]
    unfold F
    rw [hcenter, hD]
  have hK : K n Q v ρ p ((1 / p : ℝ) : ℂ) = Q * diagonal d * Qᴴ := by
    have hD : diagonal (fun k => conj (v k) * positivePower (ρ k) ((p - 1 : ℝ) : ℂ)) =
        diagonal d := by
      congr 1
      funext k
      exact congrArg (fun z : ℂ => conj (v k) * z) (positivePower_ofReal (hρ k) (p - 1))
    simp only [K, hexp, hD]
  unfold f
  rw [hF, hK, Matrix.mul_assoc (Q * diagonal d) Qᴴ A,
    trace_mul_cycle, trace_mul_comm _ (diagonal d)]
  change (∑ k, (diagonal d * (Qᴴ * A * Q)) k k) = (N : ℂ)
  simp only [Matrix.diagonal_mul]
  dsimp only [A, d]
  simpa only [← hμ] using hsum

end D5.S3.Zeros.CriticalPoints.SchurStripCenter

namespace D5.S3.Zeros.CriticalPoints.SchurMomentNormalization

open Matrix Complex
open scoped ComplexConjugate
open RankOneComplexPowers

private theorem normalized_weights {n : ℕ} (hn : 0 < n) (μ : Fin n → ℂ)
    (hμ : ∀ k, μ k ≠ 0) (p : ℝ) (hp : 0 < p) :
    ∃ (N : ℝ) (ρ : Fin n → ℝ) (v : Fin n → ℂ),
      0 < N ∧ (∀ k, 0 < ρ k) ∧ (∀ k, ‖v k‖ = 1) ∧
      (∀ k, μ k = v k * ((N * ρ k : ℝ) : ℂ)) ∧
      (∑ k, ρ k ^ p) = 1 ∧ N ^ p = ∑ k, ‖μ k‖ ^ p ∧
      (∑ k, (conj (v k) * (ρ k ^ (p - 1) : ℝ)) * μ k) = (N : ℂ) := by
  let S : ℝ := ∑ k, ‖μ k‖ ^ p
  have ht (k) : 0 < ‖μ k‖ := norm_pos_iff.mpr (hμ k)
  have hS : 0 < S := Finset.sum_pos (fun k _ => Real.rpow_pos_of_pos (ht k) _)
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
  let N : ℝ := S ^ p⁻¹
  have hN : 0 < N := Real.rpow_pos_of_pos hS _
  have hNp : N ^ p = S := Real.rpow_inv_rpow hS.le hp.ne'
  let ρ : Fin n → ℝ := fun k => ‖μ k‖ / N
  let v : Fin n → ℂ := fun k => μ k / (‖μ k‖ : ℂ)
  have hρ (k) : 0 < ρ k := div_pos (ht k) hN
  have hv (k) : ‖v k‖ = 1 := by
    simp [v, norm_div, Complex.norm_real, Real.norm_of_nonneg (ht k).le, (ht k).ne']
  have hdecomp (k) : μ k = v k * ((N * ρ k : ℝ) : ℂ) := by
    dsimp [v, ρ]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hN.ne', Complex.ofReal_ne_zero.mpr (ht k).ne']
  have hsum : (∑ k, ρ k ^ p) = 1 := by
    simp only [ρ, Real.div_rpow (norm_nonneg _) hN.le, ← Finset.sum_div, hNp]
    exact div_self hS.ne'
  refine ⟨N, ρ, v, hN, hρ, hv, hdecomp, hsum, hNp, ?_⟩
  calc
    _ = ∑ k, ((N * ρ k ^ p : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hdecomp]
      have hc : conj (v k) * v k = 1 := by
        simpa [hv] using Complex.conj_mul' (v k)
      have hr : ρ k ^ (p - 1) * ρ k = ρ k ^ p := by
        rw [← Real.rpow_add_one (hρ k).ne']
        congr 1
        ring
      calc
        _ = (conj (v k) * v k) * (N : ℂ) * ((ρ k ^ (p - 1) * ρ k : ℝ) : ℂ) := by
          push_cast
          ring
        _ = ((N * ρ k ^ p : ℝ) : ℂ) := by rw [hc, one_mul, hr]; push_cast; rfl
    _ = (N : ℂ) := by rw [← Complex.ofReal_sum, ← Finset.mul_sum, hsum, mul_one]

private theorem schur_roots_moment {n : ℕ} (A Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (ht : (Qᴴ * A * Q).IsUpperTriangular) (p : ℝ) :
    (A.charpoly.roots.map (fun w => ‖w‖ ^ p)).sum =
      ∑ k, ‖(Qᴴ * A * Q) k k‖ ^ p := by
  let u : Matrix.unitaryGroup (Fin n) ℂ := ⟨Q, hQ⟩
  have hQQ := (Unitary.mem_iff.mp hQ).1
  have he : (Qᴴ * A * Q).charpoly = A.charpoly := by
    have h := Matrix.charpoly_units_conj' (Unitary.toUnits u) A
    change (Q⁻¹ * A * Q).charpoly = A.charpoly at h
    rwa [Matrix.inv_eq_left_inv hQQ] at h
  rw [← he, Matrix.charpoly_of_isUpperTriangular _ ht,
    Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.mpr
      fun k _ => Polynomial.X_sub_C_ne_zero _)]
  simp [List.sum_ofFn]

theorem reciprocal_moment {n : ℕ} (z : Fin n → ℂ) (hz : ∀ j, z j ≠ 0) (p : ℝ) :
    ((Polynomial.derivative (TangZhangOrderMinusTwo.P z)).roots.map
      (fun w => ‖w‖ ^ (-p))).sum =
    ((TangZhangOrderMinusTwo.B (fun j => (z j)⁻¹)).charpoly.roots.map
      (fun μ => ‖μ‖ ^ p)).sum := by
  rw [← TangZhangOrderMinusTwo.roots_derivative z hz, Multiset.map_map]
  simp only [Function.comp_apply, norm_inv, ← Real.rpow_neg_eq_inv_rpow]

private def A {n : ℕ} (b : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  H n ((1 / 2 : ℝ) : ℂ) * diagonal b * H n ((1 / 2 : ℝ) : ℂ)

private theorem A_charpoly {n : ℕ} (hn : 0 < n) (b : Fin n → ℂ) :
    (A b).charpoly = (TangZhangOrderMinusTwo.B b).charpoly := by
  have hH : H n ((1 / 2 : ℝ) : ℂ) * H n ((1 / 2 : ℝ) : ℂ) = 1 + TangZhangOrderMinusTwo.J n := by
    rw [H_add n hn, show ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) = 1 by norm_num,
      H_one n hn]
  unfold A TangZhangOrderMinusTwo.B
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hH, Matrix.charpoly_mul_comm]

private theorem schur_diagonal_ne_zero {n : ℕ} (hn : 0 < n) (b : Fin n → ℂ)
    (hb : ∀ j, b j ≠ 0) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (ht : (Qᴴ * A b * Q).IsUpperTriangular) :
    ∀ k, (Qᴴ * A b * Q) k k ≠ 0 := by
  have hH : (H n ((1 / 2 : ℝ) : ℂ)).det ≠ 0 := by
    apply Matrix.det_ne_zero_of_right_inverse
      (B := H n (-((1 / 2 : ℝ) : ℂ)))
    rw [H_add n hn, add_neg_cancel, H_zero]
  have hD : (diagonal b).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hb j)
  have hA : (A b).det ≠ 0 := by simp only [A, Matrix.det_mul]; exact mul_ne_zero (mul_ne_zero hH hD) hH
  have hQQ := Unitary.mem_iff.mp hQ
  have hQ0 : Q.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hQQ.1
  have hQs0 : Qᴴ.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hQQ.2
  exact ht.det_ne_zero_iff.mp (by
    simp only [Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero hQs0 hA) hQ0)

end D5.S3.Zeros.CriticalPoints.SchurMomentNormalization

namespace D5.S3.Zeros.CriticalPoints.SchurMomentInequality

open Matrix Complex
open scoped ComplexConjugate
open RankOneComplexPowers SchurMomentNormalization SchurStripFunctions
open ThreeLinesSchurMoment SchurStripBoundary SchurStripCenter
theorem spectral_bound_and_rigidity {n : ℕ} (hn : 0 < n) (b : Fin n → ℂ)
    (hb : ∀ j, b j ≠ 0) (p : ℝ) (hp : 1 ≤ p) :
    let S := ((TangZhangOrderMinusTwo.B b).charpoly.roots.map (fun μ => ‖μ‖ ^ p)).sum
    let M := ((((n : ℝ) + 1) ^ p + n - 1) / n) * ∑ j, ‖b j‖ ^ p
    S ≤ M ∧ (1 < p → S = M → ∀ i j, b i = b j) := by
  dsimp only
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let t : Fin n → ℝ := fun j => ‖b j‖
  let u : Fin n → ℂ := fun j => b j / (t j : ℂ)
  have ht (j) : 0 < t j := norm_pos_iff.mpr (hb j)
  have hu (j) : ‖u j‖ = 1 := by
    simp [u, norm_div, Complex.norm_real, Real.norm_of_nonneg (ht j).le,
      div_self (ht j).ne', t]
  have hbu (j) : b j = u j * (t j : ℂ) := by
    exact (div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (ht j).ne')).symm
  obtain ⟨Q, hQ, hQ', htri⟩ := SchurFrobeniusInequality.triangularize n (A b)
  have hQu : Q ∈ Matrix.unitaryGroup (Fin n) ℂ := Unitary.mem_iff.mpr ⟨hQ, hQ'⟩
  let μ : Fin n → ℂ := fun k => (Qᴴ * A b * Q) k k
  have hμ : ∀ k, μ k ≠ 0 := schur_diagonal_ne_zero hn b hb Q hQu htri
  obtain ⟨N, ρ, v, hN, hρ, hv, hdecomp, hmass, hNp, hsum⟩ :=
    normalized_weights hn μ hμ p hp0
  let S : ℝ := ∑ k, ‖μ k‖ ^ p
  change N ^ p = S at hNp
  let M : ℝ := ((((n : ℝ) + 1) ^ p + n - 1) / n) * ∑ j, t j ^ p
  have hM : 0 < M := by
    have hbase : 1 < (n : ℝ) + 1 := by exact_mod_cast (by omega : 1 < n + 1)
    have hpow := Real.one_lt_rpow hbase hp0
    have hcoeff : 0 < (((n : ℝ) + 1) ^ p + n - 1) / n :=
      div_pos (by have : (0 : ℝ) < n := Nat.cast_pos.mpr hn; linarith)
        (Nat.cast_pos.mpr hn)
    exact mul_pos hcoeff (Finset.sum_pos (fun j _ => Real.rpow_pos_of_pos (ht j) _)
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩))
  let g : ℂ → ℂ := f n Q u v t ρ p
  have hgcenter : g ((1 / p : ℝ) : ℂ) = (N : ℂ) := by
    apply center_identity n Q u v b μ t ρ p N hp0 ht hρ hbu
    · intro k
      simp only [μ, A, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    · exact hsum
  have hnormcenter : ‖g ((1 / p : ℝ) : ℂ)‖ = N := by
    rw [hgcenter, Complex.norm_real, Real.norm_of_nonneg hN.le]
  have hright (y : ℝ) : ‖g (1 + (y : ℂ) * I)‖ ≤ M ∧
      (‖g (1 + (y : ℂ) * I)‖ = M →
        ∀ i j, u i * positivePower (t i) (((p * y : ℝ) : ℂ) * I) =
          u j * positivePower (t j) (((p * y : ℝ) : ℂ) * I)) := by
    have h := right_boundary_bound_and_phases n hn u hu t ht p hp0 y
      (K n Q v ρ p (1 + (y : ℂ) * I)) (K_unitary_right n Q hQu v hv ρ p y)
    exact h
  have hstrip := f_strip n Q u v t ρ p
  have hinterp := strip_moment_bound_and_equality hM hstrip.differentiable.diffContOnCl
    hstrip.bddAbove (fun ζ hζ => by
      have he : ζ = (ζ.im : ℂ) * I := by apply Complex.ext <;> simp [hζ]
      rw [he]
      exact left_bound n hn Q hQu u v hu hv t ρ hρ p hmass ζ.im)
    (fun ζ hζ => by
      have he : ζ = 1 + (ζ.im : ℂ) * I := by apply Complex.ext <;> simp [hζ]
      rw [he]
      exact (hright ζ.im).1)
  have hθ0 : 0 < 1 / p := one_div_pos.mpr hp0
  have hθ1 : 1 / p ≤ 1 := (div_le_one hp0).mpr hp
  have hle : N ≤ M ^ (1 / p) := by
    have h := hinterp.1 ((1 / p : ℝ) : ℂ) ⟨hθ0.le, hθ1⟩
    change ‖g ((1 / p : ℝ) : ℂ)‖ ≤ M ^ (1 / p) at h
    rwa [hnormcenter] at h
  have hbound : S ≤ M := by
    have h := Real.rpow_le_rpow hN.le hle hp0.le
    rw [← Real.rpow_mul hM.le, one_div_mul_cancel hp0.ne', Real.rpow_one] at h
    exact hNp.symm.trans_le h
  have hspectral : ((TangZhangOrderMinusTwo.B b).charpoly.roots.map
      (fun μ => ‖μ‖ ^ p)).sum = S := by
    rw [← A_charpoly hn b]
    exact schur_roots_moment (A b) Q hQu htri p
  rw [hspectral]
  refine ⟨hbound, ?_⟩
  intro hp1 heq
  change S = M at heq
  have heqcenter : ‖g ((1 / p : ℝ) : ℂ)‖ = M ^ (1 / p) := by
    rw [hnormcenter, ← heq, ← hNp, ← Real.rpow_mul hN.le,
      mul_one_div_cancel hp0.ne', Real.rpow_one]
  have hall : ∀ y : ℝ, ∀ i j,
      u i * positivePower (t i) (((p * y : ℝ) : ℂ) * I) =
        u j * positivePower (t j) (((p * y : ℝ) : ℂ) * I) := by
    intro y
    exact (hright y).2 (hinterp.2 (1 / p) hθ0 ((div_lt_one hp0).mpr hp1) heqcenter y)
  intro i j
  have hu0 : u i ≠ 0 := by
    intro h
    have hi := hu i
    simp only [h, norm_zero, zero_ne_one] at hi
  have hfreq : ∀ y : ℝ,
      u i * exp ((y : ℂ) * ((p * Real.log (t i) : ℝ) : ℂ) * I) =
        u j * exp ((y : ℂ) * ((p * Real.log (t j) : ℝ) : ℂ) * I) := by
    intro y
    convert hall y i j using 1 <;> unfold positivePower <;> congr 2 <;> push_cast <;> ring
  obtain ⟨huij, hlog⟩ := rotating_phase_injective hu0 hfreq
  have htij : t i = t j := Real.log_injOn_pos (ht i) (ht j) (mul_left_cancel₀ hp0.ne' hlog)
  rw [hbu i, hbu j, huij, htij]

end D5.S3.Zeros.CriticalPoints.SchurMomentInequality
