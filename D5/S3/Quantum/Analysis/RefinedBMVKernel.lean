/- GID: D5/S3/Quantum/Analysis/RefinedBMVKernel
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMVKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive semidefiniteness of the refined BMV coefficient kernels. -/

import D5.S3.Quantum.Analysis.RefinedBMVCoefficients
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

open Matrix

noncomputable section

namespace RefinedBMV

private def pad {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i ↦ Fin.cases (fun _ ↦ 0) (fun k ↦ Fin.cases 0 (D k)) i

private theorem pad_psd {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : D.PosSemidef) : (pad D).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x ↦ ?_
  · ext i j
    refine Fin.cases ?_ (fun i ↦ ?_) i <;>
      refine Fin.cases ?_ (fun j ↦ ?_) j
    · simp [pad]
    · simp [pad]
    · simp [pad]
    · exact congrFun (congrFun hD.isHermitian i) j
  · simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, pad] using
      hD.dotProduct_mulVec_nonneg (fun i ↦ x i.succ)

private theorem real_diagonal_congruence {n : Type*} [Fintype n] [DecidableEq n]
    {D : Matrix n n ℝ} (hD : D.PosSemidef) (w : n → ℝ) :
    (Matrix.of fun i j ↦ w i * D i j * w j).PosSemidef := by
  convert hD.conjTranspose_mul_mul_same (Matrix.diagonal w) using 1
  ext i j
  simp [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal]

private theorem pivot_psd {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hp : 0 < A 0 0) (hs : ∀ i, A 0 i = A i 0)
    (hD : (Matrix.of fun i j : Fin n ↦
      A i.succ j.succ - (A i.succ 0 * (A 0 0)⁻¹ * A 0 j.succ)).PosSemidef) :
    A.PosSemidef := by
  let w : Fin (n + 1) → ℝ := fun i ↦ A i 0
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j ↦
    A i.succ j.succ - (A i.succ 0 * (A 0 0)⁻¹ * A 0 j.succ)
  have he : A = (A 0 0)⁻¹ • vecMulVec w (star w) + pad D := by
    have hcancel : (A 0 0)⁻¹ * A 0 0 = 1 := inv_mul_cancel₀ hp.ne'
    ext i j
    refine Fin.cases ?_ (fun i ↦ ?_) i <;>
      refine Fin.cases ?_ (fun j ↦ ?_) j
    · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
        star_trivial, smul_eq_mul, pad, Matrix.of_apply, Fin.cases_zero, add_zero, w]
      rw [← mul_assoc, hcancel, one_mul]
    · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
        star_trivial, smul_eq_mul, pad, Matrix.of_apply, Fin.cases_zero, add_zero, w]
      rw [← mul_assoc, hcancel, one_mul, hs]
    · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
        star_trivial, smul_eq_mul, pad, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, add_zero, w]
      rw [mul_left_comm, hcancel, mul_one]
    · simp only [pad, D, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.vecMulVec_apply, Matrix.of_apply, Fin.cases_succ, Pi.star_apply, star_trivial, w, hs]
      ring
  rw [he]
  exact ((posSemidef_vecMulVec_self_star w).smul (inv_nonneg.mpr hp.le)).add (pad_psd hD)

private theorem cauchy_psd (n : ℕ) (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    (Matrix.of fun i j ↦ (x i + x j)⁻¹ : Matrix (Fin n) (Fin n) ℝ).PosSemidef := by
  induction n with
  | zero =>
    convert (PosSemidef.zero : (0 : Matrix (Fin 0) (Fin 0) ℝ).PosSemidef) using 1
    ext i
    exact Fin.elim0 i
  | succ n ih =>
    apply pivot_psd
    · change 0 < (x 0 + x 0)⁻¹
      exact inv_pos.mpr (add_pos (hx 0) (hx 0))
    · intro i
      simp [add_comm]
    · have h := real_diagonal_congruence (ih (fun i ↦ x i.succ) (fun i ↦ hx i.succ))
        (fun i ↦ (x i.succ - x 0) / (x i.succ + x 0))
      convert h using 1
      ext i j
      simpa [two_mul] using cauchy_complement (x 0) (x i.succ) (x j.succ)
        (hx 0) (hx i.succ) (hx j.succ)

private theorem weighted_cauchy_psd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x w : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hw : ∀ i, x i = 0 → w i = 0) :
    (Matrix.of fun i j ↦ w i * w j / (x i + x j) : Matrix ι ι ℝ).PosSemidef := by
  let y : ι → ℝ := fun i ↦ if x i = 0 then 1 else x i
  have hy (i : ι) : 0 < y i := by
    by_cases h : x i = 0
    · simp [y, h]
    · simpa [y, h] using lt_of_le_of_ne (hx i) (Ne.symm h)
  let e := (Fintype.equivFin ι).symm
  have hC : (Matrix.of fun i j ↦ (y i + y j)⁻¹ : Matrix ι ι ℝ).PosSemidef :=
    (posSemidef_submatrix_equiv e).mp (cauchy_psd _ (y ∘ e) (fun i ↦ hy (e i)))
  convert real_diagonal_congruence hC w using 1
  ext i j
  simp only [Matrix.of_apply]
  by_cases hi : x i = 0
  · simp [hw i hi]
  by_cases hj : x j = 0
  · simp [hw j hj]
  simp [y, hi, hj, div_eq_mul_inv, mul_right_comm]

theorem kernel_zero_psd {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (Matrix.of fun i j ↦ kernel 0 (x i) (x j) : Matrix (Fin n) (Fin n) ℝ).PosSemidef := by
  convert (weighted_cauchy_psd x x hx (fun _ h ↦ h)).smul (show (0 : ℝ) ≤ 8 by norm_num)
    using 1
  ext i j
  rw [Matrix.of_apply, kernel_zero _ _ (hx i) (hx j)]
  simp [smul_eq_mul, div_eq_mul_inv, mul_assoc]

/-- The symmetric coefficient kernel is PSD on any finite family of nonnegative inputs. -/
theorem symmetricKernel_psd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ) (hc : 0 ≤ c) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (Matrix.of fun i j ↦ symmetricKernel c (x i) (x j) : Matrix ι ι ℝ).PosSemidef := by
  have h8 : (0 : ℝ) ≤ 8 := by norm_num
  rcases hc.eq_or_lt with rfl | hc
  · convert (weighted_cauchy_psd x x hx (fun _ h ↦ h)).smul h8 using 1
    ext i j
    rw [Matrix.of_apply, symmetricKernel_zero _ _ (hx i) (hx j)]
    simp [smul_eq_mul, div_eq_mul_inv, mul_assoc]
  · let u (i : ι) := (c + 3 * x i) / (c + x i)
    let w (i : ι) := x i ^ 2 / (c + x i)
    have hw (i : ι) (hi : x i = 0) : w i = 0 := by simp [w, hi]
    have hRank := (posSemidef_vecMulVec_self_star u).smul hc.le
    have hCauchy := (weighted_cauchy_psd x w hx hw).smul h8
    convert hRank.add hCauchy using 1
    ext i j
    rw [Matrix.of_apply, symmetricKernel_pos _ _ _ hc (hx i) (hx j)]
    simp [u, w, Matrix.vecMulVec_apply, star_trivial, smul_eq_mul, div_eq_mul_inv, mul_assoc]

private theorem psd_two (a b d : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d) (hb : b ^ 2 ≤ a * d) :
    (!![a, b; b, d] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  rcases ha.eq_or_lt with he | ha
  · have ha0 : a = 0 := he.symm
    have hb0 : b = 0 := by
      rw [ha0, zero_mul] at hb
      nlinarith [sq_nonneg b]
    rw [ha0, hb0]
    convert Matrix.PosSemidef.diagonal
      (show (0 : Fin 2 → ℝ) ≤ ![0, d] by intro i; fin_cases i <;> simp [hd]) using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  · apply pivot_psd
    · simpa using ha
    · intro i
      fin_cases i <;> rfl
    · have he : 0 ≤ d - b * a⁻¹ * b := by
        rw [show b * a⁻¹ * b = b ^ 2 / a by rw [div_eq_mul_inv]; ring]
        exact sub_nonneg.mpr ((div_le_iff₀ ha).mpr (by simpa [mul_comm] using hb))
      convert Matrix.PosSemidef.diagonal
        (show (0 : Fin 1 → ℝ) ≤ fun _ ↦ d - b * a⁻¹ * b by exact fun _ ↦ he) using 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

private theorem kernel_one_ordered_psd (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) :
    (Matrix.of fun i j ↦ kernel 1 (![0, u, v] i) (![0, u, v] j) :
      Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hv : 0 ≤ v := hu.trans huv
  have hu₁ : 0 < u + 1 := by positivity
  have hv₁ : 0 < v + 1 := by positivity
  have hz : kernel 1 0 0 = 1 := by rw [kernel_one_diag]; norm_num
  apply pivot_psd
  · simpa [hz]
  · intro i
    exact kernel_symm _ _ _
  · let d : Fin 2 → ℝ := ![2 / (u + 1), 2 / (v + 1)]
    have h := real_diagonal_congruence
      (psd_two (u ^ 3) (complementEntry u v) (v ^ 3) (by positivity) (by positivity)
        (complementEntry_sq_le u v hu huv)) d
    have h0u := (kernel_symm 1 u 0).trans (kernel_one_zero u hu)
    have h0v := (kernel_symm 1 v 0).trans (kernel_one_zero v hv)
    convert h using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [d, hz, kernel_one_zero, kernel_one_diag, hu, hv, h0u, h0v, complementEntry]
    · field_simp
      ring
    · field_simp
      ring
    · rw [kernel_symm 1 v u]
      field_simp
      ring
    · field_simp
      ring

/-- With a zero input, a nonnegative center gives a PSD kernel on three inputs. -/
theorem kernel_pos_psd (z : ℝ) (hz : 0 < z) (x : Fin 3 → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hzero : ∃ i, x i = 0) :
    (Matrix.of fun i j ↦ kernel z (x i) (x j) :
      Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  let e := Tuple.sort x
  let y : Fin 3 → ℝ := fun i ↦ x (e i) / z
  have hy (i : Fin 3) : 0 ≤ y i := div_nonneg (hx _) hz.le
  have hmono : Monotone y :=
    fun _ _ hij ↦ div_le_div_of_nonneg_right (Tuple.monotone_sort x hij) hz.le
  have h0 : y 0 = 0 := by
    obtain ⟨i, hi⟩ := hzero
    apply le_antisymm _ (hy 0)
    have hm : y 0 ≤ y (e.symm i) := hmono (Fin.zero_le _)
    simpa [y, hi] using hm
  have hvec : ![0, y 1, y 2] = y := by
    funext i
    fin_cases i
    · exact h0.symm
    · rfl
    · rfl
  have h := kernel_one_ordered_psd (y 1) (y 2) (hy _) (hmono (by decide))
  rw [hvec] at h
  have hscaled := h.smul hz.le
  apply (posSemidef_submatrix_equiv e).mp
  convert hscaled using 1
  ext i j
  change kernel z (x (e i)) (x (e j)) = z * kernel 1 (y i) (y j)
  have hy' (k : Fin 3) : z * y k = x (e k) := by
    change z * (x (e k) / z) = x (e k)
    field_simp [hz.ne']
  simpa only [mul_one, hy'] using kernel_scale z 1 (y i) (y j) hz

#print axioms kernel_zero_psd
#print axioms kernel_pos_psd

end RefinedBMV
