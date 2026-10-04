/- GID: D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenReduction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CatalanPowerHankel/CiglerElevenReduction
   mirror-E: none(waiver:structural-remainder-reduction)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.DegreeLT]
   utility: none
   digest: Mixed remainder and coefficient coordinates have a triangular determinant factor. -/

import D5.S3.Combinatorics.CatalanPowerHankel.CiglerElevenMoments
import Mathlib.RingTheory.Polynomial.DegreeLT

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.CatalanPowerHankel.CiglerElevenReduction

open Polynomial Matrix

/-- Remainder coordinates modulo `X^d * v` can be replaced by remainder coordinates modulo
`v` and the first `d` coefficients; their determinant multiplier is `v.coeff 0 ^ d`.
This identity does not require the multiplier to be nonzero. -/
theorem coordinate_change (k d : ℕ) (hd : 0 < d) (v : ℚ[X])
    (hv : v.Monic) (hdeg : v.natDegree = k) (Q : Fin (k + d) → ℚ[X]) :
    det (Matrix.of fun i j : Fin (k + d) =>
      if j.val < k then (Q i %ₘ v).coeff j.val else (Q i).coeff (j.val - k)) =
    v.coeff 0 ^ d *
      det (Matrix.of fun i j : Fin (k + d) => (Q i %ₘ (X ^ d * v)).coeff j.val) := by
  classical
  let u : ℚ[X] := X ^ d * v
  have hu : u.Monic := (monic_X_pow d).mul hv
  have hdu : u.natDegree = k + d := by
    dsimp [u]
    rw [(monic_X_pow d).natDegree_mul hv, natDegree_X_pow, hdeg, Nat.add_comm]
  have hune : u ≠ 1 := by
    intro h
    have he := congrArg natDegree h
    rw [hdu, natDegree_one] at he
    omega
  let C : Fin (k + d) → ℚ[X] →ₗ[ℚ] ℚ := fun j =>
    if j.val < k then (lcoeff ℚ j.val).comp (modByMonicHom v)
    else lcoeff ℚ (j.val - k)
  let E : Matrix (Fin (k + d)) (Fin (k + d)) ℚ :=
    Matrix.of fun i j => C j (X ^ i.val)
  let R : Matrix (Fin (k + d)) (Fin (k + d)) ℚ :=
    Matrix.of fun i j => (Q i %ₘ u).coeff j.val
  have expand (w : ℚ[X]) (hw : w.natDegree < k + d) :
      w = ∑ a : Fin (k + d), w.coeff a.val • X ^ a.val := by
    rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => w.coeff a • (X : ℚ[X]) ^ a)]
    simpa only [smul_eq_C_mul] using w.as_sum_range_C_mul_X_pow' hw
  have preserves (w : ℚ[X]) (j : Fin (k + d)) : C j (w %ₘ u) = C j w := by
    dsimp [C]
    split_ifs with hj
    · change ((w %ₘ u) %ₘ v).coeff j.val = (w %ₘ v).coeff j.val
      have hdiv : v ∣ u * (w /ₘ u) := by
        refine ⟨X ^ d * (w /ₘ u), ?_⟩
        dsimp [u]
        ring
      rw [modByMonic_eq_sub_mul_div w u, sub_modByMonic,
        (modByMonic_eq_zero_iff_dvd hv).mpr hdiv, sub_zero]
    · change (w %ₘ u).coeff (j.val - k) = w.coeff (j.val - k)
      rw [modByMonic_eq_sub_mul_div, coeff_sub]
      have hr : u * (w /ₘ u) = X ^ d * (v * (w /ₘ u)) := by dsimp [u]; ring
      rw [hr, coeff_X_pow_mul', if_neg (by have := j.isLt; omega), sub_zero]
  have factor : (Matrix.of fun i j : Fin (k + d) => C j (Q i)) = R * E := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, R, E]
    rw [← preserves (Q i) j]
    conv_lhs =>
      rw [expand (Q i %ₘ u) (by rw [← hdu]; exact natDegree_modByMonic_lt _ hu hune),
        map_sum]
    simp only [map_smul, smul_eq_mul]
  let W : Fin (k + d) → ℚ[X] := fun i =>
    if i.val < k then X ^ i.val else v * X ^ (i.val - k)
  have hW (i : Fin (k + d)) : (W i).Monic ∧ (W i).natDegree = i.val := by
    dsimp [W]
    split_ifs with hi
    · exact ⟨monic_X_pow _, natDegree_X_pow _⟩
    · refine ⟨hv.mul (monic_X_pow _), ?_⟩
      rw [hv.natDegree_mul (monic_X_pow _), hdeg, natDegree_X_pow]
      omega
  let H : Matrix (Fin (k + d)) (Fin (k + d)) ℚ :=
    Matrix.of fun i j => (W i).coeff j.val
  have hHdet : H.det = 1 := by
    rw [← det_transpose]
    exact det_matrixOfPolynomials W (fun i => (hW i).2) (fun i => (hW i).1)
  have basis_factor : H * E = Matrix.of (fun i j => C j (W i)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, H, E]
    conv_rhs => rw [expand (W i) (by rw [(hW i).2]; exact i.isLt), map_sum]
    simp only [map_smul, smul_eq_mul]
  let U : Matrix (Fin d) (Fin d) ℚ := Matrix.of fun i j => (v * X ^ i.val).coeff j.val
  have hU : U.IsUpperTriangular := by
    intro i j hij
    simp only [U, Matrix.of_apply, coeff_mul_X_pow',
      if_neg (show ¬ i.val ≤ j.val by exact not_le_of_gt hij)]
  have hUdet : U.det = v.coeff 0 ^ d := by
    rw [det_of_isUpperTriangular hU]
    simp [U, coeff_mul_X_pow']
  let e : Fin k ⊕ Fin d ≃ Fin (k + d) := @finSumFinEquiv k d
  have rem_X (i : Fin k) : (X ^ i.val : ℚ[X]) %ₘ v = X ^ i.val := by
    apply (modByMonic_eq_self_iff hv).mpr
    rw [degree_X_pow, degree_eq_natDegree hv.ne_zero, hdeg]
    exact_mod_cast i.isLt
  have block : (Matrix.of (fun i j => C j (W i))).submatrix e e =
      fromBlocks (1 : Matrix (Fin k) (Fin k) ℚ)
        (Matrix.of fun i : Fin k => fun j : Fin d => (X ^ i.val : ℚ[X]).coeff j.val)
        0 U := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp [Matrix.submatrix, Matrix.fromBlocks, Matrix.of_apply, C, W, e,
          i.isLt, j.isLt, rem_X, coeff_X_pow, Matrix.one_apply, Fin.ext_iff, eq_comm]
      | inr j =>
        simp [Matrix.submatrix, Matrix.fromBlocks, Matrix.of_apply, C, W, e, i.isLt]
    | inr i =>
      cases j with
      | inl j =>
        simp [Matrix.submatrix, Matrix.fromBlocks, Matrix.of_apply, C, W, e, j.isLt,
          self_mul_modByMonic hv]
      | inr j =>
        simp [Matrix.submatrix, Matrix.fromBlocks, Matrix.of_apply, C, W, e, U]
  have hEdet : E.det = v.coeff 0 ^ d := by
    have hh := congrArg Matrix.det basis_factor
    rw [det_mul, hHdet, one_mul,
      ← det_submatrix_equiv_self e (Matrix.of fun i j => C j (W i)), block,
      det_fromBlocks_zero₂₁, det_one, one_mul, hUdet] at hh
    exact hh
  have form : (Matrix.of fun i j : Fin (k + d) =>
      if j.val < k then (Q i %ₘ v).coeff j.val else (Q i).coeff (j.val - k)) =
      Matrix.of (fun i j => C j (Q i)) := by
    ext i j
    simp only [Matrix.of_apply, C]
    split_ifs <;> rfl
  rw [form, factor, det_mul, hEdet, mul_comm]


end D5.S3.Combinatorics.CatalanPowerHankel.CiglerElevenReduction
