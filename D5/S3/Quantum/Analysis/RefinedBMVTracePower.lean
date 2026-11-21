/- GID: D5/S3/Quantum/Analysis/RefinedBMVTracePower
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMVTracePower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unitary triangularization and scalar Jensen give the dyadic trace-power comparison. -/

import D5.S3.Quantum.Analysis.RefinedBMVWords
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Block

open Matrix
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace RefinedBMV

variable {n : ℕ}

private theorem triangularization (M W : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ)
    (hW : IsUnit W) (hMW : M * W = W * diagonal d) :
    ∃ U : unitaryGroup (Fin n) ℂ,
      (Unitary.conjStarAlgAut ℂ _ (star U) M).IsUpperTriangular := by
  let e := EuclideanSpace.basisFun (Fin n) ℂ
  let f : Fin n → EuclideanSpace ℂ (Fin n) := fun j ↦ WithLp.toLp 2 (fun i ↦ W i j)
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) :=
    finrank_euclideanSpace
  let q := InnerProductSpace.gramSchmidtOrthonormalBasis hdim f
  let U : unitaryGroup (Fin n) ℂ :=
    ⟨e.toBasis.toMatrix q, e.toMatrix_orthonormalBasis_mem_unitary q⟩
  let R := q.toBasis.toMatrix f
  let V : Matrix (Fin n) (Fin n) ℂ := U
  let T := Vᴴ * M * V
  have hR : R.IsUpperTriangular := InnerProductSpace.gramSchmidtOrthonormalBasis_inv_isUpperTriangular hdim f
  have he : e.toBasis.toMatrix f = W := by
    ext i j
    rfl
  have hVR : V * R = W := by
    change e.toBasis.toMatrix q.toBasis * q.toBasis.toMatrix f = _
    rw [Module.Basis.toMatrix_mul_toMatrix, he]
  have hVU : Vᴴ * V = 1 := Unitary.coe_star_mul_self U
  have hRW : R = Vᴴ * W := by rw [← hVR, ← mul_assoc, hVU, one_mul]
  have hr : IsUnit R := by
    rw [hRW]
    exact (Unitary.isUnit_coe (U := star U)).mul hW
  letI := hr.invertible
  have hTR : T * R = R * diagonal d := by
    calc
      T * R = Vᴴ * (M * (V * R)) := by simp only [T, mul_assoc]
      _ = Vᴴ * (W * diagonal d) := by rw [hVR, hMW]
      _ = R * diagonal d := by rw [← mul_assoc, ← hRW]
  have ht : T = R * diagonal d * R⁻¹ := by
    rw [← hTR, mul_assoc, Matrix.mul_inv_of_invertible, mul_one]
  refine ⟨U, ?_⟩
  rw [Unitary.conjStarAlgAut_star_apply]
  change T.IsUpperTriangular
  rw [ht]
  exact (hR.mul (blockTriangular_diagonal d)).mul (blockTriangular_inv_of_blockTriangular hR)

private theorem trace_pow_triangular (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : M.IsUpperTriangular) (p : ℕ) :
    trace (M ^ p) = ∑ i, M i i ^ p := by
  have h (i : Fin n) : (M ^ p) i i = M i i ^ p := by
    induction p with
    | zero => simp
    | succ p ih =>
      rw [pow_succ, pow_succ, mul_apply, Finset.sum_eq_single i, ih]
      · intro j _ hj
        rcases lt_or_gt_of_ne hj with hji | hij
        · rw [hM.pow p hji, zero_mul]
        · rw [hM hij, mul_zero]
      · simp
  exact Finset.sum_congr rfl fun i _ ↦ h i

private theorem sq_diag_le_gram_diag (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    ‖M i i‖ ^ 2 ≤ ((Mᴴ * M) i i).re := by
  rw [mul_apply]
  simp only [conjTranspose_apply, Complex.star_def, Complex.conj_mul', Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re]
  exact Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖M j i‖) (Finset.mem_univ i)

private theorem diag_pow_le_pow_diag (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.PosSemidef) (p : ℕ) (i : Fin n) :
    (P i i).re ^ p ≤ ((P ^ p) i i).re := by
  let U := hP.isHermitian.eigenvectorUnitary
  let eigenvalue := hP.isHermitian.eigenvalues
  let w : Fin n → ℝ := fun j ↦ ‖(U : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2
  have hweights : ∑ j, w j = 1 := by
    have hU : (U : Matrix (Fin n) (Fin n) ℂ) * (U : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 :=
      Unitary.coe_mul_star_self U
    have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ ↦ (M i i).re) hU
    simpa [mul_apply, conjTranspose_apply, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, w] using hh
  have hpow (k : ℕ) : ((P ^ k) i i).re = ∑ j, w j * eigenvalue j ^ k := by
    have he : P ^ k = Unitary.conjStarAlgAut ℂ _ U (diagonal fun j ↦ (eigenvalue j : ℂ) ^ k) := by
      calc
        P ^ k = (Unitary.conjStarAlgAut ℂ _ U (diagonal fun j ↦ (eigenvalue j : ℂ))) ^ k := by
          exact congrArg (fun M : Matrix (Fin n) (Fin n) ℂ ↦ M ^ k) hP.isHermitian.spectral_theorem
        _ = _ := by rw [← map_pow, diagonal_pow]; rfl
    rw [he, Unitary.conjStarAlgAut_apply, mul_apply]
    simp only [mul_diagonal, Unitary.coe_star, star_eq_conjTranspose, conjTranspose_apply,
      Complex.star_def, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_right_comm, Complex.mul_conj']
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re, w]
  have hh := (convexOn_pow p).map_sum_le (t := Finset.univ) (w := w) (p := eigenvalue)
    (fun j _ ↦ sq_nonneg _) hweights (fun j _ ↦ hP.eigenvalues_nonneg j)
  have hone : (P i i).re = ∑ j, w j * eigenvalue j := by simpa using hpow 1
  rw [hpow, hone]
  simpa only [smul_eq_mul] using hh

private theorem trace_pow_bound_of_triangular (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : M.IsUpperTriangular) (p : ℕ) :
    (trace (M ^ (2 * p))).re ≤ (trace ((Mᴴ * M) ^ p)).re := by
  rw [trace_pow_triangular _ hM, Matrix.trace]
  simp only [Complex.re_sum, diag_apply]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  calc
    (M i i ^ (2 * p)).re ≤ ‖M i i ^ (2 * p)‖ := Complex.re_le_norm _
    _ = (‖M i i‖ ^ 2) ^ p := by rw [norm_pow, pow_mul]
    _ ≤ (((Mᴴ * M) i i).re) ^ p := pow_le_pow_left₀ (sq_nonneg _) (sq_diag_le_gram_diag M i) _
    _ ≤ (((Mᴴ * M) ^ p) i i).re := diag_pow_le_pow_diag _ (posSemidef_conjTranspose_mul_self M) p i

private theorem trace_cycle_power (A B : Matrix (Fin n) (Fin n) ℂ) (p : ℕ) :
    trace ((A * B) ^ p) = trace ((B * A) ^ p) := by
  cases p with
  | zero => simp
  | succ p =>
    calc
      trace ((A * B) ^ (p + 1)) = trace ((A * B) ^ p * A * B) := by
        rw [pow_succ, mul_assoc]
      _ = trace (A * (B * A) ^ p * B) := by rw [mul_pow_mul]
      _ = trace ((B * A) ^ (p + 1)) := by
        rw [trace_mul_comm, ← mul_assoc, ← pow_succ']

/-- The dyadic trace-power inequality via triangularization and scalar Jensen. -/
theorem trace_mul_two_pow_le (X Y : Matrix (Fin n) (Fin n) ℂ)
    (hX : X.PosDef) (hY : Y.PosDef) (p : ℕ) :
    (trace ((X * Y) ^ (2 * p))).re ≤ (trace ((X ^ 2 * Y ^ 2) ^ p)).re := by
  let S := CFC.sqrt Y
  have hS : Sᴴ = S := (CFC.sqrt_nonneg Y).posSemidef.isHermitian
  have hSS : S * S = Y := CFC.sqrt_mul_sqrt_self _ hY.posSemidef.nonneg
  have hSu : IsUnit S := (isUnit_pow_iff (by decide : 2 ≠ 0)).mp
    (by rw [pow_two, hSS]; exact hY.isUnit)
  have hdS := (Matrix.isUnit_iff_isUnit_det S).mp hSu
  let P := S * X * S
  have hP : P.IsHermitian := by
    change (S * X * S).IsHermitian
    simpa [hS] using (hX.posSemidef.conjTranspose_mul_mul_same S).isHermitian
  let V := hP.eigenvectorUnitary
  let d : Fin n → ℂ := fun i ↦ (hP.eigenvalues i : ℂ)
  let W := S⁻¹ * (V : Matrix (Fin n) (Fin n) ℂ)
  have hW : IsUnit W := (Matrix.isUnit_nonsing_inv_iff.mpr hSu).mul (Unitary.isUnit_coe (U := V))
  have hV : P * (V : Matrix (Fin n) (Fin n) ℂ) = (V : Matrix (Fin n) (Fin n) ℂ) * diagonal d := by
    conv_lhs => rw [hP.spectral_theorem, Unitary.conjStarAlgAut_apply, mul_assoc, Unitary.coe_star_mul_self, mul_one]
    rfl
  have hMW : (X * Y) * W = W * diagonal d := by
    calc
      _ = (X * S) * (V : Matrix (Fin n) (Fin n) ℂ) := by
        dsimp only [W]
        rw [← hSS, mul_assoc _ _ (S⁻¹ * _), mul_assoc S S,
          ← mul_assoc S S⁻¹, Matrix.mul_nonsing_inv S hdS, one_mul, mul_assoc]
      _ = S⁻¹ * (P * (V : Matrix (Fin n) (Fin n) ℂ)) := by
        dsimp only [P]
        rw [← mul_assoc S⁻¹, ← mul_assoc S⁻¹, ← mul_assoc S⁻¹,
          Matrix.nonsing_inv_mul S hdS, one_mul]
      _ = _ := by rw [hV, ← mul_assoc]
  obtain ⟨U, hU⟩ := triangularization (X * Y) W d hW hMW
  let f := Unitary.conjStarAlgAut ℂ _ (star U)
  have h := trace_pow_bound_of_triangular (f (X * Y)) hU p
  have hGram : (f (X * Y))ᴴ * f (X * Y) = f ((X * Y)ᴴ * (X * Y)) := by
    change star (f (X * Y)) * f (X * Y) = f (star (X * Y) * (X * Y))
    rw [map_mul f (star (X * Y)) (X * Y), map_star]
  rw [hGram, ← map_pow, ← map_pow] at h
  change (trace (Unitary.conjStarAlgAut ℂ _ (star U) ((X * Y) ^ (2 * p)))).re ≤
    (trace (Unitary.conjStarAlgAut ℂ _ (star U) (((X * Y)ᴴ * (X * Y)) ^ p))).re at h
  simp only [trace_conjugation] at h
  have he : ((X * Y)ᴴ * (X * Y)) = Y * (X ^ 2 * Y) := by
    rw [conjTranspose_mul, hX.isHermitian, hY.isHermitian, pow_two]
    simp only [mul_assoc]
  rw [he, trace_cycle_power Y (X ^ 2 * Y), mul_assoc, ← pow_two] at h
  exact h

#print axioms trace_mul_two_pow_le

end RefinedBMV
