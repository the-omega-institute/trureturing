/- GID: D5/S3/Quantum/Foundation/HermitianExclusionBall
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/HermitianExclusionBall
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: A full orthogonal complex two-plane gives global affine coordinates on the entire original exclusion. -/

import D5.S3.Quantum.Foundation.HermitianExclusionKernel
import D5.S3.Quantum.Foundation.ExclusionBallFaces
import D5.S3.Quantum.Measurement.FourQubitParentConstruction

/-! Entire mixed exclusion faces in global affine Bloch coordinates. -/

noncomputable section
open scoped Matrix ComplexOrder InnerProductSpace RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.HermitianExclusionBall

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open SectionROGFrame HermitianExclusionKernel
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum
open D5.S3.Quantum.Measurement.FourQubitParentConstruction

private def blochHermitian (t : ℝ) (r : EuclideanSpace ℝ (Fin 3)) :
    HermitianMat (Fin 2) ℂ := ⟨blochMatrix t r, by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [blochMatrix]⟩

private def blochLinear : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] HermitianMat (Fin 2) ℂ where
  toFun := blochHermitian 0
  map_add' r s := by
    apply HermitianMat.ext
    change blochMatrix 0 (r + s) = blochMatrix 0 r + blochMatrix 0 s
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blochHermitian, blochMatrix] <;> ring
  map_smul' t r := by
    apply HermitianMat.ext
    change blochMatrix 0 (t • r) = t • blochMatrix 0 r
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blochHermitian, blochMatrix, RCLike.real_smul_eq_coe_mul] <;> ring

private def blochAffine : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] HermitianMat (Fin 2) ℂ where
  toFun := blochHermitian 1
  linear := blochLinear
  map_vadd' r s := by
    apply HermitianMat.ext
    change blochMatrix 1 (s + r) = blochMatrix 0 s + blochMatrix 1 r
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blochHermitian, blochMatrix, blochLinear] <;> ring

private theorem bloch_positive (r : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ blochHermitian 1 r ↔ ‖r‖ ≤ 1 := by
  rw [HermitianMat.zero_le_iff]
  have he : blochMatrix 1 r = (1 / 2 : ℂ) • scalarB 1 r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blochMatrix, scalarB, B_formula] <;> ring
  change (blochMatrix 1 r).PosSemidef ↔ _
  rw [he, half_scalarB_posSemidef_iff]

/-- An isometric complex two-plane equal to the whole orthogonal complement
parametrizes the entire original mixed exclusion by a global affine three-ball. -/
theorem chart_of_full_frame (v : EuclideanSpace ℂ (Fin 3)) (hv : ‖v‖ = 1)
    (W : Matrix (Fin 3) (Fin 2) ℂ)
    (hW : W.conjTranspose * W = 1)
    (hQ : W * W.conjTranspose = 1 - (rankOne v).mat) :
    ∃ a : ExclusionChart cone unit (rankOne v), a.dim = 3 := by
  let p := (rankOne v).mat
  change W * W.conjTranspose = 1 - p at hQ
  have hpH : p.conjTranspose = p := (rankOne v).H.eq
  have hnorm : star (v : Fin 3 → ℂ) ⬝ᵥ (v : Fin 3 → ℂ) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hv]
    simp
  have hpv : p *ᵥ (v : Fin 3 → ℂ) = v := by
    change Matrix.vecMulVec (v : Fin 3 → ℂ) (star (v : Fin 3 → ℂ)) *ᵥ
      (v : Fin 3 → ℂ) = v
    simp [Matrix.vecMulVec_mulVec, hnorm]
  have hWv : W.conjTranspose *ᵥ (v : Fin 3 → ℂ) = 0 := by
    have hz : (W * W.conjTranspose) *ᵥ (v : Fin 3 → ℂ) = 0 := by
      rw [hQ, Matrix.sub_mulVec, Matrix.one_mulVec, hpv, sub_self]
    have hh := congrArg (fun z => W.conjTranspose *ᵥ z) hz
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hW, Matrix.one_mul,
      Matrix.mulVec_zero] at hh
    exact hh
  have hcompress (Y : HermitianMat (Fin 2) ℂ) :
      (Y.conj W).conj W.conjTranspose = Y := by
    rw [HermitianMat.conj_conj, hW, HermitianMat.conj_one]
  have htrace (Y : HermitianMat (Fin 2) ℂ) : (Y.conj W).trace = Y.trace := by
    rw [HermitianMat.trace_eq_re_trace, HermitianMat.trace_eq_re_trace,
      HermitianMat.conj_apply_mat, Matrix.trace_mul_cycle, hW,
      Matrix.one_mul]
  have hrestore (X : HermitianMat (Fin 3) ℂ) (hXv : X.mat *ᵥ (v : Fin 3 → ℂ) = 0) :
      (X.conj W.conjTranspose).conj W = X := by
    have hXp : X.mat * p = 0 := by
      change X.mat * Matrix.vecMulVec (v : Fin 3 → ℂ) (star (v : Fin 3 → ℂ)) = 0
      rw [Matrix.mul_vecMulVec, hXv]
      simp
    have hpX : p * X.mat = 0 := by
      have h := congrArg Matrix.conjTranspose hXp
      simpa only [Matrix.conjTranspose_mul, X.H.eq, hpH,
        Matrix.conjTranspose_zero] using h
    rw [HermitianMat.conj_conj]
    apply HermitianMat.ext
    change (W * W.conjTranspose) * X.mat * (W * W.conjTranspose).conjTranspose = X.mat
    rw [hQ]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hpH,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      hpX, hXp, Matrix.zero_mul, sub_zero, zero_sub]
  let param := (HermitianMat.conjLinear ℝ W).toAffineMap.comp blochAffine
  have hparam (r) : param r = (blochHermitian 1 r).conj W := rfl
  have hinj : Function.Injective param := by
    intro r s hrs
    have h := congrArg (fun X : HermitianMat (Fin 3) ℂ => X.conj W.conjTranspose) hrs
    rw [hparam, hparam, hcompress, hcompress] at h
    have hh := congrArg (fun X : HermitianMat (Fin 2) ℂ => bloch X.mat) h
    change bloch (blochMatrix 1 r) = bloch (blochMatrix 1 s) at hh
    simpa only [bloch_blochMatrix] using hh
  refine ⟨⟨3, by norm_num, param, hinj, ?_⟩, rfl⟩
  apply Set.Subset.antisymm
  · rintro X ⟨r, hr, rfl⟩
    rw [exclusion_iff_kernel v hv, hparam]
    have hr' : ‖r‖ ≤ 1 := by simpa using hr
    refine ⟨HermitianMat.conj_nonneg W ((bloch_positive r).mpr hr'), ?_, ?_⟩
    · rw [htrace]
      rw [HermitianMat.trace_eq_re_trace]
      change (Matrix.trace (blochMatrix 1 r)).re = 1
      rw [blochMatrix_trace]
      rfl
    · change (W * blochMatrix 1 r * W.conjTranspose) *ᵥ (v : Fin 3 → ℂ) = 0
      rw [← Matrix.mulVec_mulVec, hWv, Matrix.mulVec_zero]
  · intro X hX
    obtain ⟨hXp, ht, hXv⟩ := (exclusion_iff_kernel v hv X).mp hX
    let Y := X.conj W.conjTranspose
    have hY : 0 ≤ Y := HermitianMat.conj_nonneg W.conjTranspose hXp
    have hYt : Y.trace = 1 := by
      rw [← htrace Y, hrestore X hXv, ht]
    have hYtr : Matrix.trace Y.mat = 1 := by
      rw [← HermitianMat.trace_eq_trace, hYt]
      rfl
    have hnormY : ‖bloch Y.mat‖ ≤ 1 := by
      simpa only [hYtr, Complex.one_re] using
        norm_bloch_le_trace_of_posSemidef Y.mat (HermitianMat.zero_le_iff.mp hY)
    refine ⟨bloch Y.mat, by simpa using hnormY, ?_⟩
    rw [hparam]
    have heq : blochHermitian 1 (bloch Y.mat) = Y := by
      apply HermitianMat.ext
      exact ((bloch_geometry_of_isHermitian Y.mat Y.H).1.trans
        (by rw [hYtr]; rfl)).symm
    rw [heq, hrestore X hXv]

end D5.S3.Quantum.Foundation.HermitianExclusionBall
