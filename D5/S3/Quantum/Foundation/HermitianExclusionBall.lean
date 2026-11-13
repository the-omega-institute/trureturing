/- GID: D5/S3/Quantum/Foundation/HermitianExclusionBall
   generality: I
   mirror-B: D5/B/S3/Quantum/Foundation/HermitianExclusionBall
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Whole complex two-planes give global affine charts of all original exclusions. -/

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
    fin_cases i <;> fin_cases j <;> simp [blochMatrix] <;> ring
  map_smul' t r := by
    apply HermitianMat.ext
    change blochMatrix 0 (t • r) = t • blochMatrix 0 r
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blochMatrix, RCLike.real_smul_eq_coe_mul] <;> ring

private def blochAffine : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] HermitianMat (Fin 2) ℂ where
  toFun := blochHermitian 1
  linear := blochLinear
  map_vadd' r s := by
    apply HermitianMat.ext
    change blochMatrix 1 (s + r) = blochMatrix 0 s + blochMatrix 1 r
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blochMatrix] <;> ring

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
      hpX, hXp, sub_zero]
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

private theorem whole_rog {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ROG (⊤ : Submodule ℝ (HermitianMat ι ℂ)) := by
  classical
  intro X _ hX
  obtain ⟨m, w, hw⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp
    (HermitianMat.zero_le_iff.mp hX)
  let S := {j : Fin m // w j ≠ 0}
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S, fun j => WithLp.toLp 2 (w (e j)), ?_, ?_⟩
  · intro j
    exact ⟨fun hz => (e j).property (congrArg WithLp.ofLp hz), Submodule.mem_top⟩
  · have hfull : X = ∑ j, rankOne (w j) := by
      apply HermitianMat.ext
      rw [HermitianMat.mat_finset_sum]
      exact hw
    rw [hfull]
    have hfilt : (∑ j : S, rankOne (w j)) = ∑ j : Fin m, rankOne (w j) := by
      change (∑ j : {j : Fin m // w j ≠ 0}, rankOne (w j)) = _
      rw [← Finset.sum_subtype (Finset.univ.filter (fun j => w j ≠ 0))
        (by simp) (fun j => rankOne (w j))]
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j _ hj
      have hz : w j = 0 := by simpa using hj
      apply HermitianMat.ext
      change Matrix.vecMulVec (w j) (star (w j)) = 0
      simp [hz]
    rw [← hfilt]
    exact (e.sum_comp (fun j : S => rankOne (w j))).symm

/-- Every actual extreme point of the entire qutrit density body has a full
three-dimensional global affine chart of its entire original exclusion. -/
theorem all_pure_charts (p : pure (cone : PointedCone ℝ (HermitianMat (Fin 3) ℂ)) unit) :
    ∃ a : ExclusionChart cone unit (p : HermitianMat (Fin 3) ℂ), a.dim = 3 := by
  have hb : CircuitBalancedConfirmation.base cone unit =
      SectionROGFrame.base (⊤ : Submodule ℝ (HermitianMat (Fin 3) ℂ)) := by
    ext X
    simp [CircuitBalancedConfirmation.base, SectionROGFrame.base, cone, unit]
  have hp : (p : HermitianMat (Fin 3) ℂ) ∈ pureRanks
      (⊤ : Submodule ℝ (HermitianMat (Fin 3) ℂ)) := by
    rw [← whole_pure_carrier _ whole_rog, ← hb]
    exact p.property
  obtain ⟨v, hv, heq, _⟩ := hp
  obtain ⟨b, hb0, _, _, hsum⟩ := rog_frame
    (⊤ : Submodule ℝ (HermitianMat (Fin 3) ℂ)) Submodule.mem_top whole_rog v hv
    Submodule.mem_top (0 : Fin 3)
  let W : Matrix (Fin 3) (Fin 2) ℂ := fun i j => b j.succ i
  have hW : W.conjTranspose * W = 1 := by
    ext i j
    change star (b i.succ : Fin 3 → ℂ) ⬝ᵥ (b j.succ : Fin 3 → ℂ) = _
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    simpa [Matrix.one_apply] using (orthonormal_iff_ite.mp b.orthonormal i.succ j.succ)
  have hQ : W * W.conjTranspose = 1 - (rankOne v).mat := by
    have hh := congrArg HermitianMat.mat hsum
    change (HermitianMat.matₗ (R := ℝ) (∑ j, rankOne (b j))) = 1 at hh
    rw [map_sum] at hh
    have he : (rankOne (b 0)).mat + W * W.conjTranspose = 1 := by
      calc
        (rankOne (b 0)).mat + W * W.conjTranspose =
            ∑ j, (rankOne (b j)).mat := by
          change Matrix.vecMulVec (b 0 : Fin 3 → ℂ) (star (b 0 : Fin 3 → ℂ)) +
            W * W.conjTranspose = ∑ j, Matrix.vecMulVec (b j : Fin 3 → ℂ)
              (star (b j : Fin 3 → ℂ))
          ext i j
          change (b 0 i * star (b 0 j)) +
            (∑ k : Fin 2, W i k * star (W j k)) =
              ∑ k : Fin 3, b k i * star (b k j)
          simp [W, Fin.sum_univ_succ]
        _ = 1 := hh
    rw [hb0] at he
    exact eq_sub_of_add_eq' he
  rw [← heq]
  exact chart_of_full_frame v hv W hW hQ

end D5.S3.Quantum.Foundation.HermitianExclusionBall
