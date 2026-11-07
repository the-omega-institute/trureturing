/- GID: D5/S3/Quantum/Measurements/UnitaryOrthogonalWeight
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/UnitaryOrthogonalWeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unitary invariance and orthogonal additivity determine the squared norm. -/

import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Module.Span
import Mathlib.Algebra.Module.Rat
import Mathlib.Tactic

noncomputable section

open scoped InnerProductSpace
open Submodule Module

namespace D5.S3.Quantum.Measurements.UnitaryOrthogonalWeight

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

private theorem finite_unitary_transport [FiniteDimensional 𝕜 H]
    (x y : H) (hxy : ‖x‖ = ‖y‖) : ∃ U : H ≃ₗᵢ[𝕜] H, U x = y := by
  by_cases hx : x = 0
  · have hy : y = 0 := norm_eq_zero.mp (by simpa [hx] using hxy.symm)
    exact ⟨LinearIsometryEquiv.refl 𝕜 H, by simp [hx, hy]⟩
  let e := LinearEquiv.toSpanNonzeroSingleton 𝕜 H x hx
  let L : (𝕜 ∙ x) →ₗᵢ[𝕜] H :=
    { toLinearMap := (LinearMap.toSpanSingleton 𝕜 H y).comp e.symm.toLinearMap
      norm_map' := by
        intro z
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp z.property
        have hz : z = e a := Subtype.ext ha.symm
        rw [hz]
        simp [e, norm_smul, hxy] }
  refine ⟨L.extend.toLinearIsometryEquiv rfl, ?_⟩
  change L.extend x = y
  rw [← show (⟨x, Submodule.mem_span_singleton_self x⟩ : 𝕜 ∙ x).val = x from rfl,
    L.extend_apply]
  change (LinearMap.toSpanSingleton 𝕜 H y) (e.symm ⟨x, _⟩) = y
  simp [e, ← LinearEquiv.coord_apply, LinearEquiv.coord_self]

private theorem unitary_transport (x y : H) (hxy : ‖x‖ = ‖y‖) :
    ∃ U : H ≃ₗᵢ[𝕜] H, U x = y := by
  let S := Submodule.span 𝕜 ({x, y} : Set H)
  letI : FiniteDimensional 𝕜 S := FiniteDimensional.span_of_finite 𝕜 (Set.toFinite _)
  let xs : S := ⟨x, Submodule.subset_span (by simp)⟩
  let ys : S := ⟨y, Submodule.subset_span (by simp)⟩
  obtain ⟨V, hV⟩ := finite_unitary_transport xs ys hxy
  let D := S.orthogonalDecomposition
  let U := D.trans ((V.withLpProdCongr 2 (LinearIsometryEquiv.refl 𝕜 Sᗮ)).trans D.symm)
  refine ⟨U, ?_⟩
  have hx : D x = WithLp.toLp 2 (xs, (0 : Sᗮ)) := by
    simp [D, Submodule.orthogonalDecomposition_apply, xs]
  have hy : D y = WithLp.toLp 2 (ys, (0 : Sᗮ)) := by
    simp [D, Submodule.orthogonalDecomposition_apply, ys]
  apply D.injective
  simp [U, hx, hy, hV]

/-- A nonnegative weight on any real or complex Hilbert space of rank at least two,
invariant under all linear isometric equivalences, orthogonally additive and one on
unit vectors, is the squared norm. No regularity of the weight is assumed. -/
theorem unitary_orthogonal_weight_eq_norm_sq [CompleteSpace H]
    (hdim : 2 ≤ Module.rank 𝕜 H) (W : H → ℝ≥0)
    (hU : ∀ (U : H ≃ₗᵢ[𝕜] H) (v : H), W (U v) = W v)
    (hadd : ∀ x y : H, ⟪x, y⟫_𝕜 = 0 → W (x + y) = W x + W y)
    (hone : ∀ u : H, ‖u‖ = 1 → W u = 1) (v : H) :
    (W v : ℝ) = ‖v‖ ^ 2 := by
  classical
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_rank hdim
  let e := gramSchmidtNormed 𝕜 b
  have he : Orthonormal 𝕜 e := gramSchmidtNormed_orthonormal hb
  have radial (x y : H) (hxy : ‖x‖ = ‖y‖) : W x = W y := by
    obtain ⟨U, hUv⟩ := unitary_transport x y hxy
    rw [← hUv, hU]
  let f : ℝ≥0 → ℝ≥0 := fun s => W ((Real.sqrt (s : ℝ) : 𝕜) • e 0)
  have norm_radius (s : ℝ≥0) (i : Fin 2) :
      ‖(Real.sqrt (s : ℝ) : 𝕜) • e i‖ = Real.sqrt (s : ℝ) := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _), he.norm_eq_one,
      mul_one]
  have hf (s : ℝ≥0) (x : H) (hx : ‖x‖ ^ 2 = (s : ℝ)) : W x = f s := by
    apply radial
    rw [norm_radius]
    exact (Real.sqrt_eq_iff_sq_eq (norm_nonneg _) s.property).2 hx.symm |>.symm
  have fadd (s t : ℝ≥0) : f (s + t) = f s + f t := by
    let x := (Real.sqrt (s : ℝ) : 𝕜) • e 0
    let y := (Real.sqrt (t : ℝ) : 𝕜) • e 1
    have horth : ⟪x, y⟫_𝕜 = 0 := by
      simp [x, y, inner_smul_left, inner_smul_right, he.inner_eq_zero (by decide : (0 : Fin 2) ≠ 1)]
    have hxs : ‖x‖ ^ 2 = (s : ℝ) := by rw [norm_radius, Real.sq_sqrt s.property]
    have hyt : ‖y‖ ^ 2 = (t : ℝ) := by rw [norm_radius, Real.sq_sqrt t.property]
    have hsum : ‖x + y‖ ^ 2 = ((s + t : ℝ≥0) : ℝ) := by
      rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y horth, hxs, hyt,
        NNReal.coe_add]
    rw [← hf (s + t) (x + y) hsum, hadd x y horth, hf s x hxs, hf t y hyt]
  have fzero : f 0 = 0 := by
    have hz := fadd 0 0
    simpa using (add_left_cancel (show f 0 + f 0 = f 0 + 0 by simpa using hz.symm))
  let F : ℝ≥0 →+ ℝ≥0 := { toFun := f, map_zero' := fzero, map_add' := fadd }
  have fone : F 1 = 1 := by
    change W ((Real.sqrt (1 : ℝ) : 𝕜) • e 0) = 1
    simpa using hone (e 0) (he.norm_eq_one 0)
  have fmono : Monotone F := by
    intro s t hst
    obtain ⟨r, rfl⟩ := exists_add_of_le hst
    rw [map_add]
    exact le_add_of_nonneg_right (zero_le _)
  have frat (q : ℚ≥0) : F (q : ℝ≥0) = q := by
    have h := map_nnrat_smul F q (1 : ℝ≥0)
    simpa [fone, NNRat.smul_def] using h
  have fid (s : ℝ≥0) : F s = s := by
    apply le_antisymm
    · by_contra h
      have hlt : (s : ℝ) < (F s : ℝ) := by exact_mod_cast (lt_of_not_ge h)
      obtain ⟨q, hsq, hqf⟩ := exists_rat_btwn hlt
      let qn : ℚ≥0 := ⟨q, by exact_mod_cast (s.property.trans hsq.le)⟩
      have hs : s ≤ (qn : ℝ≥0) := by exact_mod_cast hsq.le
      have hle := fmono hs
      rw [frat] at hle
      have hr : (F s : ℝ) ≤ (q : ℝ) := by exact_mod_cast hle
      linarith
    · by_contra h
      have hlt : (F s : ℝ) < (s : ℝ) := by exact_mod_cast (lt_of_not_ge h)
      obtain ⟨q, hfq, hqs⟩ := exists_rat_btwn hlt
      let qn : ℚ≥0 := ⟨q, by exact_mod_cast ((F s).property.trans hfq.le)⟩
      have hs : (qn : ℝ≥0) ≤ s := by exact_mod_cast hqs.le
      have hle := fmono hs
      rw [frat] at hle
      have hr : (q : ℝ) ≤ (F s : ℝ) := by exact_mod_cast hle
      linarith
  let s : ℝ≥0 := ⟨‖v‖ ^ 2, sq_nonneg _⟩
  have hv := hf s v rfl
  change W v = F s at hv
  exact congrArg (fun r : ℝ≥0 => (r : ℝ)) (hv.trans (fid s))

end D5.S3.Quantum.Measurements.UnitaryOrthogonalWeight
