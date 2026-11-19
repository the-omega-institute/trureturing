/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceDerivative
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceDerivative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Genuine real radial derivative of the literal original Gaussian source constant. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceMeans

/-! The ordinary bilinear transpose closes the real radial source derivative. -/

noncomputable section
open scoped BigOperators Topology ENNReal
open Filter
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceDerivative
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianDifferentiation
open OriginalGaussianBilinearTranspose OriginalGaussianSourceMeans

theorem hasDerivAt_radial_source_pairing {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun u : ℝ =>
      innerSL ℂ (star (sourceFamily 0 (Real.sqrt u : ℂ)))
        (columnSeries (Real.sqrt u : ℂ)))
      (((1 / ((1 - r) * F r ^ 2) - 1) / (2 * r) : ℝ) : ℂ) r := by
  let z : ℂ := (Real.sqrt r : ℂ)
  let v : H := radialSourceFamily 0 r
  let w : H := radialSourceFamily 1 r
  let c : H := radialColumn r
  let P : ℂ := sourceBilinearFunctional v (radialColumnDerivative r)
  let t : ℂ := sourceBilinearFunctional w c
  let κ : ℂ := (radialNormalization r : ℂ)
  have hz : ‖z‖ < 1 := radial_norm_lt_one hr1
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hw : w = weightedSource r hr.le hr1 :=
    sourceFamily_one_eq_weightedSource hr.le hr1
  have hRv : resolvent z v = c := rfl
  have hnorm : 1 + t = κ := radial_pair_normalization hr hr1
  have hcross : sourceBilinearFunctional v (resolvent z w) = t := by
    rw [resolvent_bilinear_transpose hz v w, hRv]
    exact sourceBilinearFunctional_comm c w
  have hP : (r : ℂ) * P = (κ / 2) * t := by
    have h := congrArg (sourceBilinearFunctional v)
      (radial_column_derivative_scaled hr hr1)
    rw [← hw] at h
    simp only [map_smul, smul_eq_mul] at h
    change (r : ℂ) * P =
      (κ / 2) * sourceBilinearFunctional v (resolvent z w) at h
    rw [hcross] at h
    exact h
  have hd := (hasDerivAt_radial_sourceFamily 0 hr hr1).star.inner ℂ
    (hasDerivAt_radial_column hr hr1)
  change HasDerivAt (fun u : ℝ =>
    sourceBilinearFunctional (radialSourceFamily 0 u) (radialColumn u))
    (P + sourceBilinearFunctional
      ((1 / (2 * (r : ℂ))) • w) c) r at hd
  rw [sourceBilinearFunctional_smul_left] at hd
  have hs2 : (Real.sqrt (1 - r) : ℂ) ^ 2 = 1 - (r : ℂ) := by
    have h := Real.sq_sqrt (by linarith : 0 ≤ (1 : ℝ) - r)
    exact_mod_cast h
  have hκ2 : κ ^ 2 = 1 / ((1 - (r : ℂ)) * (F r : ℂ) ^ 2) := by
    dsimp only [κ, radialNormalization]
    push_cast
    rw [div_pow, one_pow, mul_pow, hs2]
  have hscaled :
      2 * (r : ℂ) * (P + (1 / (2 * (r : ℂ))) * t) = κ ^ 2 - 1 := by
    calc
      _ = 2 * ((r : ℂ) * P) + t := by
        field_simp [hr0] <;> ring
      _ = κ * t + t := by rw [hP]; ring
      _ = κ ^ 2 - 1 := by rw [← hnorm]; ring
  have hfinal :
      P + (1 / (2 * (r : ℂ))) * t =
        (((1 / ((1 - r) * F r ^ 2) - 1) / (2 * r) : ℝ) : ℂ) := by
    push_cast
    apply (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hr0)).mpr
    calc
      _ = κ ^ 2 - 1 := by linear_combination hscaled
      _ = _ := by rw [hκ2]
  simpa only [sourceBilinearFunctional, radialSourceFamily, radialColumn]
    using hd.congr_deriv hfinal

theorem hasDerivAt_radial_sourceConstant {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun u : ℝ => sourceConstant (Real.sqrt u : ℂ))
      (((1 / ((1 - r) * F r ^ 2) - 1) / (2 * r) : ℝ) : ℂ) r := by
  apply (hasDerivAt_radial_source_pairing
    hr hr1).congr_of_eventuallyEq
  have hU : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 r :=
    isOpen_Ioo.mem_nhds ⟨hr, hr1⟩
  filter_upwards [hU] with u hu
  exact ((source_pairings_explicit (radial_norm_lt_one hu.2) false 0).2.2.2).symm


end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceDerivative
