/- GID: D5/S3/HilbertOperators/RelativeMetricProjectionStability
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/RelativeMetricProjectionStability
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Relative metric stability for projections onto one subspace. -/

import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import D5.S3.Observer.BlockStructure.FourBlockDecomposition
import Mathlib.Analysis.Normed.Algebra.Exponential

/-! # Relative metric stability for orthogonal projections -/

set_option autoImplicit false

open ContinuousLinearMap
open scoped InnerProductSpace

namespace D5.S3.HilbertOperators.RelativeMetricProjectionStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private theorem realPartOfRealMul (a : ℝ) (z : ℂ) : ((a : ℂ) * z).re = a * z.re :=
  RCLike.re_ofReal_mul a z

omit [CompleteSpace E] in
private theorem realPartInnerSelf (x : E) : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) x

private theorem relativeVariance (A : E →L[ℂ] E) (hA : A.IsSymmetric)
    {l u : ℝ} (hLower : (l : ℂ) • (1 : E →L[ℂ] E) ≤ A)
    (hUpper : A ≤ (u : ℂ) • (1 : E →L[ℂ] E)) (w : E) (hw : ‖w‖ = 1) :
    l ≤ (⟪w, A w⟫_ℂ).re ∧
      ‖A w - ((⟪w, A w⟫_ℂ).re : ℂ) • w‖ ^ 2 ≤
        (u - (⟪w, A w⟫_ℂ).re) * ((⟪w, A w⟫_ℂ).re - l) := by
  have hl : 0 ≤ (⟪w, (A - (l : ℂ) • (1 : E →L[ℂ] E)) w⟫_ℂ).re :=
    (le_def.mp hLower).re_inner_nonneg_right w
  simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_right,
    inner_smul_right, Complex.sub_re, realPartOfRealMul, realPartInnerSelf, hw, one_pow,
    mul_one] at hl
  refine ⟨by linarith, ?_⟩
  have hComm : Commute (A - (l : ℂ) • (1 : E →L[ℂ] E))
      ((u : ℂ) • (1 : E →L[ℂ] E) - A) := by
    simp only [← Algebra.algebraMap_eq_smul_one]
    exact ((Algebra.commute_algebraMap_left u A).symm.sub_right (Commute.refl A)).sub_left
      ((Algebra.commute_algebraMap_left u (algebraMap ℂ (E →L[ℂ] E) l)).symm.sub_right
        (Algebra.commute_algebraMap_left l A))
  have hProd : 0 ≤ (⟪w, ((A - (l : ℂ) • (1 : E →L[ℂ] E)) *
      ((u : ℂ) • (1 : E →L[ℂ] E) - A)) w⟫_ℂ).re :=
    (nonneg_iff_isPositive.mp
      (hComm.mul_nonneg (sub_nonneg.mpr hLower) (sub_nonneg.mpr hUpper))).re_inner_nonneg_right w
  have hAA : ⟪w, A (A w)⟫_ℂ = ⟪A w, A w⟫_ℂ := (hA w (A w)).symm
  change 0 ≤ (⟪w, (A - (l : ℂ) • (1 : E →L[ℂ] E))
    (((u : ℂ) • (1 : E →L[ℂ] E) - A) w)⟫_ℂ).re at hProd
  simp only [sub_apply, smul_apply, one_apply_eq_self, map_sub, map_smul,
    inner_sub_right, inner_smul_right, Complex.sub_re, realPartOfRealMul, hAA, realPartInnerSelf,
    hw, one_pow, mul_one] at hProd
  have hSym : ⟪A w, w⟫_ℂ = ⟪w, A w⟫_ℂ := hA w w
  have hCross : ⟪A w, ((⟪w, A w⟫_ℂ).re : ℂ) • w⟫_ℂ =
      ((⟪w, A w⟫_ℂ).re : ℂ) * ⟪w, A w⟫_ℂ := by
    rw [inner_smul_right, hSym]
  rw [@norm_sub_sq ℂ, hCross, norm_smul, Complex.norm_real, Real.norm_eq_abs, hw, mul_one,
    sq_abs]
  change ‖A w‖ ^ 2 - 2 * (((⟪w, A w⟫_ℂ).re : ℂ) * ⟪w, A w⟫_ℂ).re +
    (⟪w, A w⟫_ℂ).re ^ 2 ≤ _
  rw [realPartOfRealMul]
  nlinarith only [hProd]

/-- The norm of the difference between the reference orthogonal projection and
the projection onto the same subspace for the metric induced by `A`. -/
theorem opNorm_sub_starProjection_le (V : Submodule ℂ E) [V.HasOrthogonalProjection]
    (A R : E →L[ℂ] E) (hA : A.IsSymmetric) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hLower : (l : ℂ) • (1 : E →L[ℂ] E) ≤ A)
    (hUpper : A ≤ (u : ℂ) • (1 : E →L[ℂ] E))
    (hRange : ∀ x, R x ∈ V) (hFix : ∀ v ∈ V, R v = v)
    (hOrth : ∀ x v, v ∈ V → ⟪v, A (x - R x)⟫_ℂ = 0) :
    ‖R - V.starProjection‖ ≤ (u - l) / (2 * Real.sqrt (u * l)) := by
  let c := (u - l) / (2 * Real.sqrt (u * l))
  have hu : 0 < u := hl.trans_le hlu
  have hc : 0 ≤ c := div_nonneg (sub_nonneg.mpr hlu) (by positivity)
  have hs : 0 < Real.sqrt (u * l) := Real.sqrt_pos.2 (mul_pos hu hl)
  have hcSq : 4 * (u * l) * c ^ 2 = (u - l) ^ 2 := by
    dsimp [c]
    rw [div_pow, mul_pow, Real.sq_sqrt (mul_pos hu hl).le]
    field_simp <;> ring
  have residual (y : E) (hy : y ∈ Vᗮ) : ‖R y‖ ≤ c * ‖y‖ := by
    by_cases hz : R y = 0
    · simpa [hz] using mul_nonneg hc (norm_nonneg y)
    let n := ‖R y‖
    have hn : 0 < n := norm_pos_iff.mpr hz
    let w := ((n⁻¹ : ℝ) : ℂ) • R y
    have hwV : w ∈ V := V.smul_mem _ (hRange y)
    have hw : ‖w‖ = 1 := by
      dsimp only [w]
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
      exact inv_mul_cancel₀ (ne_of_gt hn)
    have hv : R y = (n : ℂ) • w := by
      simp [w, smul_smul, mul_inv_cancel₀ (ne_of_gt hn)]
    let m := (⟪w, A w⟫_ℂ).re
    let z := A w - (m : ℂ) • w
    obtain ⟨hm, hVar⟩ : l ≤ m ∧ ‖z‖ ^ 2 ≤ (u - m) * (m - l) :=
      relativeVariance A hA hLower hUpper w hw
    have hmPos : 0 < m := hl.trans_le hm
    have hSquare : (2 * u * l - (u + l) * m) ^ 2 =
        (u - l) ^ 2 * m ^ 2 - 4 * (u * l) * ((u - m) * (m - l)) := by ring
    have hVarBound : ‖z‖ ^ 2 ≤ (c * m) ^ 2 := by
      apply le_of_mul_le_mul_left (a := 4 * (u * l))
      · calc
          4 * (u * l) * ‖z‖ ^ 2 ≤ 4 * (u * l) * ((u - m) * (m - l)) :=
            mul_le_mul_of_nonneg_left hVar (by positivity)
          _ ≤ (u - l) ^ 2 * m ^ 2 := by
            linarith only [hSquare, sq_nonneg (2 * u * l - (u + l) * m)]
          _ = 4 * (u * l) * (c * m) ^ 2 := by rw [mul_pow, ← mul_assoc, hcSq]
      · positivity
    have hzNorm : ‖z‖ ≤ c * m :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc hmPos.le)).mp hVarBound
    have hEq := hOrth y w hwV
    rw [map_sub, inner_sub_right, sub_eq_zero, hv, map_smul, inner_smul_right] at hEq
    have hzy : (⟪z, y⟫_ℂ).re = n * m := by
      dsimp only [z]
      have hMove : ⟪A w, y⟫_ℂ = ⟪w, A y⟫_ℂ := hA w y
      rw [inner_sub_left, inner_smul_left, V.inner_right_of_mem_orthogonal hwV hy,
        mul_zero, sub_zero, hMove, hEq, realPartOfRealMul]
    have hCS : n * m ≤ ‖z‖ * ‖y‖ := hzy ▸ re_inner_le_norm (𝕜 := ℂ) z y
    have hScaled : n * m ≤ (c * ‖y‖) * m := calc
      n * m ≤ ‖z‖ * ‖y‖ := hCS
      _ ≤ (c * m) * ‖y‖ := mul_le_mul_of_nonneg_right hzNorm (norm_nonneg _)
      _ = (c * ‖y‖) * m := by ring
    exact le_of_mul_le_mul_right hScaled hmPos
  apply opNorm_le_bound _ hc
  intro x
  have hSplit := V.starProjection_add_starProjection_orthogonal x
  have hResidual : x - V.starProjection x = Vᗮ.starProjection x := by
    rw [sub_eq_iff_eq_add, add_comm]
    exact hSplit.symm
  have hEval : (R - V.starProjection) x = R (x - V.starProjection x) := by
    rw [sub_apply, map_sub, hFix _ (V.starProjection_apply_mem x)]
  rw [hEval]
  exact (residual _ (V.sub_starProjection_mem_orthogonal x)).trans
    (mul_le_mul_of_nonneg_left (hResidual ▸ Vᗮ.norm_starProjection_apply_le x) hc)

#print axioms opNorm_sub_starProjection_le


open D5.S3.Observer.BlockStructure.FourBlockDecomposition

/-- The change of metric affects the visible compression only through the
reference-metric leakage of the evolution out of the visible subspace. -/
theorem visibleCompression_sub_le (V : Submodule ℂ E) [V.HasOrthogonalProjection]
    (A : E →L[ℂ] E) (R : E →L[ℂ] V) (hA : A.IsSymmetric)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hLower : (l : ℂ) • (1 : E →L[ℂ] E) ≤ A)
    (hUpper : A ≤ (u : ℂ) • (1 : E →L[ℂ] E))
    (hFix : ∀ v : V, R v = v)
    (hOrth : ∀ x v, v ∈ V → ⟪v, A (x - (R x : E))⟫_ℂ = 0)
    (T : E →L[ℂ] E) :
    ‖R.comp (T.comp V.subtypeL) - visibleInternalBlock V T‖ ≤
      ((u - l) / (2 * Real.sqrt (u * l))) * ‖visibleResidualLeakage V T‖ := by
  have hBound := opNorm_sub_starProjection_le V A (V.subtypeL.comp R) hA hl hlu
    hLower hUpper (fun x => (R x).property)
    (fun v hv => congrArg Subtype.val (hFix ⟨v, hv⟩)) hOrth
  have hRestriction : ‖R.comp Vᗮ.subtypeL‖ ≤ ‖V.subtypeL.comp R - V.starProjection‖ := by
    apply opNorm_le_bound _ (norm_nonneg _)
    intro y
    have hy : V.starProjection (y : E) = 0 := V.starProjection_apply_eq_zero_iff.mpr y.property
    simpa only [comp_apply, Submodule.subtypeL_apply, sub_apply, hy, sub_zero,
      Submodule.norm_coe] using (V.subtypeL.comp R - V.starProjection).le_opNorm (y : E)
  have hFactor : R.comp (T.comp V.subtypeL) - visibleInternalBlock V T =
      (R.comp Vᗮ.subtypeL).comp (visibleResidualLeakage V T) := by
    apply ContinuousLinearMap.ext
    intro x
    have hx := V.starProjection_mem_subspace_eq_self x
    have hDecomp := congrArg R (V.starProjection_add_starProjection_orthogonal (T x))
    rw [map_add] at hDecomp
    change R ((V.orthogonalProjectionOnto (T x) : V) : E) +
      R (Vᗮ.starProjection (T x)) = R (T x) at hDecomp
    rw [hFix] at hDecomp
    simp only [visibleInternalBlock, visibleResidualLeakage, comp_apply, sub_apply,
      Submodule.subtypeL_apply, hx]
    change R (T x) - V.orthogonalProjectionOnto (T x) = R (Vᗮ.starProjection (T x))
    rw [sub_eq_iff_eq_add, add_comm]
    exact hDecomp.symm
  rw [hFactor]
  exact (opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (hRestriction.trans hBound) (norm_nonneg _))

#print axioms visibleCompression_sub_le

end D5.S3.HilbertOperators.RelativeMetricProjectionStability
