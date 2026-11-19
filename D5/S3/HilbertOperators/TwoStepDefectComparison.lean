/- GID: D5/S3/HilbertOperators/TwoStepDefectComparison
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/TwoStepDefectComparison
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Compare two-step defects through the reference orthogonal blocks. -/

import D5.S3.HilbertOperators.RelativeMetricProjectionStability
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Two-step defect comparison in a reference orthogonal split -/

set_option autoImplicit false

open ContinuousLinearMap
open scoped InnerProductSpace

namespace D5.S3.HilbertOperators.TwoStepDefectComparison

open D5.S3.Observer.BlockStructure.FourBlockDecomposition
open D5.S3.HilbertOperators.RelativeMetricProjectionStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (V : Submodule ℂ E) [V.HasOrthogonalProjection]

/-- Two-step compression minus the square of the one-step compression. -/
noncomputable def twoStepDefect (R : E →L[ℂ] V) (T : E →L[ℂ] E) : V →L[ℂ] V :=
  R.comp ((T * T).comp V.subtypeL) - (R.comp (T.comp V.subtypeL)) ^ 2

omit [CompleteSpace E] in
private theorem retraction_split (R : E →L[ℂ] V) (hFix : ∀ x : V, R x = x)
    (z : E) : R z = V.orthogonalProjectionOnto z +
      R (Vᗮ.starProjection z) := by
  have h := congrArg R (V.starProjection_add_starProjection_orthogonal z)
  rw [map_add] at h
  change R ((V.orthogonalProjectionOnto z : V) : E) + R (Vᗮ.starProjection z) = R z at h
  rw [hFix] at h
  exact h.symm

omit [CompleteSpace E] in
private theorem defect_apply (R : E →L[ℂ] V) (hFix : ∀ x : V, R x = x)
    (T : E →L[ℂ] E) (x : V) :
    twoStepDefect V R T x =
      R (T (visibleResidualLeakage V T x : E)) -
        R (T (R (visibleResidualLeakage V T x : E) : E)) := by
  let y := visibleResidualLeakage V T x
  have hy : (y : E) = Vᗮ.starProjection (T x) := by
    simp [y, visibleResidualLeakage, comp_apply]
  have hsplit : (T x : E) = (V.orthogonalProjectionOnto (T x) : E) + (y : E) := by
    rw [hy]
    exact (V.starProjection_add_starProjection_orthogonal (T x)).symm
  have hR : R (T x) = V.orthogonalProjectionOnto (T x) + R y := by
    rw [hy]
    exact retraction_split V R hFix _
  change R (T (T x)) - R (T (R (T x) : E)) = _
  change _ = R (T (y : E)) - R (T (R y : E))
  conv_lhs =>
    congr
    · rw [hsplit, map_add, map_add]
    · rw [hR, Submodule.coe_add, map_add, map_add]
  abel

/-- The change of two-step defect factors through the reference leakage block. -/
theorem defect_sub_eq (R : E →L[ℂ] V) (hFix : ∀ x : V, R x = x) (T : E →L[ℂ] E) :
    let K := R.comp Vᗮ.subtypeL
    let ER := R.comp (T.comp V.subtypeL)
    twoStepDefect V R T - twoStepDefect V V.orthogonalProjectionOnto T =
      (K.comp (residualInternalBlock V T) - ER.comp K).comp (visibleResidualLeakage V T) := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro x
  rw [sub_apply, defect_apply V R hFix,
    defect_apply V V.orthogonalProjectionOnto V.orthogonalProjectionOnto_mem_subspace_eq_self]
  let y := visibleResidualLeakage V T x
  have hPy : V.orthogonalProjectionOnto (y : E) = 0 := by
    apply Subtype.ext
    exact V.starProjection_apply_eq_zero_iff.mpr y.property
  have hW : (residualInternalBlock V T y : E) = Vᗮ.starProjection (T y) := by
    simp [residualInternalBlock, comp_apply]
  change R (T y) - R (T (R y : E)) -
      (V.orthogonalProjectionOnto (T y) - V.orthogonalProjectionOnto
        (T (V.orthogonalProjectionOnto (y : E) : E))) =
    R (residualInternalBlock V T y : E) - R (T (R y : E))
  rw [hPy, Submodule.coe_zero, map_zero, map_zero, sub_zero, hW,
    retraction_split V R hFix (T y)]
  abel

/-- Scalar centering cancels between the two terms in the factorization. -/
theorem norm_defect_sub_le (R : E →L[ℂ] V) (hFix : ∀ x : V, R x = x)
    (T : E →L[ℂ] E) (center : ℂ) :
    let K := R.comp Vᗮ.subtypeL
    let ER := R.comp (T.comp V.subtypeL)
    ‖twoStepDefect V R T - twoStepDefect V V.orthogonalProjectionOnto T‖ ≤
      ‖K‖ * (‖residualInternalBlock V T - center • 1‖ + ‖ER - center • 1‖) *
        ‖visibleResidualLeakage V T‖ := by
  let K := R.comp Vᗮ.subtypeL
  let ER := R.comp (T.comp V.subtypeL)
  let W := residualInternalBlock V T
  let C := visibleResidualLeakage V T
  let W₀ := W - center • 1
  let ER₀ := ER - center • 1
  change _ ≤ ‖K‖ * (‖W₀‖ + ‖ER₀‖) * ‖C‖
  rw [defect_sub_eq V R hFix T]
  change ‖(K.comp W - ER.comp K).comp C‖ ≤ _
  have hCenter : K.comp W - ER.comp K = K.comp W₀ - ER₀.comp K := by
    apply ContinuousLinearMap.ext
    intro y
    simp [W₀, ER₀, comp_apply, one_apply_eq_self]
  rw [hCenter]
  calc
    _ ≤ ‖K.comp W₀ - ER₀.comp K‖ * ‖C‖ := opNorm_comp_le _ _
    _ ≤ (‖K.comp W₀‖ + ‖ER₀.comp K‖) * ‖C‖ :=
      mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ (‖K‖ * ‖W₀‖ + ‖ER₀‖ * ‖K‖) * ‖C‖ :=
      mul_le_mul_of_nonneg_right (add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _))
        (norm_nonneg _)
    _ = _ := by ring

omit [CompleteSpace E] in
private theorem norm_hidden_restriction_le (R : E →L[ℂ] V) :
    ‖R.comp Vᗮ.subtypeL‖ ≤ ‖V.subtypeL.comp R - V.starProjection‖ := by
  apply opNorm_le_bound _ (norm_nonneg _)
  intro y
  have hy : V.starProjection (y : E) = 0 := V.starProjection_apply_eq_zero_iff.mpr y.property
  simpa only [comp_apply, Submodule.subtypeL_apply, sub_apply, hy, sub_zero,
    Submodule.norm_coe] using (V.subtypeL.comp R - V.starProjection).le_opNorm (y : E)

/-- Relative metric defect bound, with every operator norm taken in the reference metric. -/
theorem norm_defect_sub_le_relative (A : E →L[ℂ] E) (R : E →L[ℂ] V)
    (hA : A.IsSymmetric) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hLower : (l : ℂ) • (1 : E →L[ℂ] E) ≤ A)
    (hUpper : A ≤ (u : ℂ) • (1 : E →L[ℂ] E))
    (hFix : ∀ v : V, R v = v)
    (hOrth : ∀ x v, v ∈ V → ⟪v, A (x - (R x : E))⟫_ℂ = 0)
    (T : E →L[ℂ] E) (center : ℂ) :
    let ER := R.comp (T.comp V.subtypeL)
    ‖twoStepDefect V R T - twoStepDefect V V.orthogonalProjectionOnto T‖ ≤
      ((u - l) / (2 * Real.sqrt (u * l))) *
        (‖residualInternalBlock V T - center • 1‖ + ‖ER - center • 1‖) *
        ‖visibleResidualLeakage V T‖ := by
  dsimp only
  have hK := (norm_hidden_restriction_le V R).trans
    (opNorm_sub_starProjection_le V A (V.subtypeL.comp R) hA hl hlu hLower hUpper
      (fun x => (R x).property)
      (fun v hv => congrArg Subtype.val (hFix ⟨v, hv⟩)) hOrth)
  exact (norm_defect_sub_le V R hFix T center).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (by positivity))
      (norm_nonneg _))

/-- The bounded-operator exponential gives a genuine double-time defect. -/
theorem exponential_defect_sub_eq (R : E →L[ℂ] V) (hFix : ∀ x : V, R x = x)
    (L : E →L[ℂ] E) (t : ℝ) :
    let T := NormedSpace.exp ((t : ℂ) • L)
    let T₂ := NormedSpace.exp (((2 * t : ℝ) : ℂ) • L)
    let K := R.comp Vᗮ.subtypeL
    let ER := R.comp (T.comp V.subtypeL)
    let EP := visibleInternalBlock V T
    (R.comp (T₂.comp V.subtypeL) - ER ^ 2) -
      (V.orthogonalProjectionOnto.comp (T₂.comp V.subtypeL) - EP ^ 2) =
      (K.comp (residualInternalBlock V T) - ER.comp K).comp (visibleResidualLeakage V T) := by
  dsimp only
  have hEP (T : E →L[ℂ] E) : visibleInternalBlock V T =
      V.orthogonalProjectionOnto.comp (T.comp V.subtypeL) := by
    apply ContinuousLinearMap.ext
    intro x
    simp [visibleInternalBlock, comp_apply]
  have hTime : (((2 * t : ℝ) : ℂ) • L) = (t : ℂ) • L + (t : ℂ) • L := by
    rw [two_mul, Complex.ofReal_add, add_smul]
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ _
  rw [hEP, hTime, NormedSpace.exp_add_of_commute (Commute.refl _)]
  exact defect_sub_eq V R hFix _

omit [CompleteSpace E] in
private theorem centered_block_bounds (R : E →L[ℂ] V) (hFix : ∀ x : V, R x = x)
    (T : E →L[ℂ] E) (center : ℂ) :
    ‖residualInternalBlock V T - center • 1‖ ≤ ‖T - center • 1‖ ∧
    ‖R.comp (T.comp V.subtypeL) - center • 1‖ ≤ ‖R‖ * ‖T - center • 1‖ ∧
    ‖visibleResidualLeakage V T‖ ≤ ‖T - center • 1‖ := by
  let S := T - center • 1
  constructor
  · apply opNorm_le_bound _ (norm_nonneg S)
    intro y
    have hEval : (residualInternalBlock V T - center • 1) y =
        Vᗮ.orthogonalProjectionOnto (S y) := by
      simp [S, residualInternalBlock, comp_apply, map_sub, map_smul, one_apply_eq_self,
        Vᗮ.orthogonalProjectionOnto_mem_subspace_eq_self y]
    rw [hEval]
    exact (Vᗮ.norm_orthogonalProjectionOnto_apply_le _).trans (S.le_opNorm (y : E))
  constructor
  · apply opNorm_le_bound _ (by positivity)
    intro x
    have hEval : (R.comp (T.comp V.subtypeL) - center • 1) x = R (S x) := by
      simp [S, comp_apply, map_sub, map_smul, one_apply_eq_self, hFix]
    rw [hEval, mul_assoc]
    exact (R.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (S.le_opNorm (x : E)) (norm_nonneg _))
  · apply opNorm_le_bound _ (norm_nonneg S)
    intro x
    have hZero : Vᗮ.orthogonalProjectionOnto (x : E) = 0 :=
      Vᗮ.orthogonalProjectionOnto_apply_of_mem_orthogonal (V.le_orthogonal_orthogonal x.property)
    have hEval : visibleResidualLeakage V T x = Vᗮ.orthogonalProjectionOnto (S x) := by
      simp [S, visibleResidualLeakage, comp_apply, map_sub, map_smul, one_apply_eq_self, hZero]
    rw [hEval]
    exact (Vᗮ.norm_orthogonalProjectionOnto_apply_le _).trans (S.le_opNorm (x : E))

/-- A quadratic bound in the ambient distance to any scalar operator. -/
theorem norm_defect_sub_le_sq (R : E →L[ℂ] V) (hFix : ∀ x : V, R x = x)
    (T : E →L[ℂ] E) (center : ℂ) :
    ‖twoStepDefect V R T - twoStepDefect V V.orthogonalProjectionOnto T‖ ≤
      ‖R.comp Vᗮ.subtypeL‖ * (1 + ‖R‖) * ‖T - center • 1‖ ^ 2 := by
  obtain ⟨hW, hER, hC⟩ := centered_block_bounds V R hFix T center
  calc
    _ ≤ ‖R.comp Vᗮ.subtypeL‖ *
        (‖residualInternalBlock V T - center • 1‖ +
          ‖R.comp (T.comp V.subtypeL) - center • 1‖) * ‖visibleResidualLeakage V T‖ :=
      norm_defect_sub_le V R hFix T center
    _ ≤ ‖R.comp Vᗮ.subtypeL‖ *
        (‖T - center • 1‖ + ‖R‖ * ‖T - center • 1‖) * ‖T - center • 1‖ := by
      gcongr
    _ = _ := by ring

open Asymptotics Filter
open scoped Topology

/-- The difference of defects along the exponential is quadratic at time zero. -/
theorem exponential_defect_sub_isBigO (R : E →L[ℂ] V) (hFix : ∀ x : V, R x = x)
    (L : E →L[ℂ] E) :
    (fun t : ℝ =>
      let T := NormedSpace.exp ((t : ℂ) • L)
      twoStepDefect V R T - twoStepDefect V V.orthogonalProjectionOnto T)
        =O[𝓝 (0 : ℝ)] (fun t : ℝ => t ^ 2) := by
  let scale : ℝ →L[ℝ] (E →L[ℂ] E) := Complex.ofRealCLM.smulRight L
  have hExp : DifferentiableAt ℝ (fun t : ℝ => NormedSpace.exp ((t : ℂ) • L)) 0 := by
    have hZero : scale (0 : ℝ) = 0 := map_zero _
    have hDeriv := hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := E →L[ℂ] E)
    rw [← hZero] at hDeriv
    exact (hDeriv.comp 0 scale.hasFDerivAt).differentiableAt
  have hLinear : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • L) - 1)
      =O[𝓝 (0 : ℝ)] (fun t : ℝ => t) := by
    simpa [NormedSpace.exp_zero] using hExp.isBigO_sub
  obtain ⟨M, hM, hNear⟩ := isBigO_iff'.mp hLinear
  apply isBigO_iff.mpr
  refine ⟨‖R.comp Vᗮ.subtypeL‖ * (1 + ‖R‖) * M ^ 2, ?_⟩
  filter_upwards [hNear] with t ht
  have hSq : ‖NormedSpace.exp ((t : ℂ) • L) - 1‖ ^ 2 ≤ M ^ 2 * ‖t ^ 2‖ := by
    rw [norm_pow, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ht 2
  have hDefect := norm_defect_sub_le_sq V R hFix (NormedSpace.exp ((t : ℂ) • L)) 1
  rw [one_smul] at hDefect
  rw [mul_assoc]
  exact hDefect.trans (mul_le_mul_of_nonneg_left hSq (by positivity))

#print axioms defect_sub_eq
#print axioms norm_defect_sub_le
#print axioms norm_defect_sub_le_relative
#print axioms exponential_defect_sub_eq
#print axioms norm_defect_sub_le_sq
#print axioms exponential_defect_sub_isBigO

end D5.S3.HilbertOperators.TwoStepDefectComparison
