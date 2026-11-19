/- GID: D5/S3/Quantum/Recovery/BKMActualMetricHeat
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/BKMActualMetricHeat
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Compare genuine finite BKM heat compression defects. -/

import D5.S3.Quantum.Recovery.BKMActualMetricCoordinates
import D5.S3.HilbertOperators.TwoStepDefectComparison

/-! # Genuine finite BKM heat compression defects -/

noncomputable section

open ContinuousLinearMap
open scoped MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder

namespace D5.S3.Quantum.Recovery.BKMActualMetricHeat

open D5.S3.Quantum.Recovery.BKMActualMetricCoordinates
open D5.S3.HilbertOperators.TwoStepDefectComparison
open D5.S3.Observer.BlockStructure.FourBlockDecomposition

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]
variable (V : Submodule ℂ E) (Z : E →L[ℂ] E)

private def gram : V →L[ℂ] V :=
  V.orthogonalProjectionOnto.comp (Z.comp V.subtypeL)

private theorem gram_injective {l : ℝ} (hl : 0 < l)
    (hlo : (l : ℂ) • (1 : E →L[ℂ] E) ≤ Z) :
    Function.Injective (gram V Z) := by
  change Function.Injective (gram V Z).toLinearMap
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  apply Subtype.ext
  change (v : E) = 0
  have hi : ⟪(v : E), Z v⟫_ℂ = 0 := by
    rw [← V.inner_orthogonalProjectionOnto_eq_of_mem_left v (Z v)]
    change ⟪v, gram V Z v⟫_ℂ = 0
    change gram V Z v = 0 at hv
    rw [hv, inner_zero_right]
  have hq := (ContinuousLinearMap.le_def.mp hlo).re_inner_nonneg_right (v : E)
  simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_right, hi,
    inner_smul_right] at hq
  change 0 ≤ (0 - (l : ℂ) * ⟪(v : E), (v : E)⟫_ℂ).re at hq
  rw [Complex.sub_re, Complex.zero_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hq
  have hvre : (⟪(v : E), (v : E)⟫_ℂ).re = ‖(v : E)‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hvre] at hq
  have hzero : ‖(v : E)‖ = 0 := by
    by_contra hn
    have hp := mul_pos hl (sq_pos_of_ne_zero hn)
    linarith
  exact norm_eq_zero.mp hzero

private def gramEquiv {l : ℝ} (hl : 0 < l)
    (hlo : (l : ℂ) • (1 : E →L[ℂ] E) ≤ Z) : V ≃L[ℂ] V :=
  (LinearEquiv.ofInjectiveEndo (gram V Z).toLinearMap
    (gram_injective V Z hl hlo)).toContinuousLinearEquiv

/-- Orthogonal projection for the form with coefficient Z, in reference coordinates. -/
def relativeProjection {l : ℝ} (hl : 0 < l)
    (hlo : (l : ℂ) • (1 : E →L[ℂ] E) ≤ Z) : E →L[ℂ] V :=
  (gramEquiv V Z hl hlo).symm.toContinuousLinearMap.comp
    (V.orthogonalProjectionOnto.comp Z)

theorem relativeProjection_fix {l : ℝ} (hl : 0 < l)
    (hlo : (l : ℂ) • (1 : E →L[ℂ] E) ≤ Z) (v : V) :
    relativeProjection V Z hl hlo v = v :=
  (gramEquiv V Z hl hlo).symm_apply_apply v

theorem relativeProjection_orthogonal {l : ℝ} (hl : 0 < l)
    (hlo : (l : ℂ) • (1 : E →L[ℂ] E) ≤ Z) (x v : E) (hv : v ∈ V) :
    ⟪v, Z (x - (relativeProjection V Z hl hlo x : E))⟫_ℂ = 0 := by
  let w : V := ⟨v, hv⟩
  change ⟪(w : E), Z (x - (relativeProjection V Z hl hlo x : E))⟫_ℂ = 0
  rw [← V.inner_orthogonalProjectionOnto_eq_of_mem_left, map_sub, map_sub]
  have heq : V.orthogonalProjectionOnto (Z (relativeProjection V Z hl hlo x)) =
      V.orthogonalProjectionOnto (Z x) :=
    (gramEquiv V Z hl hlo).apply_symm_apply _
  rw [heq, sub_self, inner_zero_right]

end Projection

#print axioms relativeProjection
#print axioms relativeProjection_fix
#print axioms relativeProjection_orthogonal

end D5.S3.Quantum.Recovery.BKMActualMetricHeat

namespace D5.S3.Quantum.Recovery.BKMActualMetricHeat

open D5.S3.Quantum.Recovery.BKMActualMetricCoordinates
open D5.S3.HilbertOperators.TwoStepDefectComparison
open D5.S3.Observer.BlockStructure.FourBlockDecomposition

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "M" => Matrix n n ℂ
local notation "E" => EuclideanSpace ℂ (n × n)

/-- The image of the same physical visible subspace in the reference metric. -/
def visibleCoordinates (b : M) (hb : b.PosDef) (B : Submodule ℂ M) : Submodule ℂ E :=
  B.map (metricCoordinates b hb).toLinearEquiv.toLinearMap

/-- The reference coordinates of the genuine projection for the changed BKM form. -/
def changedProjection {a b : M} (ha : a.PosDef) (hb : b.PosDef)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hlo : l • b ≤ a) (hhi : a ≤ u • b)
    (B : Submodule ℂ M) : E →L[ℂ] visibleCoordinates b hb B :=
  relativeProjection (visibleCoordinates b hb B) (relativeOperator a b) hl
    (relativeOperator_bounds ha hb hl hlu hlo hhi).1

/-- The transported projection satisfies the physical BKM orthogonality equation. -/
theorem changedProjection_bkm_orthogonal {a b : M} (ha : a.PosDef) (hb : b.PosDef)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hlo : l • b ≤ a) (hhi : a ≤ u • b)
    (B : Submodule ℂ M) (X Y : M) (hY : Y ∈ B) :
    let e := metricCoordinates b hb
    let R := changedProjection ha hb hl hlu hlo hhi B
    bkmInner a Y (X - e.symm (R (e X) : E)) = 0 := by
  dsimp only
  rw [← relativeOperator_inner a b ha hb, map_sub, ContinuousLinearEquiv.apply_symm_apply]
  exact relativeProjection_orthogonal _ _ hl (relativeOperator_bounds ha hb hl hlu hlo hhi).1
    _ _ (Submodule.mem_map.mpr ⟨Y, hY, rfl⟩)

/-- One physical generator, transported once to the reference Euclidean space. -/
def referenceGenerator (b : M) (hb : b.PosDef) (L : M →L[ℂ] M) : E →L[ℂ] E :=
  (metricCoordinates b hb).conjContinuousAlgEquiv L

private theorem exp_double_time {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (L : H →L[ℂ] H) (t : ℝ) :
    NormedSpace.exp (((2 * t : ℝ) : ℂ) • L) =
      NormedSpace.exp ((t : ℂ) • L) * NormedSpace.exp ((t : ℂ) • L) := by
  let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
  rw [two_mul, Complex.ofReal_add, add_smul, NormedSpace.exp_add_of_commute (Commute.refl _)]

/-- Both defects use the very same heat operator and time doubling. -/
theorem bkm_heat_defect_comparison {a b : M} (ha : a.PosDef) (hb : b.PosDef)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hlo : l • b ≤ a) (hhi : a ≤ u • b)
    (B : Submodule ℂ M) (L : M →L[ℂ] M) (t : ℝ) (center : ℂ) :
    let V := visibleCoordinates b hb B
    let R := changedProjection ha hb hl hlu hlo hhi B
    let P := V.orthogonalProjectionOnto
    let T := NormedSpace.exp ((t : ℂ) • referenceGenerator b hb L)
    let T₂ := NormedSpace.exp (((2 * t : ℝ) : ℂ) • referenceGenerator b hb L)
    let K := R.comp Vᗮ.subtypeL
    let C := visibleResidualLeakage V T
    let W := residualInternalBlock V T
    let ER := R.comp (T.comp V.subtypeL)
    let EP := P.comp (T.comp V.subtypeL)
    let D := (R.comp (T₂.comp V.subtypeL) - ER ^ 2) -
      (P.comp (T₂.comp V.subtypeL) - EP ^ 2)
    D = (K.comp W - ER.comp K).comp C ∧
      ‖D‖ ≤ ((u - l) / (2 * Real.sqrt (u * l))) *
        (‖W - center • 1‖ + ‖ER - center • 1‖) * ‖C‖ := by
  let V := visibleCoordinates b hb B
  let R := changedProjection ha hb hl hlu hlo hhi B
  let A := relativeOperator a b
  let Lb := referenceGenerator b hb L
  obtain ⟨hAlo, hAhi⟩ := relativeOperator_bounds ha hb hl hlu hlo hhi
  have hFix : ∀ v : V, R v = v := relativeProjection_fix V A hl hAlo
  have hOrth : ∀ x v, v ∈ V → ⟪v, A (x - (R x : E))⟫_ℂ = 0 :=
    relativeProjection_orthogonal V A hl hAlo
  have hBlock (T : E →L[ℂ] E) :
      visibleInternalBlock V T = V.orthogonalProjectionOnto.comp (T.comp V.subtypeL) := by
    ext x
    simp [visibleInternalBlock, comp_apply]
  have hExp := exponential_defect_sub_eq V R hFix Lb t
  dsimp only at hExp ⊢
  rw [hBlock] at hExp
  refine ⟨hExp, ?_⟩
  change ‖(R.comp ((NormedSpace.exp (((2 * t : ℝ) : ℂ) • Lb)).comp V.subtypeL) -
      (R.comp ((NormedSpace.exp ((t : ℂ) • Lb)).comp V.subtypeL)) ^ 2) - _‖ ≤ _
  have hDouble := exp_double_time Lb t
  rw [hDouble]
  exact norm_defect_sub_le_relative V A R (relativeOperator_selfAdjoint a b ha).isSymmetric
    hl hlu hAlo hAhi hFix hOrth (NormedSpace.exp ((t : ℂ) • Lb)) center

#print axioms visibleCoordinates
#print axioms changedProjection
#print axioms changedProjection_bkm_orthogonal
#print axioms referenceGenerator
#print axioms bkm_heat_defect_comparison

end D5.S3.Quantum.Recovery.BKMActualMetricHeat
