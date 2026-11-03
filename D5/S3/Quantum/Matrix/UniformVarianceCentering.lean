/- GID: D5/S3/Quantum/Matrix/UniformVarianceCentering
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/UniformVarianceCentering
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform vector variances control simultaneous means and ambient centered energy. -/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix.Hermitian

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace D5.S3.Quantum.Matrix.UniformVarianceCentering

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Scalar expectation in a real Hilbert space. -/
def mean (T : E →ₗ[ℝ] E) (x : E) : ℝ := ⟪x, T x⟫_ℝ

private lemma extrema (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (e : E) (he : ‖e‖ = 1) :
    ∃ a b : E, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧
      T a = mean T a • a ∧ T b = mean T b • b ∧
      (∀ x : E, ‖x‖ = 1 → mean T a ≤ mean T x) ∧
      (∀ x : E, ‖x‖ = 1 → mean T x ≤ mean T b) := by
  let A := T.toContinuousLinearMap
  have hc : Continuous (mean T) := by unfold mean; fun_prop
  have hs : (Metric.sphere (0 : E) 1).Nonempty := ⟨e, by simpa using he⟩
  obtain ⟨a, ha, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hs hc.continuousOn
  obtain ⟨b, hb, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hs hc.continuousOn
  have ha1 : ‖a‖ = 1 := by simpa using ha
  have hb1 : ‖b‖ = 1 := by simpa using hb
  have hsa : IsSelfAdjoint A := hT.toSelfAdjoint.prop
  have ha' : IsLocalExtrOn A.reApplyInnerSelf (Metric.sphere (0 : E) ‖a‖) a := by
    rw [ha1]
    simpa only [ContinuousLinearMap.reApplyInnerSelf, A, mean, real_inner_comm] using
      (Or.inl hmin.isLocalMinOn : IsLocalExtrOn (mean T) (Metric.sphere 0 1) a)
  have hb' : IsLocalExtrOn A.reApplyInnerSelf (Metric.sphere (0 : E) ‖b‖) b := by
    rw [hb1]
    simpa only [ContinuousLinearMap.reApplyInnerSelf, A, mean, real_inner_comm] using
      (Or.inr hmax.isLocalMaxOn : IsLocalExtrOn (mean T) (Metric.sphere 0 1) b)
  refine ⟨a, b, ha1, hb1, ?_, ?_, ?_, ?_⟩
  · simpa [ContinuousLinearMap.rayleighQuotient, A, mean, ha1, real_inner_comm] using
      hsa.eq_smul_self_of_isLocalExtrOn_real ha'
  · simpa [ContinuousLinearMap.rayleighQuotient, A, mean, hb1, real_inner_comm] using
      hsa.eq_smul_self_of_isLocalExtrOn_real hb'
  · intro x hx; exact hmin (by simpa using hx)
  · intro x hx; exact hmax (by simpa using hx)

/-- A uniform variance bound bounds every difference of unit-vector expectations. -/
theorem expectation_gap_sq_le_four_variance (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hv : ∀ x : E, ‖x‖ = 1 → ‖T x - mean T x • x‖ ^ 2 ≤ δ)
    (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (mean T x - mean T y) ^ 2 ≤ 4 * δ := by
  obtain ⟨a,b,ha,hb,hTa,hTb,hmin,hmax⟩ := extrema T hT x hx
  let l := mean T a
  let u := mean T b
  have hlu : l ≤ u := hmin b hb
  have hwidth : (u-l)^2 ≤ 4*δ := by
    by_cases heq : l = u
    · simp [heq, hδ]
    have hab : ⟪a,b⟫_ℝ = 0 := by
      have hs := hT a b
      rw [hTa,hTb,real_inner_smul_left,real_inner_smul_right] at hs
      change l * ⟪a,b⟫_ℝ = u * ⟪a,b⟫_ℝ at hs
      exact (mul_eq_mul_right_iff.mp hs).resolve_left heq
    let t : ℝ := (Real.sqrt 2)⁻¹
    have ht : t^2 = 1/2 := by dsimp [t]; rw [inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
    let z := t • (a+b)
    have hz2 : ‖z‖^2 = 1 := by
      simp only [z, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        norm_add_sq_real, ha, hb, hab]
      nlinarith [ht]
    have hz : ‖z‖ = 1 := by nlinarith [norm_nonneg z]
    have hm : mean T z = (l+u)/2 := by
      simp only [mean,z,map_smul,map_add,hTa,hTb,real_inner_smul_left,
        real_inner_smul_right,inner_add_left,inner_add_right,
        inner_self_eq_norm_sq_to_K,ha,hb,hab,real_inner_comm b a]
      change t * (t * (l * 1^2 + u * 0 + (l * 0 + u * 1^2))) = _
      nlinarith [ht]
    have he : ‖T z - mean T z • z‖^2 = (u-l)^2/4 := by
      have hevec : T z - mean T z • z =
          (t*(l-(l+u)/2)) • a + (t*(u-(l+u)/2)) • b := by
        simp only [z,map_smul,map_add,hTa,hTb,hm,smul_add,smul_smul]
        module
      rw [hevec,norm_add_sq_real,norm_smul,norm_smul,
        real_inner_smul_left,real_inner_smul_right,hab,ha,hb]
      simp only [mul_pow,Real.norm_eq_abs,sq_abs]
      nlinarith [ht]
    have hh := hv z hz
    rw [he] at hh
    linarith
  have hxlo := hmin x hx
  have hxhi := hmax x hx
  have hylo := hmin y hy
  have hyhi := hmax y hy
  have hp : (u-l-(mean T x-mean T y)) * (u-l+(mean T x-mean T y)) ≥ 0 :=
    mul_nonneg (by dsimp [u,l]; linarith) (by dsimp [u,l]; linarith)
  nlinarith

end D5.S3.Quantum.Matrix.UniformVarianceCentering
