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

/-! Uniform variance bounds, simultaneous expectations, and ambient residuals. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace D5.S3.Quantum.Matrix.UniformVarianceCentering

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Scalar expectation in a real Hilbert space. -/
def mean (T : E →ₗ[ℝ] E) (x : E) : ℝ := ⟪x, T x⟫

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
    simpa only [ContinuousLinearMap.reApplyInnerSelf_apply, A, mean, real_inner_comm] using
      (Or.inl hmin.isLocalMinOn : IsLocalExtrOn (mean T) (Metric.sphere 0 1) a)
  have hb' : IsLocalExtrOn A.reApplyInnerSelf (Metric.sphere (0 : E) ‖b‖) b := by
    rw [hb1]
    simpa only [ContinuousLinearMap.reApplyInnerSelf_apply, A, mean, real_inner_comm] using
      (Or.inr hmax.isLocalMaxOn : IsLocalExtrOn (mean T) (Metric.sphere 0 1) b)
  refine ⟨a, b, ha1, hb1, ?_, ?_, ?_, ?_⟩
  · simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply, A, mean, ha1, real_inner_comm] using
      hsa.eq_smul_self_of_isLocalExtrOn_real ha'
  · simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply, A, mean, hb1, real_inner_comm] using
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
    have hab : ⟪a,b⟫ = 0 := by
      have hs := hT a b
      rw [hTa,hTb,real_inner_smul_left,real_inner_smul_right] at hs
      change l * ⟪a,b⟫ = u * ⟪a,b⟫ at hs
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


private lemma weighted_sum_sq_le {J : Type*} [Fintype J]
    (c : J → ℝ) (v : J → F) :
    ‖∑ j, c j • v j‖ ^ 2 ≤ (∑ j, c j ^ 2) * ∑ j, ‖v j‖ ^ 2 := by
  have hn : ‖∑ j, c j • v j‖ ≤ ∑ j, |c j| * ‖v j‖ := by
    simpa only [norm_smul, Real.norm_eq_abs] using norm_sum_le Finset.univ (fun j => c j • v j)
  calc
    _ ≤ (∑ j, |c j| * ‖v j‖)^2 := by
      exact sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun j _ => by positivity)) |>.mpr hn
    _ ≤ (∑ j, c j ^ 2) * ∑ j, ‖v j‖ ^ 2 := by
      simpa only [sq_abs] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun j => |c j|) (fun j => ‖v j‖)

variable [FiniteDimensional ℝ F]

private lemma adjoint_isometry_norm_le (V : E →ₗᵢ[ℝ] F) (z : F) :
    ‖V.adjoint z‖ ≤ ‖z‖ := by
  have hp : ‖V.adjoint z‖^2 = ⟪V (V.adjoint z), z⟫ := by
    rw [← LinearMap.adjoint_inner_right]
    exact (real_inner_self_eq_norm_sq _).symm
  have hb := real_inner_le_norm (V (V.adjoint z)) z
  rw [V.norm_map] at hb
  by_cases hz : ‖V.adjoint z‖ = 0
  · rw [hz]; exact norm_nonneg _
  · nlinarith [norm_nonneg (V.adjoint z)]

/-- All unit vectors in the block are tested, and residuals remain in the ambient space. -/
theorem uniform_block_centering {J : Type*} [Fintype J]
    (V : E →ₗᵢ[ℝ] F) (H : J → E →ₗ[ℝ] F)
    (hs : ∀ j, (V.adjoint.comp (H j)).IsSymmetric)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hv : ∀ x : E, ‖x‖ = 1 →
      ∑ j, ‖H j x - ⟪V x,H j x⟫ • V x‖^2 ≤ δ)
    (e : E) (he : ‖e‖ = 1) (x : E) (hx : ‖x‖ = 1) :
    (∑ j, (⟪V x,H j x⟫ - ⟪V e,H j e⟫)^2 ≤ 4*δ) ∧
    (∑ j, ‖H j x - ⟪V e,H j e⟫ • V x‖^2 ≤ 5*δ) := by
  classical
  let S : J → E →ₗ[ℝ] E := fun j => V.adjoint.comp (H j)
  have hm (j : J) (z : E) : mean (S j) z = ⟪V z,H j z⟫ := by
    exact LinearMap.adjoint_inner_right V.toLinearMap z (H j z)
  let c : J → ℝ := fun j => mean (S j) x - mean (S j) e
  let q : ℝ := ∑ j, c j^2
  have hq : 0 ≤ q := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  let T : E →ₗ[ℝ] E := ∑ j, c j • S j
  have hT : T.IsSymmetric := LinearMap.isSymmetric_sum _ (fun j _ =>
    (hs j).smul (by simp))
  have hmT (z : E) : mean T z = ∑ j, c j * mean (S j) z := by
    simp [mean,T,LinearMap.sum_apply,inner_sum,real_inner_smul_right]
  have hadj (z : E) : V.adjoint (V z) = z := by
    exact DFunLike.congr_fun V.adjoint_comp_self' z
  have hvar (z : E) (hz : ‖z‖ = 1) : ‖T z - mean T z • z‖^2 ≤ q*δ := by
    let r : J → F := fun j => H j z - mean (S j) z • V z
    have heq : T z - mean T z • z = V.adjoint (∑ j, c j • r j) := by
      simp only [r,map_sum,map_smul,map_sub,hadj,T,LinearMap.sum_apply,
        LinearMap.smul_apply,S,LinearMap.comp_apply,hmT,
        ← Finset.sum_smul,smul_sub,smul_smul,Finset.sum_sub_distrib]
    rw [heq]
    calc
      _ ≤ ‖∑ j, c j • r j‖^2 :=
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (adjoint_isometry_norm_le V _)
      _ ≤ q * ∑ j, ‖r j‖^2 := weighted_sum_sq_le c r
      _ ≤ q*δ := mul_le_mul_of_nonneg_left (by simpa only [r,hm] using hv z hz) hq
  have hdiff : mean T x - mean T e = q := by
    rw [hmT,hmT,← Finset.sum_sub_distrib]
    simp only [q,c,pow_two,mul_sub]
  have hgap := expectation_gap_sq_le_four_variance T hT (q*δ) (mul_nonneg hq hδ)
    hvar x e hx he
  rw [hdiff] at hgap
  have hqbound : q ≤ 4*δ := by
    by_cases hz : q = 0
    · rw [hz]; positivity
    · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
      nlinarith
  have hmeans : ∑ j, (⟪V x,H j x⟫ - ⟪V e,H j e⟫)^2 ≤ 4*δ := by
    simpa only [q,c,hm] using hqbound
  refine ⟨hmeans, ?_⟩
  have hsplit (j : J) :
      ‖H j x - ⟪V e,H j e⟫ • V x‖^2 =
      ‖H j x - ⟪V x,H j x⟫ • V x‖^2 +
        (⟪V x,H j x⟫ - ⟪V e,H j e⟫)^2 := by
    rw [norm_sub_sq_real,norm_sub_sq_real]
    simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,V.norm_map,hx,
      real_inner_smul_right,real_inner_comm (H j x) (V x)]
    ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  linarith [hv x hx]

end D5.S3.Quantum.Matrix.UniformVarianceCentering
