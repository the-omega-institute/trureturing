/- GID: D5/S3/Analytic/MultivariateEnergy/Moments
   generality: G
   mirror-B: D5/B/S3/Analytic/MultivariateEnergy/Moments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Function.LocallyIntegrable, mathlib/module/Mathlib.MeasureTheory.SpecificCodomains.Pi, mathlib/module/Mathlib.MeasureTheory.Constructions.Polish.Basic]
   utility: none
   digest: Orthogonal invariance and centered second moments of normalized surface measure. -/

import D5.S3.Analytic.MultivariateEnergy.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Spherical orthogonal invariance and quadratic moments. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Matrix.Norms.Elementwise Pointwise

namespace D5.S3.Analytic.MultivariateEnergy.Moments
open Defs

local instance (d : ℕ) : ContinuousENorm (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (ContinuousENorm (Fin d → Fin d → ℝ))

private lemma continuous_sphereAction {d : ℕ}
    (V : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Continuous (sphereAction V) :=
  (V.continuous.comp continuous_subtype_val).subtype_mk _

private lemma cone_preimage {d : ℕ}
    (V : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (s : Set (S d)) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereAction V ⁻¹' s)) =
      V ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨r, hr, V z, ⟨sphereAction V z, hz, rfl⟩, by simp⟩
  · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, he⟩
    refine ⟨r, hr, V.symm z, ⟨sphereAction V.symm z, ?_, rfl⟩, ?_⟩
    · simpa only [mem_preimage, sphereAction, V.apply_symm_apply] using hz
    · apply V.injective
      simpa using he

/-- Every orthogonal transformation preserves normalized surface measure. -/
theorem measurePreserving_sphereAction {d : ℕ}
    (V : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    MeasurePreserving (sphereAction V) (sigma d) (sigma d) := by
  have hm := (continuous_sphereAction V).measurable
  refine ⟨hm, ?_⟩
  unfold sigma
  rw [Measure.map_smul _ hm.aemeasurable]
  congr 1
  ext s hs
  rw [Measure.map_apply hm hs, Measure.toSphere_apply' _ (hm hs),
    Measure.toSphere_apply' _ hs, cone_preimage]
  rw [V.measurePreserving.measure_preimage_emb V.toHomeomorph.measurableEmbedding]


private lemma sphereAction_embedding {d : ℕ}
    (V : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    MeasurableEmbedding (sphereAction V) :=
  (continuous_sphereAction V).measurableEmbedding (by
    intro x y h
    apply Subtype.ext
    exact V.injective (congrArg Subtype.val h))

private lemma continuous_coord {d : ℕ} (i : Fin d) :
    Continuous (fun x : S d => (x : EuclideanSpace ℝ (Fin d)) i) :=
  (PiLp.continuous_apply 2 _ i).comp continuous_subtype_val

private lemma integral_off_diagonal {d : ℕ} (i j : Fin d) (hij : i ≠ j) :
    (∫ x : S d, (x : EuclideanSpace ℝ (Fin d)) i * x.val j ∂sigma d) = 0 := by
  let V : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
    LinearIsometryEquiv.piLpCongrRight 2 (fun k : Fin d =>
      if k = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)
  have h := (measurePreserving_sphereAction V).integral_comp (sphereAction_embedding V)
    (fun x : S d => (x : EuclideanSpace ℝ (Fin d)) i * x.val j)
  have he : (fun x : S d => (sphereAction V x).val i * (sphereAction V x).val j) =
      (fun x : S d => -((x : EuclideanSpace ℝ (Fin d)) i * x.val j)) := by
    funext x
    simp [sphereAction, V, hij, hij.symm]
  rw [he, integral_neg] at h
  linarith

private lemma integral_diagonal_eq {d : ℕ} (i j : Fin d) :
    (∫ x : S d, (x : EuclideanSpace ℝ (Fin d)) i * x.val i ∂sigma d) =
      ∫ x : S d, (x : EuclideanSpace ℝ (Fin d)) j * x.val j ∂sigma d := by
  let V := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have h := (measurePreserving_sphereAction V).integral_comp (sphereAction_embedding V)
    (fun x : S d => (x : EuclideanSpace ℝ (Fin d)) i * x.val i)
  simpa [sphereAction, V, Equiv.piCongrLeft'] using h.symm


/-- The centered rank-one feature is continuous. -/
theorem continuous_A (d : ℕ) : Continuous (A (d := d)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((continuous_coord i).mul (continuous_coord j)).sub continuous_const

/-- The feature is integrable against every finite Borel measure on the sphere. -/
theorem integrable_A {d : ℕ} (μ : Measure (S d)) [IsFiniteMeasure μ] :
    Integrable (A (d := d)) μ :=
by
  change Integrable (fun x : S d => (fun i j => A x i j)) μ
  apply Integrable.of_eval
  intro i
  apply Integrable.of_eval
  intro j
  have hc : Continuous (fun x : S d => A x i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_A d))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Normalized surface measure has covariance equal to the identity divided by dimension. -/
theorem integral_coord_mul_coord (d : ℕ) [NeZero d] (i j : Fin d) :
    (∫ x : S d, (x : EuclideanSpace ℝ (Fin d)) i * x.val j ∂sigma d) =
      if i = j then 1 / (d : ℝ) else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    have hint (k : Fin d) : Integrable (fun x : S d => x.val k * x.val k) (sigma d) :=
      ((continuous_coord k).mul (continuous_coord k)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hn (x : S d) : (∑ k : Fin d, x.val k * x.val k) = 1 := by
      simp_rw [← sq]
      rw [← EuclideanSpace.real_norm_sq_eq]
      have hx : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
      rw [hx, one_pow]
    have he : (d : ℝ) * (∫ x : S d, x.val i * x.val i ∂sigma d) = 1 := by
      calc
        _ = ∑ k : Fin d, ∫ x : S d, x.val k * x.val k ∂sigma d := by
          simp_rw [← integral_diagonal_eq i]
          simp
        _ = ∫ x : S d, ∑ k : Fin d, x.val k * x.val k ∂sigma d :=
          (integral_finsetSum _ (fun k _ => hint k)).symm
        _ = 1 := by simp_rw [hn]; simp
    apply (eq_div_iff (Nat.cast_ne_zero.mpr (NeZero.ne d))).mpr
    linarith
  · rw [if_neg hij]
    exact integral_off_diagonal i j hij

/-- The centered matrix feature has zero surface average. -/
theorem integral_A_eq_zero (d : ℕ) [NeZero d] :
    (∫ x : S d, A x ∂sigma d) = 0 := by
  change (∫ x : S d, (fun i j => A x i j) ∂sigma d) = (fun _ _ => 0)
  ext i j
  rw [eval_integral (fun k => (integrable_A (sigma d)).eval k),
    eval_integral (fun k => ((integrable_A (sigma d)).eval i).eval k)]
  change (∫ x : S d, x.val i * x.val j - (if i = j then 1 / (d : ℝ) else 0)
    ∂sigma d) = 0
  have hint : Integrable (fun x : S d => x.val i * x.val j) (sigma d) :=
    ((continuous_coord i).mul (continuous_coord j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_sub hint (integrable_const _), integral_coord_mul_coord]
  simp


private lemma A_eq {d : ℕ} (x : S d) :
    A x = Matrix.vecMulVec (fun i => x.val i) (fun i => x.val i) -
      (1 / (d : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  ext i j
  simp only [A, Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

private lemma dot_self {d : ℕ} (x : S d) :
    dotProduct (fun i => x.val i) (fun i => x.val i) = 1 := by
  have hx : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  simpa only [dotProduct, ← sq, ← EuclideanSpace.real_norm_sq_eq, hx, one_pow]

/-- The pair trace is the squared Euclidean inner product minus the reciprocal dimension. -/
theorem L_eq {d : ℕ} [NeZero d] (x y : S d) :
    L x y = (inner ℝ x.val y.val) ^ 2 - 1 / (d : ℝ) := by
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  simp only [L, A_eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.vecMulVec_smul, Matrix.trace_vecMulVec, dot_self, smul_eq_mul]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Pi.star_apply, star_trivial]
  rw [dotProduct_comm (fun i => x.val i) (fun i => y.val i)]
  field_simp [hd]
  <;> ring

/-- The cubic trace is a polynomial in the three pairwise Euclidean inner products. -/
theorem T_eq {d : ℕ} [NeZero d] (x y z : S d) :
    T x y z = inner ℝ x.val y.val * inner ℝ y.val z.val * inner ℝ z.val x.val -
      ((inner ℝ x.val y.val)^2 + (inner ℝ y.val z.val)^2 +
        (inner ℝ z.val x.val)^2) / (d : ℝ) + 2 / (d : ℝ)^2 := by
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  simp only [T, A_eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.vecMulVec_smul, Matrix.trace_vecMulVec, dot_self, smul_smul]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Pi.star_apply, star_trivial]
  simp only [dotProduct_smul, smul_eq_mul]
  simp only [dotProduct_comm (fun i => y.val i) (fun i => x.val i),
    dotProduct_comm (fun i => z.val i) (fun i => y.val i),
    dotProduct_comm (fun i => z.val i) (fun i => x.val i)]
  field_simp [hd]
  <;> ring

/-- Every three-input family member is continuous, symmetric and orthogonally invariant. -/
theorem isAdmissible_familyKernel_three (d : ℕ) [NeZero d] (β : ℝ) :
    IsAdmissible (familyKernel d β) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold familyKernel
    simp only [L_eq, T_eq]
    fun_prop
  · intro π x
    simp only [familyKernel, L_eq, T_eq, Function.comp_apply]
    have h01 : π 0 ≠ π 1 := π.injective.ne (by decide)
    have h02 : π 0 ≠ π 2 := π.injective.ne (by decide)
    have h12 : π 1 ≠ π 2 := π.injective.ne (by decide)
    generalize h0 : π 0 = a at *
    generalize h1 : π 1 = b at *
    generalize h2 : π 2 = c at *
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      simp_all <;>
      simp only [real_inner_comm (x 1).val (x 0).val,
        real_inner_comm (x 2).val (x 0).val, real_inner_comm (x 2).val (x 1).val] <;> ring
  · intro V x
    simp only [familyKernel, L_eq, T_eq, sphereAction, V.inner_map_map]

end D5.S3.Analytic.MultivariateEnergy.Moments
