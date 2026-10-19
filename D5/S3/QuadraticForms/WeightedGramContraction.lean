/- GID: D5/S3/QuadraticForms/WeightedGramContraction
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/WeightedGramContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted dual saturation is equivalent to normalized Gram equality. -/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic

/-!
The geometric part of Kopel's v2 Lemma 4. This file proves the common-contraction
criterion, including dependent and repeated vectors in different real spaces.
It does not identify the optimized pairing with the matrix nuclear norm.

Admission: escape-witness. The substantive construction descends a map of finite
linear combinations through its kernel and extends the resulting span isometry
by orthogonal projection. The forward direction uses both polarization signs.
The public conclusion is content; each private helper is consumed by it.
No computational instance, enumeration, or numerical reduction is used.
-/


public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators InnerProductSpace

namespace D5.S3.QuadraticForms.WeightedGramContraction

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [Fintype ι]

omit [FiniteDimensional ℝ F] in
private theorem inner_eq_of_contraction (Z : F →L[ℝ] E) (hZ : ‖Z‖ ≤ 1)
    (v w : F) (hv : ‖Z v‖ = ‖v‖) (hw : ‖Z w‖ = ‖w‖) :
    ⟪Z v, Z w⟫_ℝ = ⟪v, w⟫_ℝ := by
  have hb (z : F) : ‖Z z‖ ≤ ‖z‖ := by
    calc
      ‖Z z‖ ≤ ‖Z‖ * ‖z‖ := Z.le_opNorm z
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hZ (norm_nonneg _)
      _ = ‖z‖ := one_mul _
  have ha : ‖Z v + Z w‖ ^ 2 ≤ ‖v + w‖ ^ 2 := by
    simpa only [map_add] using pow_le_pow_left₀ (norm_nonneg _) (hb (v + w)) 2
  have hs : ‖Z v - Z w‖ ^ 2 ≤ ‖v - w‖ ^ 2 := by
    simpa only [map_sub] using pow_le_pow_left₀ (norm_nonneg _) (hb (v - w)) 2
  rw [norm_add_sq_real, norm_add_sq_real, hv, hw] at ha
  rw [norm_sub_sq_real, norm_sub_sq_real, hv, hw] at hs
  linarith

omit [Fintype ι] in
private theorem contraction_of_gram [Finite ι] (x : ι → E) (y : ι → F)
    (hg : ∀ j k, ⟪x j, x k⟫_ℝ = ⟪y j, y k⟫_ℝ) :
    ∃ Z : F →L[ℝ] E, ‖Z‖ ≤ 1 ∧ ∀ k, Z (y k) = x k := by
  classical
  letI := Fintype.ofFinite ι
  let X := Fintype.linearCombination ℝ x
  let Y := Fintype.linearCombination ℝ y
  have hn (a : ι → ℝ) : ‖X a‖ = ‖Y a‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [X, Y, Fintype.linearCombination_apply, sum_inner, inner_sum,
      real_inner_smul_left, real_inner_smul_right, hg]
  have hk : LinearMap.ker Y.rangeRestrict ≤ LinearMap.ker X := by
    intro a ha
    apply LinearMap.mem_ker.mpr
    have hy : Y a = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp ha)
    apply norm_eq_zero.mp
    rw [hn, hy, norm_zero]
  let L : LinearMap.range Y →ₗ[ℝ] E :=
    Y.rangeRestrict.liftOfSurjective Y.surjective_rangeRestrict ⟨X, hk⟩
  have hL (a : ι → ℝ) : L (Y.rangeRestrict a) = X a := by
    exact LinearMap.equivOfSurjective_apply _ _
  let I : LinearMap.range Y →ₗᵢ[ℝ] E :=
    { toLinearMap := L
      norm_map' := by
        intro z
        obtain ⟨a, rfl⟩ := Y.surjective_rangeRestrict z
        change ‖L (Y.rangeRestrict a)‖ = ‖Y a‖
        rw [hL]
        exact hn a }
  let Z : F →L[ℝ] E :=
    I.toContinuousLinearMap.comp (LinearMap.range Y).orthogonalProjectionOnto
  refine ⟨Z, ?_, ?_⟩
  · apply Z.opNorm_le_bound (by norm_num : (0 : ℝ) ≤ 1)
    intro z
    change ‖I ((LinearMap.range Y).orthogonalProjectionOnto z)‖ ≤ 1 * ‖z‖
    rw [I.norm_map, one_mul]
    exact (LinearMap.range Y).norm_orthogonalProjectionOnto_apply_le z
  · intro k
    have hy : y k ∈ LinearMap.range Y := by
      refine ⟨Pi.single k 1, ?_⟩
      simp [Y]
    have hy' : (⟨y k, hy⟩ : LinearMap.range Y) = Y.rangeRestrict (Pi.single k 1) := by
      apply Subtype.ext
      simp [Y]
    change I ((LinearMap.range Y).orthogonalProjectionOnto (⟨y k, hy⟩ : LinearMap.range Y)) = x k
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    change L ⟨y k, hy⟩ = x k
    rw [hy', hL]
    simp [X]

omit [Fintype ι] in
private theorem unit_contraction_iff_gram [Finite ι] (x : ι → E) (y : ι → F)
    (hx : ∀ k, ‖x k‖ = 1) (hy : ∀ k, ‖y k‖ = 1) :
    (∃ Z : F →L[ℝ] E, ‖Z‖ ≤ 1 ∧ ∀ k, Z (y k) = x k) ↔
      ∀ j k, ⟪x j, x k⟫_ℝ = ⟪y j, y k⟫_ℝ := by
  constructor
  · rintro ⟨Z, hZ, hmap⟩ j k
    simpa only [hmap] using inner_eq_of_contraction Z hZ (y j) (y k)
      (by rw [hmap, hx, hy]) (by rw [hmap, hx, hy])
  · exact contraction_of_gram x y

/-- Positive weighted saturation by one contraction is equivalent to equality
of the normalized Gram matrices. No independence or distinctness is assumed.
The source space is finite dimensional; the target may be any real inner
product space. This is the geometric dual-witness step of v2 Lemma 4. -/
theorem weighted_dual_saturation_iff_normalized_gram
    (x : ι → E) (y : ι → F) (u : ι → ℝ)
    (hx : ∀ k, x k ≠ 0) (hy : ∀ k, y k ≠ 0) (hu : ∀ k, 0 < u k) :
    (∃ Z : F →L[ℝ] E, ‖Z‖ ≤ 1 ∧
      (∑ k, u k * ⟪x k, Z (y k)⟫_ℝ) = ∑ k, u k * ‖x k‖ * ‖y k‖) ↔
    ∀ j k, ⟪‖x j‖⁻¹ • x j, ‖x k‖⁻¹ • x k⟫_ℝ =
      ⟪‖y j‖⁻¹ • y j, ‖y k‖⁻¹ • y k⟫_ℝ := by
  have hxn (k : ι) : ‖‖x k‖⁻¹ • x k‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hx k))]
  have hyn (k : ι) : ‖‖y k‖⁻¹ • y k‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hy k))]
  rw [← unit_contraction_iff_gram (fun k => ‖x k‖⁻¹ • x k)
    (fun k => ‖y k‖⁻¹ • y k) hxn hyn]
  constructor
  · rintro ⟨Z, hZ, hsum⟩
    have hb (k : ι) : ⟪x k, Z (y k)⟫_ℝ ≤ ‖x k‖ * ‖y k‖ := by
      calc
        _ ≤ ‖x k‖ * ‖Z (y k)‖ := real_inner_le_norm _ _
        _ ≤ ‖x k‖ * (‖Z‖ * ‖y k‖) :=
          mul_le_mul_of_nonneg_left (Z.le_opNorm _) (norm_nonneg _)
        _ ≤ ‖x k‖ * (1 * ‖y k‖) := by gcongr
        _ = _ := by ring
    have he (k : ι) : ⟪x k, Z (y k)⟫_ℝ = ‖x k‖ * ‖y k‖ := by
      have hnon : ∀ i ∈ Finset.univ, 0 ≤ u i * (‖x i‖ * ‖y i‖ - ⟪x i, Z (y i)⟫_ℝ) :=
        fun i _ => mul_nonneg (le_of_lt (hu i)) (sub_nonneg.mpr (hb i))
      have hz : (∑ i, u i * (‖x i‖ * ‖y i‖ - ⟪x i, Z (y i)⟫_ℝ)) = 0 := by
        simp_rw [mul_sub, ← mul_assoc]
        rw [Finset.sum_sub_distrib, hsum, sub_self]
      have hi := (Finset.sum_eq_zero_iff_of_nonneg hnon).mp hz k (Finset.mem_univ k)
      exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (ne_of_gt (hu k))) |>.symm
    refine ⟨Z, hZ, fun k => ?_⟩
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ)
    · calc
        ‖Z (‖y k‖⁻¹ • y k)‖ ≤ ‖Z‖ * ‖‖y k‖⁻¹ • y k‖ := Z.le_opNorm _
        _ ≤ 1 := by rw [hyn, mul_one]; exact hZ
        _ = ‖‖x k‖⁻¹ • x k‖ := (hxn k).symm
    · simp only [RCLike.re_to_real, map_smul, real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_comm, he, hxn]
      field_simp [norm_ne_zero_iff.mpr (hx k), norm_ne_zero_iff.mpr (hy k)]
  · rintro ⟨Z, hZ, hmap⟩
    refine ⟨Z, hZ, Finset.sum_congr rfl (fun k _ => ?_)⟩
    have hm : Z (y k) = (‖y k‖ / ‖x k‖) • x k := by
      have h := congrArg (fun v : E => ‖y k‖ • v) (hmap k)
      simpa [map_smul, smul_smul, norm_ne_zero_iff.mpr (hy k), div_eq_mul_inv] using h
    rw [hm, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [norm_ne_zero_iff.mpr (hx k), norm_ne_zero_iff.mpr (hy k)]

end D5.S3.QuadraticForms.WeightedGramContraction
