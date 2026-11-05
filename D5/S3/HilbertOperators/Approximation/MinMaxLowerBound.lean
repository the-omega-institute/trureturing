/- GID: D5/S3/HilbertOperators/Approximation/MinMaxLowerBound
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/Approximation/MinMaxLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict-threshold min-max lower bounds for bounded complex Hilbert operators. -/

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the accompanying LICENSE.
Authors (ApproximationNumber/Basic): Jon Crall, OpenAI GPT-5.6 Thinking,
  Niels Voss, Arnav Mehta, Rawad Kansoh.
Authors (OperatorModulus): Jon Crall, Claude Fable 5, OpenAI GPT-5.6 Thinking.
Authors (Spectral/Cutoff and ApproximationNumber/MinMaxUpper): Jon Crall, Claude Opus 5.

Adapted from https://github.com/AIQ-Kitware/aiq-dkps-formalization,
revision 8924c4cc743d2f193bb4f39bee800790698a681b, the four modules named above.
Changes by OpenAI Codex: declaration slicing, native namespace and private support,
complex specialization using Mathlib CFC, and direct Mathlib independent-family extraction.
The Basic source credits Mathlib PR #32126 and Davis--Kahan revision
fc38eb48b9b49f2e1d87fe0c7022dc5e262820a7. OperatorModulus credits
DavisKahan/OperatorIdeal/ApproximationNumbers/OperatorModulus.lean and
ForMathlib/Analysis/InnerProductSpace/OperatorAbsoluteValue.lean at fc38eb4.
The supplier attributes the cutoff and min-max proof to its CFC development;
the statement was also used by its Spectra bridge, whose PVM proof is not used here.
Retirement: replace this slice by direct imports when this repository's pinned
Mathlib contains equivalent declarations with these full hypotheses.
-/

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity

namespace D5.S3.HilbertOperators.Approximation.MinMaxLowerBound

open ContinuousLinearMap
open scoped InnerProductSpace
noncomputable section
universe u v
variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


omit [CompleteSpace E] [CompleteSpace F] in
theorem errors_bdd_below (T : E →L[ℂ] F) (n : ℕ) :
    BddBelow (Set.range fun R : {R : E →L[ℂ] F // R.rank ≤ (n : Cardinal)} =>
      ‖T - R.1‖) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨R, rfl⟩
  exact norm_nonneg _

/-- Zero-based infimum of operator-norm errors over bounded maps of rank at most `n`. -/
noncomputable def approximation_number (T : E →L[ℂ] F) (n : ℕ) : ℝ :=
  ⨅ R : {R : E →L[ℂ] F // R.rank ≤ (n : Cardinal)}, ‖T - R.1‖

omit [CompleteSpace E] [CompleteSpace F] in
theorem approximation_number_le_error (T : E →L[ℂ] F) {n : ℕ}
    {R : E →L[ℂ] F} (hR : R.rank ≤ (n : Cardinal)) :
    (approximation_number T) n ≤ ‖T - R‖ :=
  ciInf_le ((errors_bdd_below T) n) ⟨R, hR⟩

private theorem gram_nonneg (T : E →L[ℂ] F) : 0 ≤ T.adjoint ∘L T :=
  nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self T)

private noncomputable def modulus (T : E →L[ℂ] F) : E →L[ℂ] E :=
  CFC.sqrt (T.adjoint ∘L T)

private theorem modulus_nonneg (T : E →L[ℂ] F) : 0 ≤ (modulus T) :=
  CFC.sqrt_nonneg _

private theorem modulus_is_self_adjoint (T : E →L[ℂ] F) : IsSelfAdjoint (modulus T) :=
  .of_nonneg (modulus_nonneg T)

@[simp]
private theorem adjoint_modulus (T : E →L[ℂ] F) : (modulus T).adjoint = (modulus T) := by
  rw [← star_eq_adjoint]
  exact (modulus_is_self_adjoint T).star_eq

private theorem modulus_mul_self (T : E →L[ℂ] F) :
    (modulus T) * (modulus T) = T.adjoint ∘L T :=
  CFC.sqrt_mul_sqrt_self _ (gram_nonneg T)

@[simp]
private theorem norm_modulus_apply (T : E →L[ℂ] F) (x : E) : ‖(modulus T) x‖ = ‖T x‖ := by
  have hinner : (⟪(modulus T) x, (modulus T) x⟫_ℂ : ℂ) = ⟪T x, T x⟫_ℂ := by
    calc (⟪(modulus T) x, (modulus T) x⟫_ℂ : ℂ)
        = ⟪(modulus T).adjoint x, (modulus T) x⟫_ℂ := by rw [adjoint_modulus]
      _ = ⟪x, (modulus T) ((modulus T) x)⟫_ℂ := adjoint_inner_left _ _ _
      _ = ⟪x, ((modulus T) * (modulus T)) x⟫_ℂ := (rfl)
      _ = ⟪x, (T.adjoint ∘L T) x⟫_ℂ := by rw [modulus_mul_self]
      _ = ⟪T x, T x⟫_ℂ := adjoint_inner_right T x (T x)
  have hsq : ‖(modulus T) x‖ ^ 2 = ‖T x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hinner
    exact_mod_cast hinner
  have hsqrt := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsqrt

private noncomputable def spectral_cutoff (A : E →L[ℂ] E) (s : ℝ) : E →L[ℂ] E :=
  cfc (fun t : ℝ => max (t - s) 0) A

private noncomputable def spectral_cocutoff (A : E →L[ℂ] E) (s : ℝ) : E →L[ℂ] E :=
  cfc (fun t : ℝ => max (s - t) 0) A

private theorem cutoff_split (A : E →L[ℂ] E) (hA : 0 ≤ A) (s : ℝ) :
    (s ^ 2 : ℝ) • (1 : E →L[ℂ] E) + (A + (s : ℝ) • 1) * (spectral_cutoff A) s - A * A
      = cfc (fun t : ℝ => s ^ 2 + (t + s) * max (t - s) 0 - t * t) A := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  simp only [spectral_cutoff,
    cfc_sub (a := A) (fun t : ℝ => s ^ 2 + (t + s) * max (t - s) 0) (fun t : ℝ => t * t),
    cfc_add (a := A) (fun _ : ℝ => s ^ 2) (fun t : ℝ => (t + s) * max (t - s) 0),
    cfc_mul (fun t : ℝ => t + s) (fun t : ℝ => max (t - s) 0) A,
    cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) A,
    cfc_add (a := A) (fun t : ℝ => t) (fun _ : ℝ => s),
    cfc_const (s ^ 2) A, cfc_const s A, cfc_id' ℝ A]
  simp [Algebra.algebraMap_eq_smul_one]

private theorem cocutoff_split (A : E →L[ℂ] E) (hA : 0 ≤ A) (s : ℝ) :
    (spectral_cocutoff A) s - ((s : ℝ) • (1 : E →L[ℂ] E) - A)
      = cfc (fun t : ℝ => max (s - t) 0 - (s - t)) A := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  rw [spectral_cocutoff,
    cfc_sub (a := A) (fun t : ℝ => max (s - t) 0) (fun t : ℝ => s - t),
    cfc_sub (a := A) (fun _ : ℝ => s) (fun t : ℝ => t),
    cfc_const s A, cfc_id' ℝ A]
  simp [Algebra.algebraMap_eq_smul_one]

private theorem cutoff_mul_cocutoff (A : E →L[ℂ] E) (hA : 0 ≤ A) (s : ℝ) :
    (spectral_cutoff A) s * (spectral_cocutoff A) s = 0 := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  rw [spectral_cutoff, spectral_cocutoff,
    ← cfc_mul (fun t : ℝ => max (t - s) 0) (fun t : ℝ => max (s - t) 0) A]
  have hzero : (fun t : ℝ => max (t - s) 0 * max (s - t) 0) = fun _ : ℝ => (0 : ℝ) := by
    funext t
    rcases le_or_gt t s with h | h
    · rw [max_eq_right (by linarith)]; ring
    · rw [max_eq_right (a := s - t) (by linarith)]; ring
  rw [hzero, cfc_const_zero]

private theorem is_self_adjoint_cocutoff (A : E →L[ℂ] E) (hA : 0 ≤ A) (s : ℝ) :
    IsSelfAdjoint ((spectral_cocutoff A) s) := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  exact cfc_predicate _ A

@[simp]
private theorem cutoff_cocutoff_apply (A : E →L[ℂ] E) (hA : 0 ≤ A) (s : ℝ) (x : E) :
    (spectral_cutoff A) s ((spectral_cocutoff A) s x) = 0 := by
  have h := congrArg (fun B : E →L[ℂ] E => B x) (cutoff_mul_cocutoff A hA s)
  simpa [mul_apply_eq_comp] using h

private theorem re_inner_mul_self {A : H →L[ℂ] H} (hsa : IsSelfAdjoint A) (y : H) :
    RCLike.re ⟪(A * A) y, y⟫_ℂ = ‖A y‖ ^ 2 := by
  have hadj : A.adjoint = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hsa.star_eq
  have hstep : ⟪(A * A) y, y⟫_ℂ = ⟪A y, A y⟫_ℂ := by
    rw [mul_apply_eq_comp, ← hadj, ContinuousLinearMap.adjoint_inner_left, hadj]
  rw [hstep, inner_self_eq_norm_sq_to_K]
  norm_cast

omit [CompleteSpace H] in
private theorem nonneg_re_inner {B : H →L[ℂ] H} (hB : 0 ≤ B) (y : H) :
    0 ≤ RCLike.re ⟪B y, y⟫_ℂ :=
  (ContinuousLinearMap.nonneg_iff_isPositive.mp hB).2 y

omit [CompleteSpace H] in
private theorem re_inner_real_smul_self (c : ℝ) (y : H) :
    RCLike.re ⟪c • y, y⟫_ℂ = c * ‖y‖ ^ 2 := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c y, inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

private theorem upper_bound_on_cutoff_kernel {A : E →L[ℂ] E} (hA : 0 ≤ A) {s : ℝ}
    (hs : 0 ≤ s) {y : E} (hy : (spectral_cutoff A) s y = 0) : ‖A y‖ ≤ s * ‖y‖ := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hpt : ∀ t ∈ spectrum ℝ A, 0 ≤ s ^ 2 + (t + s) * max (t - s) 0 - t * t := by
    intro t ht
    have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg hA ht
    rcases le_or_gt t s with h | h
    · rw [max_eq_right (by linarith)]; nlinarith
    · rw [max_eq_left (by linarith)]; nlinarith
  have hnn : (0 : E →L[ℂ] E) ≤
      (s ^ 2 : ℝ) • (1 : E →L[ℂ] E) + (A + (s : ℝ) • 1) * (spectral_cutoff A) s - A * A := by
    rw [cutoff_split A hA s]
    exact cfc_nonneg hpt
  have hform := nonneg_re_inner hnn y
  have happ : ((A + (s : ℝ) • 1) * (spectral_cutoff A) s) y = 0 := by
    rw [mul_apply_eq_comp]
    simp [hy]
  simp only [sub_apply, add_apply, happ, add_zero, smul_apply, one_apply_eq_self,
    inner_sub_left, map_sub, re_inner_mul_self hsa y,
    re_inner_real_smul_self (s ^ 2) y] at hform
  have hsq : ‖A y‖ ^ 2 ≤ (s * ‖y‖) ^ 2 := by nlinarith
  have h1 : (0 : ℝ) ≤ ‖A y‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ s * ‖y‖ := mul_nonneg hs (norm_nonneg _)
  nlinarith

private theorem lower_bound_on_cutoff_kernel_orthogonal {A : E →L[ℂ] E} (hA : 0 ≤ A)
    {s : ℝ} {y : E} (hy : y ∈ (LinearMap.ker ((spectral_cutoff A) s : E →ₗ[ℂ] E))ᗮ) :
    s * ‖y‖ ≤ ‖A y‖ := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hco : IsSelfAdjoint ((spectral_cocutoff A) s) := is_self_adjoint_cocutoff A hA s
  have hcoadj : ((spectral_cocutoff A) s).adjoint = (spectral_cocutoff A) s := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hco.star_eq
  have hrange : ∀ x : E,
      (spectral_cocutoff A) s x ∈ LinearMap.ker ((spectral_cutoff A) s : E →ₗ[ℂ] E) :=
    fun x => cutoff_cocutoff_apply A hA s x
  have hzero : (spectral_cocutoff A) s y = 0 := by
    have hperp : ∀ u ∈ LinearMap.ker ((spectral_cutoff A) s : E →ₗ[ℂ] E), ⟪u, y⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal _ y).mp hy
    have hself : ⟪(spectral_cocutoff A) s y, (spectral_cocutoff A) s y⟫_ℂ = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_left, hcoadj]
      exact hperp _ (hrange ((spectral_cocutoff A) s y))
    exact inner_self_eq_zero.mp hself
  have hnn : (0 : E →L[ℂ] E) ≤ (spectral_cocutoff A) s - ((s : ℝ) • (1 : E →L[ℂ] E) - A) := by
    rw [cocutoff_split A hA s]
    refine cfc_nonneg fun t _ => ?_
    rcases le_or_gt (s - t) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h.le]; linarith
  have hform := nonneg_re_inner hnn y
  simp only [sub_apply, hzero, smul_apply, one_apply_eq_self, inner_sub_left,
    map_sub, re_inner_real_smul_self s y, zero_sub, neg_sub] at hform
  have hcs : RCLike.re ⟪A y, y⟫_ℂ ≤ ‖A y‖ * ‖y‖ :=
    le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  · have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hkey : s * ‖y‖ ^ 2 ≤ ‖A y‖ * ‖y‖ := by linarith
    nlinarith

/-- Every nonnegative strict threshold below `aₙ(T)` admits an `(n+1)`-dimensional
test subspace with a strictly larger lower modulus. -/
theorem exists_independent_lower_bound
    (T : E →L[ℂ] F) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < (approximation_number T) n) :
    ∃ s : ℝ, r < s ∧ ∃ v : Fin (n + 1) → E, LinearIndependent ℂ v ∧
      ∀ x ∈ Submodule.span ℂ (Set.range v), s * ‖x‖ ≤ ‖T x‖ := by
  obtain ⟨s, hrs, hsa⟩ := exists_between hr
  have hs0 : 0 ≤ s := hr0.trans hrs.le
  set A : E →L[ℂ] E := (modulus T) with hAdef
  have hA : (0 : E →L[ℂ] E) ≤ A := (modulus_nonneg T)
  set K : Submodule ℂ E := LinearMap.ker ((spectral_cutoff A) s : E →ₗ[ℂ] E) with hKdef
  have hKclosed : IsClosed (K : Set E) := by
    simpa [hKdef] using ((spectral_cutoff A) s).isClosed_ker
  have : CompleteSpace (K : Type _) := hKclosed.completeSpace_coe
  have hlow : ∀ y ∈ Kᗮ, s * ‖y‖ ≤ ‖T y‖ := by
    intro y hy
    rw [← (norm_modulus_apply T)]
    exact lower_bound_on_cutoff_kernel_orthogonal hA hy
  rcases lt_or_ge (n : Cardinal) (Module.rank ℂ (Kᗮ : Submodule ℂ E)) with hbig | hsmall
  · obtain ⟨v, hv⟩ :=
      exists_linearIndependent_of_le_rank (R := ℂ) (M := (Kᗮ : Submodule ℂ E))
        (n := n + 1) (by
          simpa only [Nat.cast_add_one] using Cardinal.natCast_add_one_le_iff.mpr hbig)
    refine ⟨s, hrs, fun i => ((v i : Kᗮ) : E), hv.map' (Kᗮ).subtype (Kᗮ).ker_subtype, ?_⟩
    intro x hx
    refine hlow x ?_
    refine Submodule.span_le.mpr ?_ hx
    rintro _ ⟨i, rfl⟩
    exact (v i).2
  · exfalso
    have : FiniteDimensional ℂ (Kᗮ : Submodule ℂ E) :=
      Module.rank_lt_aleph0_iff.mp (hsmall.trans_lt (Cardinal.natCast_lt_aleph0 (n := n)))
    have hfr : Module.finrank ℂ (Kᗮ : Submodule ℂ E) ≤ n := by
      have hrk := Module.finrank_eq_rank' ℂ (Kᗮ : Submodule ℂ E)
      rw [← hrk] at hsmall
      exact_mod_cast hsmall
    have hrangeeq :
        LinearMap.range ((T ∘L (Kᗮ : Submodule ℂ E).starProjection) : E →ₗ[ℂ] F) =
          Submodule.map (T : E →ₗ[ℂ] F) (Kᗮ) := by
      change LinearMap.range ((T : E →ₗ[ℂ] F).comp
          (((Kᗮ : Submodule ℂ E).starProjection : E →ₗ[ℂ] E))) = _
      rw [LinearMap.range_comp, Submodule.range_starProjection]
    have : FiniteDimensional ℂ (Submodule.map (T : E →ₗ[ℂ] F) (Kᗮ)) := inferInstance
    have hrank : (T ∘L (Kᗮ : Submodule ℂ E).starProjection).rank ≤ (n : Cardinal) := by
      rw [LinearMap.rank, hrangeeq,
        ← Module.finrank_eq_rank' ℂ (Submodule.map (T : E →ₗ[ℂ] F) (Kᗮ))]
      exact_mod_cast le_trans (Submodule.finrank_map_le _ _) hfr
    have hnorm : ‖T - T ∘L (Kᗮ : Submodule ℂ E).starProjection‖ ≤ s := by
      refine ContinuousLinearMap.opNorm_le_bound _ hs0 fun x => ?_
      have hsplit : x - (Kᗮ : Submodule ℂ E).starProjection x = K.starProjection x := by
        rw [K.starProjection_orthogonal']
        simp
      have hval : (T - T ∘L (Kᗮ : Submodule ℂ E).starProjection) x
          = T (x - (Kᗮ : Submodule ℂ E).starProjection x) := by
        simp [map_sub]
      rw [hval, hsplit, ← (norm_modulus_apply T)]
      refine le_trans (upper_bound_on_cutoff_kernel hA hs0
        (K.starProjection_apply_mem x)) ?_
      gcongr
      exact K.norm_starProjection_apply_le x
    have hle := (approximation_number_le_error T) hrank
    linarith

end
end D5.S3.HilbertOperators.Approximation.MinMaxLowerBound
