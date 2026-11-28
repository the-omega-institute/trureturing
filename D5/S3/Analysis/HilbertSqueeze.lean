/- GID: D5/S3/Analysis/HilbertSqueeze
   generality: G
   mirror-B: none(waiver:covered-by-ccrgaussian-extension-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Spectral coordinates for a bounded invertible operator and its inverse adjoint on a complex Hilbert space. -/

import OmegaBuild.Commands
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.StarOrder
import D5.S3.Analysis.PositiveSkew
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

compile_only_with_mathlib

/-!
Omega original.

Spectral coordinates for a bounded invertible operator and its inverse adjoint on a
complex Hilbert space.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace Ring
open ContinuousLinearMap

noncomputable section
namespace Omega.Analysis.HilbertSqueeze

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The metric of a bounded invertible operator is uniformly positive. -/
theorem star_mul_self_coercive (L : H →L[ℂ] H) (u : IsUnit L) :
    ∃ c : ℝ, 0 < c ∧ c • (1 : H →L[ℂ] H) ≤ L.adjoint * L := by
  simpa only [star_eq_adjoint] using
    Omega.positive_lower_bound (star_mul_self_nonneg L) (u.star.mul u)

/-- An inverse of a self-adjoint operator is self-adjoint. -/
theorem inverse_adjoint_eq_self {S : H →L[ℂ] H} (hS : S.adjoint = S) :
    (S⁻¹ʳ).adjoint = S⁻¹ʳ := by
  rw [← star_eq_adjoint, ← Ring.inverse_star, star_eq_adjoint, hS]

/-- The difference of two positive covariances is the congruence formula for the transition metric. -/
theorem sqrt_transition_metric_sub (D₁ D₂ : H →L[ℂ] H) (h₁ : 0 ≤ D₁) (h₂ : 0 ≤ D₂)
    (u₁ : IsUnit D₁) :
    let L := CFC.sqrt D₂ * (CFC.sqrt D₁)⁻¹ʳ
    L.adjoint * L - 1 =
      (CFC.sqrt D₁)⁻¹ʳ * (D₂ - D₁) * (CFC.sqrt D₁)⁻¹ʳ := by
  have root_adjoint (D : H →L[ℂ] H) : (CFC.sqrt D).adjoint = CFC.sqrt D :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg D)).star_eq
  let S := CFC.sqrt D₁
  let T := CFC.sqrt D₂
  have hu : IsUnit S := (CFC.isUnit_sqrt_iff D₁ h₁).mpr u₁
  change (T * S⁻¹ʳ).adjoint * (T * S⁻¹ʳ) - 1 = _
  rw [← star_eq_adjoint, star_mul, star_eq_adjoint, star_eq_adjoint,
    root_adjoint D₂, inverse_adjoint_eq_self (root_adjoint D₁)]
  change S⁻¹ʳ * T * (T * S⁻¹ʳ) - 1 = S⁻¹ʳ * (D₂ - D₁) * S⁻¹ʳ
  rw [mul_assoc S⁻¹ʳ T, ← mul_assoc T T, CFC.sqrt_mul_sqrt_self D₂ h₂,
    mul_sub, sub_mul, ← mul_assoc, ← CFC.sqrt_mul_sqrt_self D₁ h₁,
    ← mul_assoc S⁻¹ʳ S S, Ring.inverse_mul_cancel S hu, one_mul, Ring.mul_inverse_cancel S hu]

private theorem squeeze_log_bound {c lam : ℝ} (hc : 0 < c) (hμ : c ≤ 1 + lam) :
    |Real.log (1 + lam)| ≤ max 1 c⁻¹ * |lam| := by
  have hpos := hc.trans_le hμ
  have hl := Real.one_sub_inv_le_log_of_pos hpos
  have hu := Real.log_le_sub_one_of_pos hpos
  have h₁ : lam ≤ max 1 c⁻¹ * |lam| := (le_abs_self lam).trans
    (le_mul_of_one_le_left (abs_nonneg lam) (le_max_left _ _))
  have h₂ : |lam / (1 + lam)| ≤ max 1 c⁻¹ * |lam| := by
    rw [abs_div, abs_of_pos hpos, div_eq_mul_inv, mul_comm |lam|]
    exact mul_le_mul_of_nonneg_right
      ((inv_le_inv₀ hpos hc).mpr hμ |>.trans (le_max_right _ _)) (abs_nonneg lam)
  have he : 1 - (1 + lam)⁻¹ = lam / (1 + lam) := by field_simp; ring
  rw [he] at hl
  exact abs_le.mpr ⟨(abs_le.mp h₂).1.trans hl, by linarith⟩

private theorem metric_norm_sum {ι : Type*} (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] H)
    (μ : ι → ℝ) (he : ∀ i, (A.adjoint * A) (b i) = (μ i : ℂ) • b i)
    (x : H) : HasSum (fun i => μ i * ‖⟪b i, x⟫_ℂ‖ ^ 2) (‖A x‖ ^ 2) := by
  let C := A.adjoint * A
  have ha : C.adjoint = C := by simp [C, ← star_eq_adjoint, star_mul]
  rw [apply_norm_sq_eq_inner_adjoint_right A x]
  change HasSum _ (⟪x, C x⟫_ℂ).re
  have h := (b.hasSum_inner_mul_inner x (C x)).mapL Complex.reCLM
  change HasSum (fun i => (⟪x, b i⟫_ℂ * ⟪b i, C x⟫_ℂ).re) _ at h
  convert h using 1
  · funext i
    have he' : C (b i) = (μ i : ℂ) • b i := he i
    rw [← adjoint_inner_left C, ha, he', inner_smul_left, Complex.conj_ofReal,
      ← inner_conj_symm x (b i)]
    rw [← mul_left_comm (μ i : ℂ), mul_comm (starRingEnd ℂ _) _,
      Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  · rfl

omit [CompleteSpace H] in
/-- In a separable Hilbert space, the indices of a Hilbert basis form a countable type. -/
theorem countable_basis {ι : Type*} [TopologicalSpace.SeparableSpace H]
    (C : HilbertBasis ι ℂ H) : Countable ι := by
  let s (i : ι) := Metric.ball (C i) (1 / 2)
  refine Pairwise.countable_of_isOpen_disjoint (s := s) ?_ (fun _ => Metric.isOpen_ball)
    (fun i => ⟨C i, Metric.mem_ball_self (by norm_num)⟩)
  intro i j hij
  refine Set.disjoint_left.mpr fun x hi hj => ?_
  have ht := dist_triangle (C i) x (C j)
  have hi' := Metric.mem_ball.mp hi
  have hj' := Metric.mem_ball.mp hj
  rw [dist_comm] at hi'
  have hd : dist (C i) (C j) < 1 := by linarith
  let inst : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  have ho : ⟪C i, C j⟫_ℝ = 0 := by
    change (⟪C i, C j⟫_ℂ).re = 0
    rw [C.orthonormal.2 hij]
    rfl
  have hsq := norm_sub_sq_eq_norm_sq_add_norm_sq_real ho
  rw [C.orthonormal.1 i, C.orthonormal.1 j, ← dist_eq_norm] at hsq
  nlinarith [dist_nonneg (x := C i) (y := C j)]

/-- A square-summable perturbation of an invertible metric gives square-summable logarithmic
weights and the two corresponding norm expansions along its eigenbasis. -/
theorem exists_logWeights_of_metric {ι : Type*} (b : HilbertBasis ι ℂ H)
    (L : H →L[ℂ] H) (hL : IsUnit L) (s : ι → ℝ)
    (he : ∀ i, (L.adjoint * L) (b i) = ((1 + s i : ℝ) : ℂ) • b i)
    (hs : Summable (fun i => (s i) ^ 2)) :
    ∃ r : ι → ℝ, Summable (fun i => (r i) ^ 2) ∧ ∀ x y : H,
      ‖L x‖ ^ 2 + ‖(L.adjoint)⁻¹ʳ y‖ ^ 2 =
        ∑' i, (Real.exp (2 * r i) * ‖⟪b i, x⟫_ℂ‖ ^ 2 +
          Real.exp (-2 * r i) * ‖⟪b i, y⟫_ℂ‖ ^ 2) := by
  obtain ⟨c, hc, hcoer⟩ := star_mul_self_coercive L hL
  let μ (i : ι) := 1 + s i
  have hμ (i : ι) : c ≤ μ i := by
    have hh := (nonneg_iff_isPositive.mp (sub_nonneg.mpr hcoer)).re_inner_nonneg_left (b i)
    change 0 ≤ (⟪(L.adjoint * L) (b i) - c • b i, b i⟫_ℂ).re at hh
    rw [inner_sub_left, he, inner_smul_left, inner_smul_left_eq_smul,
      inner_self_eq_norm_sq_to_K, b.orthonormal.1] at hh
    simpa [Complex.sub_re, Algebra.smul_def, sub_nonneg] using hh
  let r (i : ι) := Real.log (μ i) / 2
  refine ⟨r, ?_, ?_⟩
  · let K := (max 1 c⁻¹ / 2) ^ 2
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_) (hs.mul_left K)
    have hh := div_le_div_of_nonneg_right (squeeze_log_bound hc (hμ i)) (by norm_num : (0 : ℝ) ≤ 2)
    have habs : |r i| ≤ (max 1 c⁻¹ / 2) * |s i| := by
      simpa [r, abs_div, mul_div_right_comm] using hh
    simpa [K, mul_pow, sq_abs] using pow_le_pow_left₀ (abs_nonneg (r i)) habs 2
  intro x y
  let M := (L.adjoint)⁻¹ʳ
  have huadj : IsUnit L.adjoint := by simpa only [star_eq_adjoint] using hL.star
  have hinv : M.adjoint * M * (L.adjoint * L) = 1 := by
    change ((L.adjoint)⁻¹ʳ).adjoint * (L.adjoint)⁻¹ʳ * (L.adjoint * L) = 1
    rw [← star_eq_adjoint (L.adjoint)⁻¹ʳ, ← Ring.inverse_star, star_eq_adjoint,
      adjoint_adjoint, mul_assoc L⁻¹ʳ, ← mul_assoc _ L.adjoint L,
      Ring.inverse_mul_cancel _ huadj, one_mul, Ring.inverse_mul_cancel _ hL]
  have hMe (i : ι) : (M.adjoint * M) (b i) = (↑((μ i)⁻¹) : ℂ) • b i := by
    have hh : (M.adjoint * M) ((L.adjoint * L) (b i)) = b i := DFunLike.congr_fun hinv _
    rw [he i, map_smul] at hh
    have hp : (μ i : ℂ) ≠ 0 := by exact_mod_cast (hc.trans_le (hμ i)).ne'
    convert congrArg (fun z : H => (μ i : ℂ)⁻¹ • z) hh using 1
    · rw [smul_smul, inv_mul_cancel₀ hp, one_smul]
    · rw [Complex.ofReal_inv]
  have hsum := (metric_norm_sum b L μ he x).add
    (metric_norm_sum b M (fun i => (μ i)⁻¹) hMe y)
  refine hsum.tsum_eq.symm.trans ?_
  apply tsum_congr
  intro i
  have hp : Real.exp (2 * r i) = μ i := by
    rw [show 2 * r i = Real.log (μ i) by dsimp [r]; ring, Real.exp_log (hc.trans_le (hμ i))]
  rw [hp, neg_mul, Real.exp_neg, hp]

end Omega.Analysis.HilbertSqueeze
