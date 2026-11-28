import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Omega original.
Planar Gaussian integration in complex coordinates and integrability of finite products. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex MeasureTheory
open scoped BigOperators

namespace Omega.PlanarGaussian

def realGaussian (a : ℝ) (u : ℂ) (x : ℝ) : ℂ :=
  exp (-(a : ℂ) * (x : ℂ) ^ 2 + u * x)

private theorem integral_realGaussian {a : ℝ} (ha : 0 < a) (u : ℂ) :
    (∫ x : ℝ, realGaussian a u x) =
      (Real.sqrt (Real.pi / a) : ℂ) * exp (u ^ 2 / (4 * a)) := by
  have h := integral_cexp_quadratic (b := -(a : ℂ)) (by simpa using neg_neg_of_pos ha) u 0
  simp only [add_zero, neg_neg, zero_sub, mul_neg, div_neg] at h
  rw [← Complex.ofReal_div, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow] at h
  simpa only [realGaussian, neg_neg] using h

def planarGaussian (a b : ℝ) (u v : ℂ) (z : ℂ) : ℂ :=
  realGaussian a u z.re * realGaussian b v z.im

theorem integral_planarGaussian {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u v : ℂ) :
    (∫ z : ℂ, planarGaussian a b u v z) =
      ((Real.sqrt (Real.pi / a) * Real.sqrt (Real.pi / b) : ℝ) : ℂ) *
        exp (u ^ 2 / (4 * a) + v ^ 2 / (4 * b)) := by
  rw [← Complex.volume_preserving_equiv_real_prod.symm.integral_comp']
  change (∫ z : ℝ × ℝ, realGaussian a u z.1 * realGaussian b v z.2) = _
  rw [Measure.volume_eq_prod, MeasureTheory.integral_prod_mul,
    integral_realGaussian ha, integral_realGaussian hb, Complex.ofReal_mul, Complex.exp_add]
  ring

def weight {J : Type*} [Fintype J] (z : J → ℂ) : ℝ :=
  Real.exp (-(∑ i, ‖z i‖ ^ 2) / 2)

theorem weight_integrable {J : Type*} [Fintype J] : Integrable (weight (J := J)) := by
  have h : Integrable (fun z : ℂ => Real.exp (-‖z‖ ^ 2 / 2)) := by
    apply (Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding).mp
    rw [Measure.volume_eq_prod]
    have he : (fun z : ℝ × ℝ => Real.exp (-‖Complex.measurableEquivRealProd.symm z‖ ^ 2 / 2)) =
        fun z => Real.exp (-(1 / 2) * z.1 ^ 2) * Real.exp (-(1 / 2) * z.2 ^ 2) := by
      funext z
      rw [← Real.exp_add, Complex.sq_norm, Complex.normSq_apply]
      change Real.exp (-(z.1 * z.1 + z.2 * z.2) / 2) = _
      congr 1
      ring
    change Integrable (fun z : ℝ × ℝ => Real.exp (-‖Complex.measurableEquivRealProd.symm z‖ ^ 2 / 2)) _
    rw [he]
    exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).mul_prod
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2))
  have he (z : J → ℂ) : weight z = ∏ i, Real.exp (-‖z i‖ ^ 2 / 2) := by
    simp only [weight, ← Real.exp_sum, ← Finset.sum_neg_distrib, Finset.sum_div]
  change Integrable (fun z : J → ℂ => weight z)
  simp_rw [he]
  exact Integrable.fintype_prod (fun _ : J => h)

section Average

variable {J E : Type*} [Fintype J] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Gaussian weight times a strongly continuous isometry orbit is Bochner integrable. -/
theorem weighted_integrable (U : (J → ℂ) → E ≃ₗᵢ[ℂ] E)
    (hU : ∀ x, Continuous fun z => U z x) (x : E) :
    Integrable (fun z => (weight z : ℂ) • U z x) := by
  refine (weight_integrable.mul_const ‖x‖).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    exact (Complex.continuous_ofReal.comp (by unfold weight; fun_prop)).smul
      (hU x)
  · filter_upwards with z
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ weight z from (Real.exp_pos _).le),
      LinearIsometryEquiv.norm_map]

/-- A scalar multiple of the Gaussian average of a strongly continuous isometry family. -/
def weightedAverage (U : (J → ℂ) → E ≃ₗᵢ[ℂ] E)
    (hU : ∀ x, Continuous fun z => U z x) (a : ℂ) : E →L[ℂ] E := by
  refine LinearMap.mkContinuous
    { toFun := fun ψ => a • ∫ z : J → ℂ, (weight z : ℂ) • U z ψ
      map_add' := fun ψ χ => by
        simp only [map_add, smul_add]
        rw [integral_add (weighted_integrable U hU ψ) (weighted_integrable U hU χ), smul_add]
      map_smul' := fun c ψ => by
        have h (z : J → ℂ) : (weight z : ℂ) • U z (c • ψ) =
            c • ((weight z : ℂ) • U z ψ) := by
          rw [map_smul, smul_comm]
        simp only [h, integral_smul, RingHom.id_apply, smul_comm a c] }
    (‖a‖ * ∫ z : J → ℂ, weight z) ?_
  intro ψ
  simp only [LinearMap.coe_mk, AddHom.coe_mk, norm_smul]
  rw [mul_assoc, ← integral_mul_const]
  gcongr
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  congr 1
  funext z
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ weight z from (Real.exp_pos _).le),
    LinearIsometryEquiv.norm_map]

end Average

private theorem sq_le_cosh (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have hn (n : ℕ) : 0 ≤ x ^ (2 * n) / ((2 * n).factorial : ℝ) := by
    rw [Nat.mul_comm, pow_mul]
    positivity
  have h := (Real.hasSum_cosh x).summable.sum_le_tsum (Finset.range 2) (fun n _ => hn n)
  simpa [Finset.sum_range_succ, (Real.hasSum_cosh x).tsum_eq] using h

theorem summable_sq_of_prod {I : Type*} {r : I → ℝ} (S : Finset I)
    (h : ∀ F : Finset I, Disjoint F S → (1 / 2 : ℝ) ≤ ∏ i ∈ F, (Real.cosh (r i))⁻¹) :
    Summable (fun i => (r i) ^ 2) := by
  classical
  have hl (F : Finset I) : 1 + ∑ i ∈ F, (r i) ^ 2 / 2 ≤ ∏ i ∈ F, Real.cosh (r i) := by
    induction F using Finset.induction_on with
    | empty => simp
    | insert i F hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      have hn : 0 ≤ ∑ j ∈ F, (r j) ^ 2 / 2 :=
        Finset.sum_nonneg (fun _ _ => by positivity)
      have hh := mul_le_mul (sq_le_cosh (r i)) ih (by linarith) (Real.cosh_pos _).le
      nlinarith [mul_nonneg (show 0 ≤ (r i) ^ 2 / 2 by positivity) hn]
  apply summable_of_sum_le (fun i => sq_nonneg (r i)) (c := 2 + ∑ i ∈ S, (r i) ^ 2)
  intro F
  have hF := h (F \ S) Finset.sdiff_disjoint
  rw [Finset.prod_inv_distrib, ← one_div, le_div_iff₀ (by positivity)] at hF
  have hh := hl (F \ S)
  rw [← Finset.sum_div] at hh
  have hp := Finset.sum_sdiff (f := fun i => (r i) ^ 2) (Finset.inter_subset_left (s₂ := S) (s₁ := F))
  rw [Finset.inter_comm F S, Finset.sdiff_inter_self_right] at hp
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right (s₁ := F) (s₂ := S))
    (fun i _ _ => sq_nonneg (r i))
  rw [Finset.inter_comm F S] at hle
  linarith

end Omega.PlanarGaussian
