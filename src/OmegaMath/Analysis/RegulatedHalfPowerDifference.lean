import OmegaBuild.Commands
import Batteries.Tactic.OpenPrivate
import OmegaMath.Analysis.HalfPowerCapIntegral
import OmegaMath.Analysis.RegulatedSeparation
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
Omega original.

Dominated convergence for the elementary half-power massive correction.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace Omega

open private regulatedSeparation_norm_bound from OmegaMath.Analysis.RegulatedSeparation

/-- The massive-minus-massless elementary correction at a complex separation. -/
def halfPowerDifference (M : ℝ) (q : ℂ) : ℂ :=
  let r := principalRoot q
  (1 / (8 * (Real.pi : ℂ) ^ 2)) * (Complex.exp (-(M : ℂ) * r) * (1 + M * r) - 1) /
    (q * r)

theorem halfPowerDifference_analyticAt (M : ℝ) {q : ℂ} (hq : 0 < q.re) :
    AnalyticAt ℂ (halfPowerDifference M) q := by
  have hn := slitPlane_ne_zero (Or.inl hq)
  have hr : AnalyticAt ℂ principalRoot q := analyticAt_id.cpow analyticAt_const (Or.inl hq)
  have hroot : principalRoot q ≠ 0 :=
    fun he => (principalRoot_re_pos hq).ne' (by rw [he]; rfl)
  have ha : AnalyticAt ℂ (fun r => -(M : ℂ) * principalRoot r) q := analyticAt_const.mul hr
  have hb : AnalyticAt ℂ (fun r => 1 + M * principalRoot r) q :=
    analyticAt_const.add (analyticAt_const.mul hr)
  exact (analyticAt_const.mul ((ha.cexp.mul hb).sub analyticAt_const)).div
    (analyticAt_id.mul hr) (mul_ne_zero hn hroot)

private theorem numerator_norm_le {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) :
    ‖Complex.exp (-z) * (1 + z) - 1‖ ≤
      (Real.exp R * (1 + R) + 1) * ‖z‖ ^ 2 := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (-z) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one, norm_neg] at h
  rw [show Complex.exp (-z) * (1 + z) - 1 =
    (Complex.exp (-z) - (1 + -z)) * (1 + z) - z ^ 2 by ring]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (‖z‖ ^ 2 * Real.exp R) * (1 + R) + ‖z‖ ^ 2 := by
      gcongr
      · exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hz) (sq_nonneg _))
      · simpa using (norm_add_le (1 : ℂ) z).trans (by simp; linarith)
    _ = _ := by ring

private theorem halfPowerDifference_norm_bound (M : ℝ) :
    ∃ C ≥ (0 : ℝ), ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ ≤ 7 →
      ‖halfPowerDifference M q‖ ≤ C * (Real.sqrt ‖q‖)⁻¹ := by
  let R := |M| * Real.sqrt 7
  let c : ℝ := (8 * Real.pi ^ 2)⁻¹
  refine ⟨c * (Real.exp R * (1 + R) + 1) * M ^ 2, by dsimp [c, R]; positivity, ?_⟩
  intro q hq hq'
  have hz : ‖(M : ℂ) * principalRoot q‖ ≤ R := by
    rw [norm_mul, principalRoot_norm, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hq') (abs_nonneg _)
  have hsq : ‖(M : ℂ) * principalRoot q‖ ^ 2 = M ^ 2 * ‖q‖ := by
    rw [norm_mul, mul_pow, principalRoot_norm, Real.sq_sqrt (norm_nonneg _),
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold halfPowerDifference
  rw [norm_div, norm_mul, norm_mul, principalRoot_norm, show
    ‖(1 / (8 * (Real.pi : ℂ) ^ 2) : ℂ)‖ = c by
      rw [one_div, norm_inv, norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]]
  have hh := numerator_norm_le hz
  rw [hsq, ← neg_mul] at hh
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hden : 0 ≤ ‖q‖ * Real.sqrt ‖q‖ := by positivity
  refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh hc) hden).trans_eq ?_
  field_simp [hq.ne', (Real.sqrt_pos.2 hq).ne']

theorem tendsto_integral_regulated_halfPowerDifference {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {u v x : X → ℝ} {a : X → ℂ}
    (hu : Measurable u) (hv : Measurable v) (hx : Measurable x) (ha : Measurable a)
    (M : ℝ) {δ D : ℝ} (hδ : 0 < δ) (hD : 0 ≤ D)
    (hs : ∀ᵐ q ∂μ, u q ∈ Ioo (0 : ℝ) 1 ∧ v q ∈ Ioo (0 : ℝ) 1 ∧
      |x q| ≤ 1 ∧ x q < 1 ∧ ‖a q‖ ≤ D)
    (hzero : ∀ᵐ q ∂μ, (u q < δ ∨ v q < δ) → a q = 0)
    (hint : Integrable (fun q => (Real.sqrt (1 - x q))⁻¹) μ) :
    Tendsto (fun ε : ℝ => ∫ q, a q *
      halfPowerDifference M (regulatedSeparation ε (u q) (v q) (x q)) ∂μ)
      (𝓝[>] 0) (𝓝 (∫ q, a q * halfPowerDifference M
        (regulatedSeparation 0 (u q) (v q) (x q)) ∂μ)) ∧
      Integrable (fun q => a q * halfPowerDifference M
        (regulatedSeparation 0 (u q) (v q) (x q))) μ := by
  let f (ε : ℝ) (q : X) := a q *
    halfPowerDifference M (regulatedSeparation ε (u q) (v q) (x q))
  obtain ⟨K, hK, hk⟩ := halfPowerDifference_norm_bound M
  let majorant (q : X) := (D * K / Real.sqrt (2 * δ ^ 2)) * (Real.sqrt (1 - x q))⁻¹
  have hi : Integrable majorant μ := hint.const_mul _
  have hmeas (ε : ℝ) : Measurable (f ε) := by
    unfold f halfPowerDifference principalRoot regulatedSeparation
    fun_prop
  have hb (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) : ∀ᵐ q ∂μ, ‖f ε q‖ ≤ majorant q := by
    filter_upwards [hs, hzero] with q ⟨huq, hvq, hxq, hxq', haq⟩ hz
    by_cases hcut : u q < δ ∨ v q < δ
    · simp [f, hz hcut]
      dsimp [majorant]
      positivity
    · push Not at hcut
      have ht := regulatedSeparation_norm_bound hε₀ hε₁ huq hvq hxq
      have hxpos := sub_pos.mpr hxq'
      have hlo : (2 * δ ^ 2) * (1 - x q) ≤
          ‖regulatedSeparation ε (u q) (v q) (x q)‖ := by
        apply le_trans _ ht.1
        apply mul_le_mul_of_nonneg_right _ hxpos.le
        rw [mul_assoc, pow_two]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hcut.1 hcut.2 hδ.le huq.1.le) two_pos.le
      have hlowpos : 0 < (2 * δ ^ 2) * (1 - x q) := by positivity
      dsimp only [f, majorant]
      rw [norm_mul]
      calc
        _ ≤ D * (K * (Real.sqrt ‖regulatedSeparation ε (u q) (v q) (x q)‖)⁻¹) :=
          mul_le_mul haq (hk _ (hlowpos.trans_le hlo) ht.2) (norm_nonneg _) hD
        _ ≤ D * (K * (Real.sqrt ((2 * δ ^ 2) * (1 - x q)))⁻¹) := by
          gcongr
        _ = _ := by rw [Real.sqrt_mul (by positivity), mul_inv_rev]; ring
  refine ⟨?_, hi.mono' (hmeas 0).aestronglyMeasurable (hb 0 le_rfl zero_le_one)⟩
  refine tendsto_integral_filter_of_dominated_convergence (F := f) (f := f 0) majorant
    (.of_forall fun ε => (hmeas ε).aestronglyMeasurable) ?_ hi ?_
  · have hh : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo (0 : ℝ) 1 :=
      Ioo_mem_nhdsGT (by norm_num)
    exact hh.mono fun ε he => hb ε he.1.le he.2.le
  · filter_upwards [hs] with q ⟨huq, hvq, _, hxq, _⟩
    have hc : Continuous (fun ε => regulatedSeparation ε (u q) (v q) (x q)) := by
      unfold regulatedSeparation
      fun_prop
    have hp : 0 < (regulatedSeparation 0 (u q) (v q) (x q)).re := by
      simp [regulatedSeparation]
      exact mul_pos (mul_pos (mul_pos two_pos huq.1) hvq.1) (sub_pos.mpr hxq)
    exact (((halfPowerDifference_analyticAt M hp).continuousAt.comp
      (x := (0 : ℝ)) hc.continuousAt).tendsto.const_mul (a q)).mono_left nhdsWithin_le_nhds

end Omega
