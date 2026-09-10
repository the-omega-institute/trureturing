/- GID: D5/S3/Weil/Probability/AnalyticLogarithmicContinuation
   generality: G
   mirror-B: D5/B/S3/Weil/Probability/AnalyticLogarithmicContinuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An absolutely convergent scalar series and a local logarithmic derivative identity force zero-freeness on a connected analytic domain. -/

import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic

/-!
The analytic tools are classical. This module retains the scalar coefficients
and proves the two analytic obligations used by CanonicalLiGrowthZeroFree:
quadratic coefficient bounds imply disk analyticity, and a local equation
f'=g*f extends and excludes zeros. No global logarithm, global logarithmic
identity or pre-existing zero-free domain is a hypothesis of the local theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Probability.AnalyticLogarithmicContinuation

open Filter Set
open scoped Topology BigOperators NNReal ENNReal

/-- The polynomial bound controls the full absolute series at each radius,
including zero radius. No finite coefficient cutoff is used. -/
theorem quadratic_coefficients_summable (a : ℕ → ℂ) (C : ℝ)
    (bound : ∀ n, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ 2)
    (r : ℝ≥0) (hr : r < 1) :
    Summable (fun n => ‖a n‖ * (r : ℝ) ^ n) := by
  have hrnorm : ‖(r : ℝ)‖ < 1 := by simpa using hr
  have h0 := summable_geometric_of_norm_lt_one hrnorm
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hrnorm
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hrnorm
  have major : Summable (fun n : ℕ => C * ((n : ℝ) + 1) ^ 2 * (r : ℝ) ^ n) := by
    apply (((h2.add (h1.mul_left 2)).add h0).mul_left C).congr
    intro n
    simp only [pow_one]
    ring
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg r.property n))
    (fun n => mul_le_mul_of_nonneg_right (bound n) (pow_nonneg r.property n)) major

/-- Absolute convergence at every smaller radius makes the actual scalar sum
analytic throughout the unit disk, by the existing formal-series radius API. -/
theorem scalar_series_analytic_unit_disk (a : ℕ → ℂ)
    (summable : ∀ r : ℝ≥0, r < 1 → Summable (fun n => ‖a n‖ * (r : ℝ) ^ n)) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∑' n, a n * z ^ n) (Metric.ball 0 1) := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ a
  have radius : (1 : ℝ≥0∞) ≤ p.radius := by
    apply ENNReal.le_of_forall_nnreal_lt
    intro r hr
    have hr' : r < 1 := by exact_mod_cast hr
    apply p.le_radius_of_summable
    simpa only [p, FormalMultilinearSeries.ofScalars_norm] using summable r hr'
  have sum_eq : p.sum = (fun z : ℂ => ∑' n, a n * z ^ n) := by
    funext z
    simp only [p, FormalMultilinearSeries.sum,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  rw [← sum_eq]
  intro z hz
  apply (FormalMultilinearSeries.analyticOnNhd (p := p))
  have hn : ‖z‖₊ < (1 : ℝ≥0) := by
    exact_mod_cast (show ‖z‖ < 1 from by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  have he : edist z 0 < (1 : ℝ≥0∞) := by
    rw [edist_nndist, nndist_zero_right]
    exact_mod_cast hn
  exact he.trans_le radius

/-- On an open preconnected domain, a nonzero analytic solution of f'=g*f
cannot acquire a zero. The proof compares actual analytic orders at a putative
zero and uses a nonzero value to exclude infinite order. -/
theorem analytic_linear_ode_zero_free {U : Set ℂ} {f g : ℂ → ℂ} {p : ℂ}
    (openU : IsOpen U) (connected : IsPreconnected U)
    (analyticF : AnalyticOnNhd ℂ f U) (analyticG : AnalyticOnNhd ℂ g U)
    (hp : p ∈ U) (nonzero : f p ≠ 0)
    (equation : ∀ z ∈ U, deriv f z = g z * f z) :
    ∀ z ∈ U, f z ≠ 0 := by
  intro z hz zero
  have finiteOrder : analyticOrderAt f z ≠ ⊤ := by
    intro htop
    have locallyZero : f =ᶠ[𝓝 z] (fun _ => 0) := analyticOrderAt_eq_top.mp htop
    have globallyZero : Set.EqOn f (fun _ => 0) U :=
      analyticF.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const connected hz locallyZero
    exact nonzero (globallyZero hp)
  have localEquation : deriv f =ᶠ[𝓝 z] (g * f) := by
    filter_upwards [openU.mem_nhds hz] with w hw
    exact equation w hw
  have orderProduct : analyticOrderAt (deriv f) z =
      analyticOrderAt g z + analyticOrderAt f z := by
    rw [analyticOrderAt_congr localEquation]
    exact analyticOrderAt_mul (analyticG z hz) (analyticF z hz)
  have nondecreasing : analyticOrderAt f z ≤ analyticOrderAt (deriv f) z := by
    rw [orderProduct]
    exact le_add_of_nonneg_left zero_le
  have drops : analyticOrderAt (deriv f) z + 1 = analyticOrderAt f z := by
    simpa [zero] using (analyticF z hz).analyticOrderAt_deriv_add_one
  cases orderF : analyticOrderAt f z with
  | top => exact finiteOrder orderF
  | coe n =>
      cases orderD : analyticOrderAt (deriv f) z with
      | top => simp [orderF, orderD] at drops
      | coe m =>
          have hnm : n ≤ m := by
            exact_mod_cast (show (n : ℕ∞) ≤ (m : ℕ∞) from by
              simpa only [orderF, orderD] using nondecreasing)
          have hmn : m + 1 = n := by
            exact_mod_cast (show (m : ℕ∞) + 1 = (n : ℕ∞) from by
              simpa only [orderF, orderD] using drops)
          omega

/-- A local derivative equation suffices: the identity theorem first extends
it throughout the original domain, then analytic orders exclude every zero. -/
theorem local_logarithmic_equation_zero_free {U : Set ℂ} {f g : ℂ → ℂ} {p : ℂ}
    (openU : IsOpen U) (connected : IsPreconnected U)
    (analyticF : AnalyticOnNhd ℂ f U) (analyticG : AnalyticOnNhd ℂ g U)
    (hp : p ∈ U) (nonzero : f p ≠ 0)
    (localEquation : deriv f =ᶠ[𝓝 p] (fun z => g z * f z)) :
    (∀ z ∈ U, deriv f z = g z * f z) ∧ (∀ z ∈ U, f z ≠ 0) := by
  have derivativeAnalytic : AnalyticOnNhd ℂ (deriv f) U := fun z hz => (analyticF z hz).deriv
  have productAnalytic : AnalyticOnNhd ℂ (fun z => g z * f z) U :=
    fun z hz => (analyticG z hz).mul (analyticF z hz)
  have extended : Set.EqOn (deriv f) (fun z => g z * f z) U :=
    derivativeAnalytic.eqOn_of_preconnected_of_eventuallyEq productAnalytic connected hp localEquation
  exact ⟨fun z hz => extended hz,
    analytic_linear_ode_zero_free openU connected analyticF analyticG hp nonzero
      (fun z hz => extended hz)⟩

#print axioms scalar_series_analytic_unit_disk
#print axioms analytic_linear_ode_zero_free
#print axioms local_logarithmic_equation_zero_free

end D5.S3.Weil.Probability.AnalyticLogarithmicContinuation
