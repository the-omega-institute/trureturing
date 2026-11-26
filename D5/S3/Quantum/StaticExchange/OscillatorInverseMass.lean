/- GID: D5/S3/Quantum/StaticExchange/OscillatorInverseMass
   generality: G
   mirror-B: D5/B/S3/Quantum/StaticExchange/OscillatorInverseMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.ImproperIntegrals]
   utility: none
   digest: Inverse-mass summability characterizes finite positive-frequency oscillator mass. -/

module
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Positive oscillator towers and the inverse-mass obstruction to finite equal-time variance. -/

@[expose] public section
open Real Set MeasureTheory
open scoped ENNReal
namespace D5.S3.Quantum.StaticExchange.OscillatorInverseMass

/-- Positive-frequency response of one Euclidean oscillator with mass m and weight a. -/
noncomputable def oscillator (a m w : ℝ) : ℝ := a / (m ^ 2 + w ^ 2)

/-- Sum in the extended nonnegative reals, allowing divergence at individual frequencies. -/
noncomputable def tower (a m : ℕ → ℝ) (w : ℝ) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (oscillator (a n) (m n) w)

/-- The positive-frequency integral of an oscillator. The real weight may have either sign. -/
theorem oscillator_integral {a m : ℝ} (hm : 0 < m) :
    Integrable (oscillator a m) ∧
      ∫ w in Ioi (0 : ℝ), oscillator a m w = (π / 2) * (a / m) := by
  let g := fun x : ℝ => (1 + x ^ 2)⁻¹
  have scale : oscillator a m = fun w => (a / m^2) * g (m⁻¹ * w) := by
    funext w
    dsimp [oscillator, g]
    field_simp
    <;> ring
  rw [scale]
  constructor
  · exact (integrable_inv_one_add_mul_sq (inv_ne_zero hm.ne')).const_mul _
  · rw [integral_const_mul, integral_comp_mul_left_Ioi g 0 (inv_pos.mpr hm)]
    simp [g]
    field_simp
    <;> ring

/-- For arbitrary positive masses and nonnegative residues, the half-axis spectral mass is
the inverse-mass sum times π/2, including infinity. Its finiteness is exactly summability. -/
theorem tower_integral_criterion {a m : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hm : ∀ n, 0 < m n) :
    (∫⁻ w in Ioi (0 : ℝ), tower a m w) = ∑' n, ENNReal.ofReal ((π / 2) * (a n / m n)) ∧
    ((∫⁻ w in Ioi (0 : ℝ), tower a m w) ≠ ⊤ ↔ Summable (fun n => a n / m n)) := by
  have integrable (n : ℕ) := (oscillator_integral (a := a n) (hm n)).1
  have nonneg (n : ℕ) (w : ℝ) : 0 ≤ oscillator (a n) (m n) w := by
    exact div_nonneg (ha n) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hmass : (∫⁻ w in Ioi (0 : ℝ), tower a m w) =
      ∑' n, ENNReal.ofReal ((π / 2) * (a n / m n)) := by
    unfold tower
    rw [lintegral_tsum (fun n => ((integrable n).integrableOn.aemeasurable.ennreal_ofReal))]
    apply tsum_congr
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable n).integrableOn
      (Filter.Eventually.of_forall (nonneg n)), (oscillator_integral (hm n)).2]
  refine ⟨hmass, ?_⟩
  rw [hmass]
  let b := fun n => ((π / 2) * (a n / m n)).toNNReal
  change (∑' n, (b n : ℝ≥0∞)) ≠ ⊤ ↔ _
  rw [ENNReal.tsum_coe_ne_top_iff_summable_coe]
  have hb (n) : (b n : ℝ) = (π / 2) * (a n / m n) := by
    apply Real.coe_toNNReal
    exact mul_nonneg (by positivity) (div_nonneg (ha n) (hm n).le)
  simp_rw [hb]
  exact summable_mul_left_iff (by positivity : π / 2 ≠ 0)

end D5.S3.Quantum.StaticExchange.OscillatorInverseMass
