/- GID: D5/S3/Arith/Robin/Analytic/ZeroAbscissaMertensLowerBound
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/ZeroAbscissaMertensLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual zero abscissa controls the lower power envelope of the arithmetic B. -/

import D5.S3.Weil.Mertens.ZeroAbscissaPower
import D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope
import D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope
import D5.S3.Arith.Robin.EulerLayerRootCorrection
import D5.S3.Arith.Robin.LogarithmBounds
import D5.S3.Weil.Mertens.Third
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Transport the unconditional actual psi power estimate through the actual
theta tail and the finite Mertens cancellation. All logarithmic comparisons
are made on explicitly positive eventual domains. The finite cancellation is
supplied by RHSharpArithmeticEnvelope.finite_cancellation. The half-abscissa
argument uses KappaGap's RH/right-strip dichotomy. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set MeasureTheory Asymptotics
open scoped Topology BigOperators
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa zero_re_le_abscissa)
open D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (B)

namespace D5.S3.Arith.Robin.Analytic.ZeroAbscissaMertensLowerBound

private abbrev w := D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity

private def Jtheta (x : ℝ) : ℝ :=
  ∫ t in Ioi x, (Chebyshev.theta t - t) * w t

private def N (x : ℝ) : ℝ :=
  Real.log (Real.log (Chebyshev.theta x)) - Real.log (Real.log x) -
    (Chebyshev.theta x - x) / (x * Real.log x)

private lemma half_le_zero_abscissa : (1 / 2 : ℝ) ≤ zeroAbscissa := by
  classical
  by_cases hRH : RiemannHypothesis
  · obtain ⟨ρ, hρ⟩ :=
      D5.S3.Weil.ZeroInfinitude.ExplicitFormulaObstruction.isNontrivialZero_infinite.nonempty
    simpa only [Zeta23.RH_implies_on_line hRH hρ] using zero_re_le_abscissa hρ
  · have hright : ∃ ρ : ℂ, IsNontrivialZero ρ ∧ 1 / 2 < ρ.re := by
      by_contra! hnone
      apply hRH
      apply D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh
      intro ρ hzero hhalf hone
      have hρ : IsNontrivialZero ρ := ⟨hzero, by linarith, hone⟩
      exact (not_lt_of_ge (hnone ρ hρ)) hhalf
    obtain ⟨ρ, hρ, hhalf⟩ := hright
    exact hhalf.le.trans (zero_re_le_abscissa hρ)

private lemma theta_window :
    ∀ᶠ x : ℝ in atTop,
      x / 2 ≤ Chebyshev.theta x ∧ Chebyshev.theta x ≤ 3 * x / 2 := by
  have hpnt := D5.S3.Arith.Robin.EulerLayerRootCorrection.prime_number_limits.2
  have hlo : ∀ᶠ x : ℝ in atTop, (1 / 2 : ℝ) < Chebyshev.theta x / x :=
    hpnt.eventually (Ioi_mem_nhds (by norm_num))
  have hhi : ∀ᶠ x : ℝ in atTop, Chebyshev.theta x / x < (3 / 2 : ℝ) :=
    hpnt.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [hlo, hhi, eventually_gt_atTop (0 : ℝ)] with x hxlo hxhi hx0
  have hl := (lt_div_iff₀ hx0).mp hxlo
  have hu := (div_lt_iff₀ hx0).mp hxhi
  constructor <;> linarith

private lemma B_tendsto_zero : Tendsto B atTop (𝓝 0) := by
  have hpnt := D5.S3.Arith.Robin.EulerLayerRootCorrection.prime_number_limits.2
  have hratio : Tendsto (fun x : ℝ => Real.log (Chebyshev.theta x / x))
      atTop (𝓝 0) := by
    simpa only [Real.log_one] using hpnt.log (by norm_num : (1 : ℝ) ≠ 0)
  have hsmall : Tendsto
      (fun x : ℝ => Real.log (Chebyshev.theta x / x) / Real.log x) atTop (𝓝 0) :=
    hratio.div_atTop Real.tendsto_log_atTop
  have houter : Tendsto
      (fun x : ℝ => Real.log (1 + Real.log (Chebyshev.theta x / x) / Real.log x))
      atTop (𝓝 0) := by
    simpa only [add_zero, Real.log_one] using
      ((tendsto_const_nhds (x := (1 : ℝ))).add hsmall).log
        (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have heq :
      (fun x : ℝ => Real.log (Real.log (Chebyshev.theta x)) - Real.log (Real.log x))
        =ᶠ[atTop]
      (fun x : ℝ => Real.log (1 + Real.log (Chebyshev.theta x / x) / Real.log x)) := by
    filter_upwards [theta_window, eventually_ge_atTop (4 : ℝ)] with x hxw hx4
    have hx0 : 0 < x := by linarith
    have hθ1 : 1 < Chebyshev.theta x := by linarith [hxw.1]
    have hθ0 : 0 < Chebyshev.theta x := by linarith
    have hlx : 0 < Real.log x := Real.log_pos (by linarith)
    have hlθ : 0 < Real.log (Chebyshev.theta x) := Real.log_pos hθ1
    rw [Real.log_div hθ0.ne' hx0.ne']
    have hid : 1 + (Real.log (Chebyshev.theta x) - Real.log x) / Real.log x =
        Real.log (Chebyshev.theta x) / Real.log x := by
      field_simp [hlx.ne']
      <;> ring
    rw [hid, Real.log_div hlθ.ne' hlx.ne']
  have hdiff : Tendsto
      (fun x : ℝ => Real.log (Real.log (Chebyshev.theta x)) - Real.log (Real.log x))
      atTop (𝓝 0) := houter.congr' heq.symm
  have hE : Tendsto Mertens.E₃ atTop (𝓝 0) :=
    (isLittleO_one_iff ℝ).mp Mertens.E₃.bound'
  change Tendsto (fun x : ℝ => Mertens.E₃ x +
    Real.log (Real.log (Chebyshev.theta x)) - Real.log (Real.log x))
    atTop (𝓝 0)
  simpa only [add_sub_assoc, zero_add] using hE.add hdiff

private lemma B_eventually_lower : ∀ᶠ x : ℝ in atTop, -(1 : ℝ) ≤ B x := by
  exact (B_tendsto_zero.eventually
    (Ioi_mem_nhds (by norm_num : -(1 : ℝ) < 0))).mono (fun _ hx => hx.le)

private lemma B_decomposition {x : ℝ} (hx : 2 ≤ x) :
    B x = Jtheta x + (Mertens.E₃ x + Mertens.E₂p x) + N x := by
  have ht : -Jtheta x =
      Mertens.E₂p x - (Chebyshev.theta x - x) / (x * Real.log x) :=
    (D5.S3.Arith.Robin.ThetaTailRobinWitness.theta_tail_mertens_robin x hx).2.1
  dsimp only [B, N]
  linarith only [ht]

private lemma density_bounds {t : ℝ} (ht : Real.exp 1 ≤ t) :
    0 ≤ w t ∧ w t ≤ 2 / t ^ 2 := by
  have ht0 : 0 < t := (Real.exp_pos 1).trans_le ht
  have hl : 1 ≤ Real.log t := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ht
  have hl0 : 0 < Real.log t := by linarith
  dsimp only [w, D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity]
  refine ⟨div_nonneg (by linarith) (by positivity), ?_⟩
  calc
    (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) ≤
        (2 * Real.log t ^ 2) / (t ^ 2 * Real.log t ^ 2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_nonneg (sub_nonneg.mpr hl)
        (show 0 ≤ 2 * Real.log t + 1 by linarith)]
    _ = 2 / t ^ 2 := by
      field_simp [ht0.ne', hl0.ne']
      <;> ring

private lemma theta_tail_abs {β K R x : ℝ} (hβ : β < 1) (hK : 0 ≤ K)
    (htheta : ∀ t : ℝ, R ≤ t → |Chebyshev.theta t - t| ≤ K * t ^ β)
    (hx2 : 2 ≤ x) (hxR : R ≤ x) (hxe : Real.exp 1 ≤ x) :
    |Jtheta x| ≤ (2 * K / (1 - β)) * x ^ (β - 1) := by
  have hx0 : 0 < x := by linarith
  have hint :=
    (D5.S3.Arith.Robin.ThetaTailRobinWitness.theta_tail_mertens_robin x hx2).1
  have hmajor : IntegrableOn (fun t : ℝ => (2 * K) * t ^ (β - 2)) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : β - 2 < -1) hx0).const_mul (2 * K)
  calc
    |Jtheta x| ≤ ∫ t in Ioi x, |(Chebyshev.theta t - t) * w t| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioi x, (2 * K) * t ^ (β - 2) := by
      apply setIntegral_mono_on hint.abs hmajor measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := hx0.trans ht
      have hw := density_bounds (hxe.trans ht.le)
      rw [abs_mul, abs_of_nonneg hw.1]
      calc
        _ ≤ (K * t ^ β) * (2 / t ^ 2) :=
          mul_le_mul (htheta t (hxR.trans ht.le)) hw.2 hw.1
            (mul_nonneg hK (Real.rpow_nonneg ht0.le _))
        _ = (2 * K) * t ^ (β - 2) := by
          rw [Real.rpow_sub ht0, Real.rpow_two]
          ring
    _ = (2 * K / (1 - β)) * x ^ (β - 1) := by
      rw [integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith : β - 2 < -1) hx0,
        show β - 2 + 1 = β - 1 by ring]
      field_simp [show 1 - β ≠ 0 by linarith, show β - 1 ≠ 0 by linarith]
      <;> ring

private lemma loglog_difference_bound {x y : ℝ} (hx : 4 ≤ x) (hy : x / 2 ≤ y) :
    |Real.log (Real.log y) - Real.log (Real.log x)| ≤
      4 * |y - x| / (x * Real.log x) := by
  have hx1 : 1 < x := by linarith
  have hy1 : 1 < y := by linarith
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hly : 0 < Real.log y := Real.log_pos hy1
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hl4 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hx
  have hlogy : Real.log x / 2 ≤ Real.log y := by
    have hh := Real.log_le_log (by linarith : 0 < x / 2) hy
    rw [Real.log_div hx0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hh
    linarith
  have hdenx : 0 < x * Real.log x := mul_pos hx0 hlx
  have hdeny : 0 < y * Real.log y := mul_pos hy0 hly
  have hden : x * Real.log x / 4 ≤ y * Real.log y := by
    calc
      x * Real.log x / 4 = (x / 2) * (Real.log x / 2) := by ring
      _ ≤ y * Real.log y :=
        mul_le_mul hy hlogy (by positivity) hy0.le
  have hinvx : 1 / (x * Real.log x) ≤ 4 / (x * Real.log x) :=
    div_le_div_of_nonneg_right (by norm_num) hdenx.le
  have hinvy : 1 / (y * Real.log y) ≤ 4 / (x * Real.log x) := by
    apply (div_le_div_iff₀ hdeny hdenx).mpr
    nlinarith
  by_cases heq : x = y
  · subst y
    simp
  · have hu := D5.S3.Arith.Robin.RestrictedDivisorStrictInventory.loglog_tangent
      hx1 hy1 heq
    have hl := D5.S3.Arith.Robin.RestrictedDivisorStrictInventory.loglog_tangent
      hy1 hx1 (fun h => heq h.symm)
    dsimp only [D5.S3.Arith.Robin.ActualRobinClockCovariance.g] at hu hl
    have hupper : Real.log (Real.log y) - Real.log (Real.log x) ≤
        4 * |y - x| / (x * Real.log x) := by
      calc
        _ ≤ (y - x) * (1 / (x * Real.log x)) := hu.le
        _ ≤ |y - x| * (1 / (x * Real.log x)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |y - x| * (4 / (x * Real.log x)) :=
          mul_le_mul_of_nonneg_left hinvx (abs_nonneg _)
        _ = _ := by ring
    have hlower : -(Real.log (Real.log y) - Real.log (Real.log x)) ≤
        4 * |y - x| / (x * Real.log x) := by
      calc
        _ = Real.log (Real.log x) - Real.log (Real.log y) := by ring
        _ ≤ (x - y) * (1 / (y * Real.log y)) := hl.le
        _ ≤ |x - y| * (1 / (y * Real.log y)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ = |y - x| * (1 / (y * Real.log y)) := by rw [abs_sub_comm x y]
        _ ≤ |y - x| * (4 / (x * Real.log x)) :=
          mul_le_mul_of_nonneg_left hinvy (abs_nonneg _)
        _ = _ := by ring
    exact abs_le.mpr ⟨by linarith, hupper⟩

private lemma nonlinear_lower {β K x : ℝ} (hK : 0 ≤ K) (hx : 4 ≤ x)
    (hxe : Real.exp 1 ≤ x) (hwindow : x / 2 ≤ Chebyshev.theta x)
    (htheta : |Chebyshev.theta x - x| ≤ K * x ^ β) :
    -(5 * K) * x ^ (β - 1) ≤ N x := by
  have hx0 : 0 < x := by linarith
  have hl : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hxe
  have hl0 : 0 < Real.log x := by linarith
  have hden : x ≤ x * Real.log x := by nlinarith
  have hden0 : 0 < x * Real.log x := mul_pos hx0 hl0
  have hp : 0 ≤ K * x ^ β := mul_nonneg hK (Real.rpow_nonneg hx0.le _)
  have hdiff :
      |Real.log (Real.log (Chebyshev.theta x)) - Real.log (Real.log x)| ≤
        (4 * K) * x ^ (β - 1) := by
    calc
      _ ≤ 4 * |Chebyshev.theta x - x| / (x * Real.log x) :=
        loglog_difference_bound hx hwindow
      _ ≤ 4 * (K * x ^ β) / (x * Real.log x) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htheta (by norm_num))
          hden0.le
      _ ≤ 4 * (K * x ^ β) / x :=
        div_le_div_of_nonneg_left (by positivity) hx0 hden
      _ = (4 * K) * x ^ (β - 1) := by
        rw [Real.rpow_sub_one hx0.ne']
        ring
  have hlinear : |(Chebyshev.theta x - x) / (x * Real.log x)| ≤
      K * x ^ (β - 1) := by
    calc
      _ = |Chebyshev.theta x - x| / (x * Real.log x) := by
        rw [abs_div, abs_of_pos hden0]
      _ ≤ (K * x ^ β) / (x * Real.log x) :=
        div_le_div_of_nonneg_right htheta hden0.le
      _ ≤ (K * x ^ β) / x := div_le_div_of_nonneg_left hp hx0 hden
      _ = K * x ^ (β - 1) := by
        rw [Real.rpow_sub_one hx0.ne']
        ring
  have hd := (abs_le.mp hdiff).1
  have he := (abs_le.mp hlinear).2
  dsimp only [N]
  nlinarith only [hd, he]

private theorem lower_power_of_psi {β C X : ℝ} (hβhalf : (1 / 2 : ℝ) < β)
    (hβone : β < 1)
    (hpsi : ∀ t : ℝ, X ≤ t → |Chebyshev.psi t - t| ≤ C * t ^ β) :
    ∃ A T : ℝ, 0 ≤ A ∧ 2 ≤ T ∧
      ∀ x : ℝ, T ≤ x → -A * x ^ (β - 1) ≤ B x := by
  obtain ⟨K, R, hK, hR, htheta⟩ :=
    D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope.theta_power_bound hβhalf hpsi
  obtain ⟨W, hW⟩ := eventually_atTop.mp theta_window
  have hβgap : 0 < 1 - β := by linarith
  let A : ℝ := 2 * K / (1 - β) + 5 * K + 4
  let T : ℝ := max (max R W) (max 4 (Real.exp 1))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hTR : R ≤ T := (le_max_left R W).trans (le_max_left _ _)
  have hTW : W ≤ T := (le_max_right R W).trans (le_max_left _ _)
  have hT4 : 4 ≤ T := (le_max_left 4 (Real.exp 1)).trans (le_max_right _ _)
  have hTe : Real.exp 1 ≤ T := (le_max_right 4 (Real.exp 1)).trans (le_max_right _ _)
  refine ⟨A, T, hA, hR.trans hTR, ?_⟩
  intro x hx
  have hxR : R ≤ x := hTR.trans hx
  have hx4 : 4 ≤ x := hT4.trans hx
  have hx2 : 2 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxe : Real.exp 1 ≤ x := hTe.trans hx
  have hJ := theta_tail_abs hβone hK htheta hx2 hxR hxe
  have hN := nonlinear_lower hK hx4 hxe (hW x (hTW.trans hx)).1 (htheta x hxR)
  have hF := D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.finite_cancellation hx2
  have hpower : (1 : ℝ) / x ≤ x ^ (β - 1) := by
    simpa only [Real.rpow_neg_one, one_div] using
      Real.rpow_le_rpow_of_exponent_le hx1 (show (-1 : ℝ) ≤ β - 1 by linarith)
  have hfour : 4 / x ≤ 4 * x ^ (β - 1) := by
    calc
      4 / x = 4 * (1 / x) := by ring
      _ ≤ 4 * x ^ (β - 1) := mul_le_mul_of_nonneg_left hpower (by norm_num)
  have hJlo := (abs_le.mp hJ).1
  have hFlo := (abs_le.mp hF).1
  rw [B_decomposition hx2]
  dsimp only [A]
  nlinarith only [hJlo, hFlo, hN, hfour]

/-- Unconditionally, the actual zero abscissa gives every positive-slack
lower power envelope of the existing arithmetic B. -/
theorem actual_B_zero_abscissa_lower_power :
    ∀ epsilon : Real, 0 < epsilon → ∃ C T : Real,
      0 ≤ C ∧ 2 ≤ T ∧ ∀ x : Real, T ≤ x →
        -C * Real.rpow x
          (D5.S3.Arith.Robin.ForwardKernel.KappaGap.zeroAbscissa - 1 + epsilon) ≤
          D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.B x := by
  intro epsilon hepsilon
  let q : ℝ := zeroAbscissa - 1 + epsilon
  by_cases hq : 0 ≤ q
  · obtain ⟨T, hT⟩ := eventually_atTop.mp B_eventually_lower
    refine ⟨1, max 2 T, by norm_num, le_max_left _ _, ?_⟩
    intro x hx
    have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
    have hp : 1 ≤ x ^ q := Real.one_le_rpow (by linarith) hq
    have hb := hT x ((le_max_right _ _).trans hx)
    change -(1 : ℝ) * x ^ q ≤ B x
    nlinarith
  · have hqneg : q < 0 := lt_of_not_ge hq
    let β : ℝ := zeroAbscissa + epsilon / 2
    have hβhalf : (1 / 2 : ℝ) < β := by
      dsimp only [β]
      linarith [half_le_zero_abscissa]
    have hβone : β < 1 := by
      dsimp only [β]
      have hq' : zeroAbscissa - 1 + epsilon < 0 := hqneg
      linarith
    obtain ⟨C, hC⟩ :=
      D5.S3.Weil.Mertens.ZeroAbscissaPower.actual_zero_abscissa_power_bound
        (epsilon / 2) (by linarith)
    have hpsi : ∀ x : ℝ, (2 : ℝ) ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ β := by
      simpa only [β] using hC
    obtain ⟨A, T, hA, hT, hbound⟩ := lower_power_of_psi hβhalf hβone hpsi
    refine ⟨A, T, hA, hT, ?_⟩
    intro x hx
    have hx1 : 1 ≤ x := by linarith
    have hexponent : β - 1 ≤ q := by dsimp only [β, q]; linarith
    have hp : x ^ (β - 1) ≤ x ^ q :=
      Real.rpow_le_rpow_of_exponent_le hx1 hexponent
    change -A * x ^ q ≤ B x
    exact (mul_le_mul_of_nonpos_left hp (by linarith : -A ≤ 0)).trans (hbound x hx)

end D5.S3.Arith.Robin.Analytic.ZeroAbscissaMertensLowerBound
