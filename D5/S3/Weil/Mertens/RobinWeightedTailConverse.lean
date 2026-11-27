/- GID: D5/S3/Weil/Mertens/RobinWeightedTailConverse
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/RobinWeightedTailConverse
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   utility: none
   digest: Critical-exponent negative peaks and an RH converse for the exact Robin weighted tail. -/

import D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope
import D5.S3.Weil.Mertens.CriticalThetaTailPeak
import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction

/-!
# The one-sided converse for the exact Robin weighted tail

The existing theta pole theorem produces positive peaks of the
negative activation tail. The prime-power correction between the
theta and psi tails has bounded normalized size. It therefore
vanishes at the scale of each off-line zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (psiErrorKernel)
open D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope
  (D Jpsi S A w weighted_eq tails A_data)
open D5.S3.Weil.Mertens.WeightedTailTransport (weightedTail)
open D5.S3.Weil.Mertens

namespace D5.S3.Weil.Mertens.RobinWeightedTailConverse

private theorem psi_tail_eq_weightedTail (x : ℝ) :
    Jpsi x = weightedTail psiErrorKernel x := by
  unfold Jpsi weightedTail
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => (weighted_eq t).symm

private theorem theta_tail_eq {u : ℝ} (hu : Real.log 2 ≤ u) :
    ActualThetaTailLaplace.f u = -(Jpsi (Real.exp u) - S (Real.exp u)) := by
  have hx : 2 ≤ Real.exp u := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr hu
  have hi := tails hx
  rw [ActualThetaTailLaplace.tail_substitution]
  unfold ActualThetaTailLaplace.F Jpsi S
  rw [← integral_sub hi.1 hi.2.1]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring

private theorem normalized_power_correction :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x → D x * S x ≤ C := by
  obtain ⟨K, hK⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let C := max K 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨2 * C, by positivity, ?_⟩
  intro x hx
  have hx1 : 1 < x := by linarith
  have hD : 0 < D x := mul_pos (Real.sqrt_pos.mpr (by linarith)) (Real.log_pos hx1)
  have hA := A_data hx1
  have hAi : IntegrableOn (fun t => Real.sqrt t * w t) (Ioi x) := hA.1
  have hAb : A x ≤ 2 / D x := hA.2.2
  have hS : S x ≤ C * A x := by
    unfold S A
    rw [← integral_const_mul]
    refine setIntegral_mono_on (tails hx).2.1 (hAi.const_mul C) measurableSet_Ioi ?_
    intro t ht
    have hlog : 0 < Real.log t := Real.log_pos (hx1.trans ht)
    have hw : 0 ≤ w t := by
      unfold w D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity
      positivity
    have hgap := (hK t).trans (mul_le_mul_of_nonneg_right (le_max_left K 0) (Real.sqrt_nonneg t))
    change (Chebyshev.psi t - Chebyshev.theta t) * w t ≤ C * (Real.sqrt t * w t)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hgap hw
  calc
    _ ≤ D x * (C * (2 / D x)) :=
      mul_le_mul_of_nonneg_left (hS.trans (mul_le_mul_of_nonneg_left hAb hC)) hD.le
    _ = _ := by field_simp [hD.ne']

private theorem normalized_log_scale (β u : ℝ) :
    Real.exp ((1 / 2 - β) * u) * D (Real.exp u) = u * Real.exp ((1 - β) * u) := by
  have hsqrt : Real.sqrt (Real.exp u) = Real.exp (u / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  unfold D
  rw [Real.log_exp, hsqrt, ← mul_assoc, ← Real.exp_add,
    show (1 / 2 - β) * u + u / 2 = (1 - β) * u by ring]
  ring

private theorem scaled_decay {β : ℝ} (hβ : 1 / 2 < β) (C : ℝ) :
    Tendsto (fun u : ℝ => Real.exp ((1 / 2 - β) * u) * C) atTop (𝓝 0) := by
  have h : Tendsto (fun u : ℝ => Real.exp ((1 / 2 - β) * u)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  simpa only [zero_mul] using h.mul_const C

/-- Every off-line zero gives negative excursions of the normalized
complete Robin tail with all strict constants below its full coefficient. -/
theorem normalized_weighted_tail_negative_peaks {ρ : ℂ}
    (hβ : 1 / 2 < ρ.re) (hβ1 : ρ.re < 1) (hzero : riemannZeta ρ = 0) :
    let m := analyticOrderNatAt riemannZeta ρ
    0 < m ∧
      ∀ c : ℝ, 0 ≤ c → c < (m : ℝ) / (‖ρ‖ * ‖ρ - 1‖) →
      ∀ T : ℝ, ∃ u : ℝ, max T (Real.log 2) < u ∧
        c < -(Real.exp ((1 / 2 - ρ.re) * u) *
          (D (Real.exp u) * weightedTail psiErrorKernel (Real.exp u))) := by
  dsimp only
  obtain ⟨hm, _, hpeaks⟩ := CriticalThetaTailPeak.critical_theta_tail_peak hβ hβ1 hzero
  refine ⟨hm, ?_⟩
  intro c hc hcl T
  obtain ⟨C, _, hC⟩ := normalized_power_correction
  let a := (analyticOrderNatAt riemannZeta ρ : ℝ) / (‖ρ‖ * ‖ρ - 1‖)
  let c₁ := (c + a) / 2
  have hca : c < a := hcl
  have hc₁ : 0 ≤ c₁ := by dsimp [c₁]; linarith
  have hc₁a : c₁ < a := by dsimp [c₁]; linarith
  have hgap : 0 < c₁ - c := by dsimp [c₁]; linarith
  obtain ⟨V, hV⟩ := eventually_atTop.mp
    ((scaled_decay hβ C).eventually (gt_mem_nhds hgap))
  obtain ⟨u, hu, hbig⟩ := hpeaks c₁ hc₁ hc₁a (max T V)
  have hu₂ : Real.log 2 ≤ u := (le_max_right _ _).trans hu.le
  have hx : 2 ≤ Real.exp u := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr hu₂
  let e := Real.exp ((1 / 2 - ρ.re) * u)
  have he0 : 0 ≤ e := Real.exp_nonneg _
  have hV' : e * C < c₁ - c :=
    hV u (((le_max_right T V).trans (le_max_left _ _)).trans hu.le)
  have herror : e * (D (Real.exp u) * S (Real.exp u)) < c₁ - c :=
    (mul_le_mul_of_nonneg_left (hC _ hx) he0).trans_lt hV'
  have htheta :
      ActualThetaTailLaplace.f u = S (Real.exp u) - Jpsi (Real.exp u) := by
    rw [theta_tail_eq hu₂]
    ring
  have hbig' :
      c₁ < e * (D (Real.exp u) * (S (Real.exp u) - Jpsi (Real.exp u))) := by
    simpa only [htheta, ← normalized_log_scale, mul_assoc, e] using hbig
  refine ⟨u, lt_of_le_of_lt (max_le_max (le_max_left T V) le_rfl) hu, ?_⟩
  rw [← psi_tail_eq_weightedTail]
  change c < -(e * (D (Real.exp u) * Jpsi (Real.exp u)))
  rw [mul_sub, mul_sub] at hbig'
  linarith only [hbig', herror]

/-- An eventual constant lower bound on the exact normalized arithmetic
tail appearing in the effective Robin inequality implies RH. -/
theorem rh_of_eventually_normalized_weighted_tail_lower
    (h : ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, -C ≤ D x * weightedTail psiErrorKernel x) :
    RiemannHypothesis := by
  apply D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh
  intro ρ hz hβ hβ1
  obtain ⟨hm, hpeaks⟩ := normalized_weighted_tail_negative_peaks hβ hβ1 hz
  let a : ℝ := (analyticOrderNatAt riemannZeta ρ : ℝ) / (‖ρ‖ * ‖ρ - 1‖)
  have hρ0 : ρ ≠ 0 := Complex.ne_zero_of_re_pos (by linarith)
  have hρ1 : ρ - 1 ≠ 0 := by
    intro hh
    have hreal := congrArg Complex.re (sub_eq_zero.mp hh)
    simp at hreal
    linarith
  have ha : 0 < a := div_pos (by exact_mod_cast hm)
    (mul_pos (norm_pos_iff.mpr hρ0) (norm_pos_iff.mpr hρ1))
  obtain ⟨C, hC⟩ := h
  have hlarge := Real.tendsto_exp_atTop.eventually hC
  have hsmall := (scaled_decay hβ C).eventually
    (gt_mem_nhds (show (0 : ℝ) < a / 2 by positivity))
  obtain ⟨V, hV⟩ := eventually_atTop.mp (hlarge.and hsmall)
  obtain ⟨u, hu, hpeak⟩ := hpeaks (a / 2) (by positivity) (by linarith) V
  have hV' := hV u ((le_max_left V _).trans hu.le)
  have hbound := mul_le_mul_of_nonneg_left hV'.1 (Real.exp_nonneg ((1 / 2 - ρ.re) * u))
  linarith only [hbound, hV'.2, hpeak,
    show Real.exp ((1 / 2 - ρ.re) * u) * (-C) =
      -(Real.exp ((1 / 2 - ρ.re) * u) * C) by ring]

end D5.S3.Weil.Mertens.RobinWeightedTailConverse

#print axioms D5.S3.Weil.Mertens.RobinWeightedTailConverse.rh_of_eventually_normalized_weighted_tail_lower
