/- GID: D5/S3/Analytic/Laplace/SignedWindowMoments
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/SignedWindowMoments
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   utility: none
   digest: Long upper windows control actual signed Laplace derivatives at a common order. -/

import D5.S3.Analytic.Laplace.SignedMoments
import D5.S3.Analytic.Laplace.CriticalGammaWindow

/-! # Signed moments on upper windows

A pointwise upper bound is used only on the given window. Outside the window,
the absolute exponential growth bound and the two gamma tails supply control.
The same order works for every imaginary part of the complex center.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Filter Set Real
open scoped Topology
open D5.S3.Analytic.Laplace.PairedPoleRegularity (laplace)

namespace D5.S3.Analytic.Laplace.SignedWindowMoments

/-- The elementary global growth bound supplies actual absolute convergence. -/
theorem growth_convergence {g : ℝ → ℝ} {M σ : ℝ} (hg : Measurable g)
    (hM : ∀ u, 0 ≤ u → |g u| ≤ M * exp (2 * u)) (hσ : 2 < σ) :
    IntegrableOn (fun u => g u * exp (-σ * u)) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have hi := (integrableOn_exp_mul_Ioi (by linarith : -(σ - 2) < 0) 0).const_mul M
  apply hi.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  calc
    |g u| * exp (-σ * u) ≤ M * exp (2 * u) * exp (-σ * u) :=
      mul_le_mul_of_nonneg_right (hM u hu.le) (exp_pos _).le
    _ = M * exp (-(σ - 2) * u) := by
      rw [mul_assoc, ← exp_add]
      congr 2
      ring

private theorem positive_integrable {g : ℝ → ℝ} {M σ : ℝ}
    (hg : Measurable g) (hM : ∀ u, 0 ≤ u → |g u| ≤ M * exp (2 * u))
    (hσ : 2 < σ) (k : ℕ) :
    IntegrableOn (fun u => max (g u) 0 * CriticalGammaWindow.moment k σ u) (Ioi 0) := by
  have hi := (SignedMoments.absolute_moment_integrable hg
    (fun t ht => growth_convergence hg hM ht) hσ k).div_const (k.factorial : ℝ)
  change IntegrableOn
    (fun u => (u ^ k * |g u| * exp (-σ * u)) / (k.factorial : ℝ)) (Ici 0) at hi
  apply (hi.mono_set Ioi_subset_Ici_self).mono' (by
    dsimp [CriticalGammaWindow.moment]
    fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := hu.le
  have hk : 0 ≤ CriticalGammaWindow.moment k σ u := by
    unfold CriticalGammaWindow.moment
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) hk)]
  calc
    _ ≤ |g u| * CriticalGammaWindow.moment k σ u :=
      mul_le_mul_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _)) hk
    _ = _ := by unfold CriticalGammaWindow.moment; rw [neg_mul]; ring

private theorem window_positive_mass {g : ℝ → ℝ} {M σ θ C U b : ℝ}
    (hg : Measurable g) (hM : ∀ u, 0 ≤ u → |g u| ≤ M * exp (2 * u))
    (hσ : 2 < σ) (hθσ : θ < σ) (hU : 0 < U) (k : ℕ)
    (hwindow : ∀ u ∈ Icc U (b * U), g u ≤ C * exp (θ * u)) :
    (∫ u in Icc U (b * U),
      max (g u) 0 * CriticalGammaWindow.moment k σ u) ≤
      |C| * (σ - θ)⁻¹ ^ (k + 1) := by
  have hr : 0 < σ - θ := sub_pos.mpr hθσ
  have hsub : Icc U (b * U) ⊆ Ioi (0 : ℝ) := fun u hu => hU.trans_le hu.1
  have hq : IntegrableOn (fun u => |C| * CriticalGammaWindow.moment k (σ - θ) u)
      (Ioi 0) := (CriticalGammaWindow.moment_integrable k hr).const_mul |C|
  have hp := positive_integrable hg hM hσ k
  have hbound (u : ℝ) (hu : u ∈ Icc U (b * U)) :
      max (g u) 0 * CriticalGammaWindow.moment k σ u ≤
        |C| * CriticalGammaWindow.moment k (σ - θ) u := by
    have hu0 : 0 ≤ u := (hsub hu).le
    have hk : 0 ≤ CriticalGammaWindow.moment k σ u := by
      unfold CriticalGammaWindow.moment
      positivity
    have hg0 : max (g u) 0 ≤ |C| * exp (θ * u) := by
      apply max_le
      · exact (hwindow u hu).trans
          (mul_le_mul_of_nonneg_right (le_abs_self C) (exp_pos _).le)
      · positivity
    calc
      _ ≤ |C| * exp (θ * u) * CriticalGammaWindow.moment k σ u :=
        mul_le_mul_of_nonneg_right hg0 hk
      _ = _ := by
        unfold CriticalGammaWindow.moment
        have he : exp (θ * u) * exp (-(σ * u)) = exp (-((σ - θ) * u)) := by
          rw [← exp_add]
          congr 1
          ring
        calc
          _ = (|C| * u ^ k / k.factorial) *
            (exp (θ * u) * exp (-(σ * u))) := by ring
          _ = _ := by rw [he]; ring
  calc
    _ ≤ ∫ u in Icc U (b * U), |C| * CriticalGammaWindow.moment k (σ - θ) u :=
      setIntegral_mono_on (hp.mono_set hsub) (hq.mono_set hsub) measurableSet_Icc hbound
    _ ≤ ∫ u in Ioi (0 : ℝ), |C| * CriticalGammaWindow.moment k (σ - θ) u := by
      apply setIntegral_mono_set hq _ (Eventually.of_forall hsub)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 ≤ u := hu.le
      unfold CriticalGammaWindow.moment
      positivity
    _ = _ := by rw [integral_const_mul, CriticalGammaWindow.moment_integral k hr]

/-- Upper control on a single long window bounds every complex moment at the same order. -/
theorem moment_bound_on_window {g : ℝ → ℝ} {M σ θ C U h b : ℝ}
    (hg : Measurable g) (hM : ∀ u, 0 ≤ u → |g u| ≤ M * exp (2 * u))
    (hθ : 0 ≤ θ) (hθσ : θ < σ) (hh : 1 < h) (hb : h < b)
    (hsign : 2 < σ * (1 - h / b))
    (hleft : 0 ≤ σ * (h * log h - h + 1) - 2)
    (hright : 0 ≤ σ * (b - h - h * log (b / h)) - 2 * b)
    (hU : 0 < U)
    (hwindow : ∀ u ∈ Icc U (b * U), g u ≤ C * exp (θ * u))
    (z : ℂ) (hz : z.re = σ) :
    let k := ⌊σ * h * U⌋₊
    (‖iteratedDeriv k (laplace g) z‖ +
        ∫ u in Ici (0 : ℝ), u ^ k * g u * exp (-σ * u)) / k.factorial ≤
      (2 * (|C| / (σ - θ) + M * (1 / σ + b / (h * σ)))) * (σ - θ)⁻¹ ^ k := by
  have hh0 : 0 < h := by linarith
  have hb0 : 0 < b := hh0.trans hb
  have hratio : 0 < h / b := div_pos hh0 hb0
  have hfactor : 0 < 1 - h / b := sub_pos.mpr ((div_lt_one hb0).mpr hb)
  have hσ : 2 < σ := by
    by_cases hs : 0 < σ
    · have hlt := mul_lt_of_lt_one_right hs (by linarith : 1 - h / b < 1)
      linarith
    · have hn := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hs) hfactor.le
      linarith
  let k := ⌊σ * h * U⌋₊
  let p : ℝ → ℝ := fun u => max (g u) 0 * CriticalGammaWindow.moment k σ u
  let S := Ioi (0 : ℝ) \ Icc U (b * U)
  have hp : IntegrableOn p (Ioi 0) := positive_integrable hg hM hσ k
  have ht := (CriticalGammaWindow.adjustable_window_off_mass hh hb).2
    hsign hU hg hM
  change IntegrableOn (fun u => |g u| * CriticalGammaWindow.moment k σ u) S ∧
    (∫ u in S, |g u| * CriticalGammaWindow.moment k σ u) ≤ _ at ht
  have hm0 : 0 ≤ M := (abs_nonneg (g 0)).trans (by simpa using hM 0 le_rfl)
  have hσ0 : 0 < σ := by linarith
  have hsmall (u : ℝ) (hu : u ∈ S) :
      p u ≤ |g u| * CriticalGammaWindow.moment k σ u := by
    have hu0 : 0 ≤ u := hu.1.le
    apply mul_le_mul_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _))
    unfold CriticalGammaWindow.moment
    positivity
  have htail : (∫ u in S, p u) ≤
      M * σ⁻¹ ^ k * (1 / σ + b / (h * σ)) := by
    apply (setIntegral_mono_on (hp.mono_set sdiff_subset) ht.1
      (measurableSet_Ioi.diff measurableSet_Icc) hsmall).trans
    apply ht.2.trans
    have hl : exp (-(σ * (h * log h - h + 1) - 2) * U) ≤ 1 :=
      exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hleft) hU.le)
    have hr : exp (-(σ * (b - h - h * log (b / h)) - 2 * b) * U) ≤ 1 :=
      exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hright) hU.le)
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ M * σ⁻¹ ^ k)
    exact add_le_add (div_le_div_of_nonneg_right hl hσ0.le)
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ b / (h * σ)))
  have hinside := window_positive_mass hg hM hσ hθσ hU k hwindow
  have hsub : Icc U (b * U) ⊆ Ioi (0 : ℝ) := fun u hu => hU.trans_le hu.1
  have hsplit : (∫ u in Icc U (b * U), p u) + (∫ u in S, p u) =
      ∫ u in Ioi (0 : ℝ), p u := by
    simpa only [inter_eq_right.mpr hsub, S] using
      integral_inter_add_sdiff (t := Icc U (b * U)) measurableSet_Icc hp
  have hr : 0 < σ - θ := sub_pos.mpr hθσ
  have hinv : σ⁻¹ ≤ (σ - θ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hr (by linarith : σ - θ ≤ σ)
  have hpow : σ⁻¹ ^ k ≤ (σ - θ)⁻¹ ^ k :=
    pow_le_pow_left₀ (inv_nonneg.mpr hσ0.le) hinv k
  have htotal : (∫ u in Ioi (0 : ℝ), p u) ≤
      (|C| / (σ - θ) + M * (1 / σ + b / (h * σ))) * (σ - θ)⁻¹ ^ k := by
    rw [← hsplit]
    apply (add_le_add hinside htail).trans
    calc
      _ ≤ |C| * (σ - θ)⁻¹ ^ (k + 1) +
          M * (σ - θ)⁻¹ ^ k * (1 / σ + b / (h * σ)) := by gcongr
      _ = _ := by rw [pow_succ]; ring
  have hc : ∀ t : ℝ, 2 < t →
      IntegrableOn (fun u => g u * exp (-t * u)) (Ici 0) :=
    fun t ht => growth_convergence hg hM ht
  have hstart := SignedMoments.moment_norm_add_real_le (h := g) (z := z) k
  rw [hz] at hstart
  have hfac : 0 < (k.factorial : ℝ) := by positivity
  have hdiv := div_le_div_of_nonneg_right hstart hfac.le
  have hnormalize :
      (2 * ∫ u in Ici (0 : ℝ), u ^ k * max (g u) 0 * exp (-σ * u)) /
          (k.factorial : ℝ) = 2 * ∫ u in Ioi (0 : ℝ), p u := by
    calc
      _ = 2 * ((∫ u in Ici (0 : ℝ), u ^ k * max (g u) 0 * exp (-σ * u)) /
          (k.factorial : ℝ)) := by ring
      _ = 2 * ∫ u in Ici (0 : ℝ),
          (u ^ k * max (g u) 0 * exp (-σ * u)) / (k.factorial : ℝ) :=
        congrArg (fun x : ℝ => 2 * x)
          (integral_div (μ := volume.restrict (Ici (0 : ℝ)))
            (k.factorial : ℝ) (fun u : ℝ =>
              u ^ k * max (g u) 0 * exp (-σ * u))).symm
      _ = _ := by
        rw [integral_Ici_eq_integral_Ioi]
        congr 1
        apply integral_congr_ae
        filter_upwards [] with u
        dsimp [p, CriticalGammaWindow.moment]
        rw [neg_mul]
        ring
  rw [hnormalize] at hdiv
  have hderiv : ‖iteratedDeriv k (laplace g) z‖ = ‖SignedMoments.moment g k z‖ := by
    rw [SignedMoments.iteratedDeriv_laplace hg hc (by simpa [hz] using hσ) k]
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  change (‖iteratedDeriv k (laplace g) z‖ + _) / _ ≤ _
  rw [hderiv]
  apply hdiv.trans
  nlinarith [htotal]

/-- Every width admits a fixed real center and an order at least the window cutoff. -/
theorem long_window_moment_bound {g : ℝ → ℝ} {M θ C b : ℝ}
    (hg : Measurable g) (hM : ∀ u, 0 ≤ u → |g u| ≤ M * exp (2 * u))
    (hθ : 0 ≤ θ) (hb : 1 < b) :
    ∃ σ K : ℝ, 2 < σ ∧ θ < σ ∧ 0 ≤ K ∧
      ∀ U : ℝ, 1 ≤ U →
      (∀ u ∈ Icc U (b * U), g u ≤ C * exp (θ * u)) →
      let k := ⌊σ * ((1 + b) / 2) * U⌋₊
      U ≤ k ∧ ∀ z : ℂ, z.re = σ →
        (‖iteratedDeriv k (laplace g) z‖ +
            ∫ u in Ici (0 : ℝ), u ^ k * g u * exp (-σ * u)) / k.factorial ≤
          K * (σ - θ)⁻¹ ^ k := by
  let h := (1 + b) / 2
  have hh : 1 < h := by dsimp [h]; linarith
  have hhb : h < b := by dsimp [h]; linarith
  obtain ⟨σ, ⟨hsign, hL, hR⟩, hσlarge⟩ :=
    (((CriticalGammaWindow.adjustable_window_off_mass hh hhb).1 0).and
      (eventually_gt_atTop (max (2 : ℝ) θ))).exists
  have hσ : 2 < σ := (le_max_left _ _).trans_lt hσlarge
  have hθσ : θ < σ := (le_max_right _ _).trans_lt hσlarge
  let K := 2 * (|C| / (σ - θ) + M * (1 / σ + b / (h * σ)))
  have hm0 : 0 ≤ M := (abs_nonneg (g 0)).trans (by simpa using hM 0 le_rfl)
  have hσ0 : 0 < σ := by linarith
  have hh0 : 0 < h := by linarith
  have hb0 : 0 < b := by linarith
  have hr : 0 < σ - θ := sub_pos.mpr hθσ
  refine ⟨σ, K, hσ, hθσ, by dsimp [K]; positivity, ?_⟩
  intro U hU hwindow
  have hU0 : 0 < U := by linarith
  let k := ⌊σ * h * U⌋₊
  have hσh : 2 < σ * h := by nlinarith
  have hfloor := Nat.lt_floor_add_one (σ * h * U)
  have hk : U ≤ (k : ℝ) := by
    dsimp [k]
    nlinarith [mul_le_mul_of_nonneg_right hσh.le hU0.le]
  refine ⟨hk, fun z hz => ?_⟩
  exact moment_bound_on_window hg hM hθ hθσ hh hhb hsign hL.le hR.le hU0 hwindow z hz

end D5.S3.Analytic.Laplace.SignedWindowMoments
