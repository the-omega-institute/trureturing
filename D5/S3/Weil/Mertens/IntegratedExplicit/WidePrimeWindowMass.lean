/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/WidePrimeWindowMass
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/WidePrimeWindowMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform prime-only window mass bounds on wide real intervals. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth
import D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean
import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction

/-! A nonnegative prime-tail integrand transfers power-window bounds to wide intervals. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
namespace D5.S3.Weil.Mertens.IntegratedExplicit.WidePrimeWindowMass

open PrimeOnlyTailCorrection (primeTail prime_integrable)
open D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
open PrimeWindowPoleGrowth (off_line_zero_forces_window_mass)
open RHPrimeWindowMean (prime_tail_logarithmic_mass_of_rh)

private lemma wide_window_power_lower_bound {b : ℝ} (hb : 1 < b)
    {ρ : ℂ} (hzero : riemannZeta ρ = 0) {η : ℝ} (hη0 : 0 < η) (hη : η < ρ.re - 1 / 2) :
    ∃ S : ℝ, ∀ B : ℝ, S ≤ B → ∀ A : ℝ, 2 ≤ A → A ^ b ≤ B →
      B ^ η ≤ ∫ x in A..B, max (-primeTail x) 0 / Real.sqrt x := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hβ : 1 / 2 < ρ.re := by linarith
  let ε : ℝ := b * (ρ.re - 1 / 2 - η)
  have hε : 0 < ε := mul_pos hb0 (sub_pos.mpr hη)
  have hpole := off_line_zero_forces_window_mass hzero hβ hb hε
  have hpull := (tendsto_rpow_atTop (inv_pos.mpr hb0)).eventually hpole
  obtain ⟨S, hS⟩ := eventually_atTop.mp hpull
  refine ⟨S, ?_⟩
  intro B hSB A hA hAB
  have hA1 : 1 ≤ A := by linarith
  have hB0 : 0 ≤ B :=
    (zero_le_one.trans hA1).trans ((Real.self_le_rpow_of_one_le hA1 hb.le).trans hAB)
  let Y := B ^ b⁻¹
  have hYb : Y ^ b = B := Real.rpow_inv_rpow hB0 hb0.ne'
  have hAY : A ≤ Y := by
    unfold Y
    simpa only [Real.rpow_rpow_inv (zero_le_one.trans hA1) hb0.ne'] using
      Real.rpow_le_rpow (Real.rpow_nonneg (zero_le_one.trans hA1) _) hAB (inv_nonneg.mpr hb0.le)
  have hYB : Y ≤ B :=
    (Real.self_le_rpow_of_one_le (hA1.trans hAY) hb.le).trans_eq hYb
  have hcont : ContinuousOn (fun x => max (-primeTail x) 0 / Real.sqrt x) (Ici 1) :=
    ((prime_integrable.continuousOn_Ici_primitive_Ioi.neg).sup
      continuousOn_const).div Real.continuous_sqrt.continuousOn
        (fun _ hx => (Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)).ne')
  have hint : IntervalIntegrable (fun x => max (-primeTail x) 0 / Real.sqrt x) volume A B :=
    (hcont.mono (by
      rw [uIcc_of_le (hAY.trans hYB)]
      exact fun _ hx => hA1.trans hx.1)).intervalIntegrable
  have hmass := intervalIntegral.integral_mono_interval hAY hYB (le_refl B)
    (ae_of_all _ fun x => div_nonneg (le_max_right _ _) (Real.sqrt_nonneg x)) hint
  have hpow : B ^ η = Y ^ (b * (ρ.re - 1 / 2) - ε) := by
    dsimp [Y, ε]
    rw [← Real.rpow_mul hB0]
    congr 1
    field_simp
    <;> ring
  have hwindow := hS B hSB
  change Y ^ (b * (ρ.re - 1 / 2) - ε) ≤
    ∫ x in Y..Y ^ b, max (-primeTail x) 0 / Real.sqrt x at hwindow
  rw [hYb, ← hpow] at hwindow
  exact hwindow.trans hmass

/-- The prime-only negative mass has a uniform logarithmic lower bound on wide
real intervals. Failure of RH forces the excess above that logarithm to diverge
uniformly with the right endpoint. -/
theorem prime_tail_wide_window_mass (b : ℝ) (hb : 1 < b) :
    let tail := primeTail
    ((¬ RiemannHypothesis) → ∀ K : ℝ, ∃ S : ℝ,
      ∀ B : ℝ, S ≤ B → ∀ A : ℝ, 2 ≤ A → A ^ b ≤ B →
        K ≤ (∫ x in A..B, max (-tail x) 0 / Real.sqrt x) - 2 * Real.log (B / A)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ A B : ℝ, 2 ≤ A → A ^ b ≤ B →
      2 * Real.log (B / A) - C ≤ ∫ x in A..B, max (-tail x) 0 / Real.sqrt x) := by
  dsimp only
  have ordered {A B : ℝ} (hA : 2 ≤ A) (hAB : A ^ b ≤ B) : A ≤ B :=
    (Real.self_le_rpow_of_one_le (by linarith) hb.le).trans hAB
  have log_bound {A B : ℝ} (hA : 2 ≤ A) (hAB : A ^ b ≤ B) :
      Real.log (B / A) ≤ Real.log B := by
    have hA0 : 0 < A := by linarith
    have hB0 := hA0.trans_le (ordered hA hAB)
    exact Real.log_le_log (div_pos hB0 hA0) (div_le_self hB0.le (by linarith))
  have diverges (hRH : ¬ RiemannHypothesis) (K : ℝ) :
      ∃ S : ℝ, ∀ B : ℝ, S ≤ B → ∀ A : ℝ, 2 ≤ A → A ^ b ≤ B →
        K ≤ (∫ x in A..B, max (-primeTail x) 0 / Real.sqrt x) - 2 * Real.log (B / A) := by
    have hρ : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1 := by
      by_contra h
      exact hRH (golden_right_half_strip_implies_rh (fun ρ hz hlo hhi => h ⟨ρ, hz, hlo, hhi⟩))
    obtain ⟨ρ, hzero, hβ, _⟩ := hρ
    obtain ⟨η, hη0, hη⟩ := exists_between (sub_pos.mpr hβ)
    obtain ⟨S₀, hS₀⟩ := wide_window_power_lower_bound hb hzero hη0 hη
    have hlog := (isLittleO_log_rpow_atTop hη0).def (by norm_num : (0 : ℝ) < 1 / 4)
    have hgrowth := (tendsto_rpow_atTop hη0).eventually (eventually_ge_atTop (2 * K))
    obtain ⟨S₁, hS₁⟩ := eventually_atTop.mp (hlog.and hgrowth)
    refine ⟨max S₀ S₁, ?_⟩
    intro B hB A hA hAB
    have hmass := hS₀ B ((le_max_left _ _).trans hB) A hA hAB
    obtain ⟨hl, hg⟩ := hS₁ B ((le_max_right _ _).trans hB)
    have hB0 : 0 ≤ B := by linarith [ordered hA hAB]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hB0 _)] at hl
    linarith [le_abs_self (Real.log B), log_bound hA hAB]
  refine ⟨diverges, ?_⟩
  by_cases hRH : RiemannHypothesis
  · obtain ⟨C, hC, hbound⟩ := prime_tail_logarithmic_mass_of_rh hRH
    refine ⟨C, hC, ?_⟩
    intro A B hA hAB
    have h := (abs_le.mp (hbound A B hA (ordered hA hAB))).1
    linarith
  · obtain ⟨S, hS⟩ := diverges hRH 0
    let C := max 0 (2 * Real.log S)
    refine ⟨C, le_max_left _ _, ?_⟩
    intro A B hA hAB
    by_cases hBS : S ≤ B
    · linarith [hS B hBS A hA hAB, le_max_left (0 : ℝ) (2 * Real.log S)]
    · have hB0 : 0 < B := by linarith [ordered hA hAB]
      have hlog := Real.log_le_log hB0 (le_of_not_ge hBS)
      have hmass : 0 ≤ ∫ x in A..B, max (-primeTail x) 0 / Real.sqrt x :=
        intervalIntegral.integral_nonneg (ordered hA hAB)
          (fun x _ => div_nonneg (le_max_right _ _) (Real.sqrt_nonneg x))
      linarith [log_bound hA hAB, le_max_right 0 (2 * Real.log S)]

end D5.S3.Weil.Mertens.IntegratedExplicit.WidePrimeWindowMass
