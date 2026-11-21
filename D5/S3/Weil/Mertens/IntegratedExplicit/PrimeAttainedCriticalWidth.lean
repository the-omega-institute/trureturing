/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeAttainedCriticalWidth
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeAttainedCriticalWidth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The real widths with zero lower prime-tail mass form a closed interval. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedShortWindows
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeFixedRatioWindowMass

/-! The critical width of normalized negative mass for the actual prime-only tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZeroSum (IsNontrivialZero)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedCriticalWidth

open MaximalRealPartProjection
open PrimeAttainedShortWindows
open PrimeFixedRatioWindowMass (prime_tail_fixed_ratio_mass_of_zero)
open PrimeOnlyTailCorrection (primeTail prime_integrable)

noncomputable def integrand (x : ℝ) : ℝ :=
  max (-primeTail x) 0 / Real.sqrt x

private noncomputable def mass (p W B : ℝ) : ℝ :=
  (∫ x in B * Real.exp (-W)..B, integrand x) / B ^ p

theorem integrand_nonneg (x : ℝ) : 0 ≤ integrand x :=
  div_nonneg (le_max_right _ _) (Real.sqrt_nonneg x)

theorem integrand_intervalIntegrable {A B : ℝ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    IntervalIntegrable integrand volume A B := by
  have hone (x : ℝ) (hx : x ∈ Icc A B) : 1 ≤ x :=
    one_le_two.trans (hA.trans hx.1)
  exact (((prime_integrable.continuousOn_Ici_primitive_Ioi.mono hone).neg.sup
    continuousOn_const).div Real.continuous_sqrt.continuousOn
      (fun x hx => (Real.sqrt_pos.mpr (zero_lt_one.trans_le (hone x hx))).ne')
    ).intervalIntegrable_of_Icc hAB

theorem eventually_abs_normalized_tail_le {β : ℝ} (hβ : 1 / 2 < β)
    (hmax : ∀ z : ℂ, IsNontrivialZero z → z.re ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, |x ^ (1 - β) * primeTail x| ≤ C := by
  have hrealPart (j : ℕ) : (actualZero j).re ≤ β :=
    hmax _ (actualData.zero_isNontrivial (actualOccurrenceEquiv j).1)
  have hcoeff := actualCoeff_hasSum.summable.norm
  let C : ℝ := ∑' j : ℕ, ‖actualCoeff j‖
  have hseries (t : ℝ) : |(maximalSeries actualCoeff actualZero β t).re| ≤ C := by
    have hs := summable_norm_maximalTerm (z := actualZero) (Θ := β) hcoeff t
    refine (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm hs).trans ?_)
    exact hs.tsum_le_tsum (fun j => norm_maximalTerm_le j t) hcoeff
  have hcomplete := normalized_complete_tail_approx (by linarith only [hβ]) hrealPart
  have herror := normalized_prime_power_error hβ
  have hlog : Tendsto (fun x : ℝ => x ^ (1 - β) * primeTail x +
      (maximalSeries actualCoeff actualZero β (Real.log x)).re) atTop (𝓝 0) := by
    have h := (hcomplete.sub herror).comp Real.tendsto_log_atTop
    rw [sub_self] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [Function.comp_def, Real.exp_log hx, Real.rpow_def_of_pos hx, mul_comm (Real.log x)]
    ring
  refine ⟨1 + C, add_pos_of_pos_of_nonneg zero_lt_one (tsum_nonneg fun _ => norm_nonneg _), ?_⟩
  filter_upwards [(Metric.tendsto_nhds.mp hlog) 1 zero_lt_one] with x hx
  rw [Real.dist_eq, sub_zero] at hx
  calc
    _ = |(x ^ (1 - β) * primeTail x + (maximalSeries actualCoeff actualZero β (Real.log x)).re) -
        (maximalSeries actualCoeff actualZero β (Real.log x)).re| := by rw [add_sub_cancel_right]
    _ ≤ _ := (abs_sub _ _).trans (add_le_add hx.le (hseries _))

theorem integrand_le_power {β C x : ℝ} (hC : 0 ≤ C) (hx : 0 < x)
    (h : |x ^ (1 - β) * primeTail x| ≤ C) :
    integrand x ≤ C * x ^ ((β - 1 / 2) - 1) := by
  have hpow : 0 < x ^ (1 - β) := Real.rpow_pos_of_pos hx _
  have hweight : x ^ ((β - 1 / 2) - 1) * Real.sqrt x * x ^ (1 - β) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx, ← Real.rpow_add hx,
      show (β - 1 / 2) - 1 + 1 / 2 + (1 - β) = 0 by ring, Real.rpow_zero]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hx)).2
  apply (mul_le_mul_iff_left₀ hpow).1
  change max (-primeTail x) 0 * x ^ (1 - β) ≤ _
  rw [mul_assoc C, mul_assoc C, hweight, mul_one, max_mul_of_nonneg _ _ hpow.le, zero_mul]
  rw [neg_mul, mul_comm (primeTail x)]
  exact max_le ((neg_le_abs _).trans h) hC

/-- Widening a late window adds at most the normalized integral of the power majorant
over its new left segment. The same constant controls every pair of widths. -/
private theorem eventually_mass_increment {p C X : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hX : 2 ≤ X) (hdom : ∀ x ≥ X, integrand x ≤ C * x ^ (p - 1))
    {U W : ℝ} (hU : 0 ≤ U) (hUW : U ≤ W) :
    ∀ᶠ B : ℝ in atTop, 0 ≤ mass p W B - mass p U B ∧
      mass p W B - mass p U B ≤ C / p * (Real.exp (-p * U) - Real.exp (-p * W)) ∧
      C / p * (Real.exp (-p * U) - Real.exp (-p * W)) ≤ C * (W - U) := by
  have hleft (V : ℝ) : Tendsto (fun B : ℝ => B * Real.exp (-V)) atTop atTop :=
    tendsto_id.atTop_mul_const (Real.exp_pos _)
  filter_upwards [eventually_gt_atTop (0 : ℝ), (hleft W).eventually_ge_atTop X] with B hB hlate
  let A := B * Real.exp (-W)
  let D := B * Real.exp (-U)
  have hA : 2 ≤ A := hX.trans hlate
  have hAD : A ≤ D :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hUW)) hB.le
  have hDB : D ≤ B := mul_le_of_le_one_right hB.le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hU))
  have hBp : 0 < B ^ p := Real.rpow_pos_of_pos hB _
  have hadd : mass p W B - mass p U B = (∫ x in A..D, integrand x) / B ^ p := by
    change (∫ x in A..B, integrand x) / B ^ p - (∫ x in D..B, integrand x) / B ^ p = _
    rw [← intervalIntegral.integral_add_adjacent_intervals (integrand_intervalIntegrable hA hAD)
      (integrand_intervalIntegrable (hA.trans hAD) hDB), add_div, add_sub_cancel_right]
  have hpint : -1 < p - 1 := by linarith only [hp]
  have hpower (V : ℝ) : (B * Real.exp (-V)) ^ p = B ^ p * Real.exp (-p * V) := by
    rw [Real.mul_rpow hB.le (Real.exp_nonneg _), ← Real.exp_mul]
    congr 2
    ring
  rw [hadd]
  refine ⟨div_nonneg (intervalIntegral.integral_nonneg_of_forall hAD integrand_nonneg) hBp.le,
    ?_, ?_⟩
  · calc
      _ ≤ (∫ x in A..D, C * x ^ (p - 1)) / B ^ p := by
        apply div_le_div_of_nonneg_right _ hBp.le
        exact intervalIntegral.integral_mono_on hAD (integrand_intervalIntegrable hA hAD)
          ((intervalIntegral.intervalIntegrable_rpow' hpint).const_mul _)
          (fun x hx => hdom x (hlate.trans hx.1))
      _ = _ := by
        dsimp only [A, D]
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hpint), sub_add_cancel,
          hpower U, hpower W, ← mul_sub]
        field_simp
  · have hfactor : Real.exp (-p * W) = Real.exp (-p * U) * Real.exp (-p * (W - U)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hd : 0 ≤ p * (W - U) := mul_nonneg hp.le (sub_nonneg.mpr hUW)
    have hdexp : 1 - Real.exp (-p * (W - U)) ≤ p * (W - U) := by
      linarith only [Real.add_one_le_exp (-p * (W - U))]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hp).2
    rw [hfactor, ← mul_one_sub]
    calc
      _ ≤ C * (Real.exp (-p * U) * (p * (W - U))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdexp (Real.exp_nonneg _)) hC
      _ ≤ C * (p * (W - U)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_of_le_one_left hd (Real.exp_le_one_iff.mpr
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp.le) hU))) hC
      _ = _ := by ring

private theorem eventually_mass_bounds {p C X : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hX : 2 ≤ X) (hdom : ∀ x ≥ X, integrand x ≤ C * x ^ (p - 1))
    {W : ℝ} (hW : 0 ≤ W) :
    ∀ᶠ B : ℝ in atTop, 0 ≤ mass p W B ∧ mass p W B ≤ C / p := by
  have hzero (B : ℝ) : mass p 0 B = 0 := by simp [mass]
  filter_upwards [eventually_mass_increment hp hC hX hdom le_rfl hW] with B h
  rw [hzero, sub_zero, mul_zero, Real.exp_zero] at h
  exact ⟨h.1, h.2.1.trans (mul_le_of_le_one_right (div_nonneg hC hp.le)
    (sub_le_self _ (Real.exp_nonneg _)))⟩

/-- At an attained zeta abscissa above one half, the lower limit of normalized
prime-tail negative mass vanishes exactly up to a unique positive real width,
including that width. -/
theorem prime_tail_zero_liminf_iff_le_critical_width (ρ : ℂ) (hρ : IsNontrivialZero ρ) :
    let β := ρ.re
    1 / 2 < β → (∀ z : ℂ, IsNontrivialZero z → z.re ≤ β) →
      ∃! Wstar : ℝ, 0 < Wstar ∧ ∀ W : ℝ, 0 ≤ W →
        (Filter.liminf
          (fun B : ℝ => (∫ x in B * Real.exp (-W)..B, max (-primeTail x) 0 / Real.sqrt x) /
            B ^ (β - 1 / 2)) atTop = 0 ↔ W ≤ Wstar) := by
  dsimp only
  intro hβ hmax
  let p : ℝ := ρ.re - 1 / 2
  let a (W : ℝ) := Filter.liminf (mass p W) atTop
  change ∃! Wstar : ℝ, 0 < Wstar ∧ ∀ W : ℝ, 0 ≤ W → (a W = 0 ↔ W ≤ Wstar)
  have hp : 0 < p := sub_pos.mpr hβ
  obtain ⟨C, hC, htail⟩ := eventually_abs_normalized_tail_le hβ hmax
  obtain ⟨Y, hY⟩ := eventually_atTop.mp htail
  let X : ℝ := max 2 Y
  have hX : 2 ≤ X := le_max_left _ _
  have hdom (x : ℝ) (hx : X ≤ x) : integrand x ≤ C * x ^ (p - 1) :=
    integrand_le_power hC.le ((by norm_num : (0 : ℝ) < 2).trans_le (hX.trans hx))
      (hY x ((le_max_right _ _).trans hx))
  have hbounds {W : ℝ} (hW : 0 ≤ W) := eventually_mass_bounds hp hC.le hX hdom hW
  have hlower {W : ℝ} (hW : 0 ≤ W) : atTop.IsBoundedUnder (· ≥ ·) (mass p W) :=
    isBoundedUnder_of_eventually_ge ((hbounds hW).mono fun _ h => h.1)
  have hupper {W : ℝ} (hW : 0 ≤ W) : atTop.IsBoundedUnder (· ≤ ·) (mass p W) :=
    isBoundedUnder_of_eventually_le ((hbounds hW).mono fun _ h => h.2)
  have ha {W : ℝ} (hW : 0 ≤ W) : 0 ≤ a W :=
    le_liminf_of_le (hupper hW).isCoboundedUnder_ge ((hbounds hW).mono fun _ h => h.1)
  have hchange {U W : ℝ} (hU : 0 ≤ U) (hUW : U ≤ W) :
      a U ≤ a W ∧ a W ≤ a U + C * (W - U) := by
    have hW := hU.trans hUW
    have hinc := eventually_mass_increment hp hC.le hX hdom hU hUW
    have hshift : ∀ᶠ B : ℝ in atTop, mass p W B ≤ mass p U B + C * (W - U) :=
      hinc.mono fun B h => sub_le_iff_le_add'.mp (h.2.1.trans h.2.2)
    refine ⟨liminf_le_liminf (hinc.mono fun _ h => sub_nonneg.mp h.1)
      (hlower hU) (hupper hW).isCoboundedUnder_ge, ?_⟩
    have hshiftBound : atTop.IsBoundedUnder (· ≤ ·) (fun B => mass p U B + C * (W - U)) :=
      isBoundedUnder_of_eventually_le ((hbounds hU).mono fun _ h => add_le_add h.2 le_rfl)
    exact (liminf_le_liminf hshift (hlower hW) hshiftBound.isCoboundedUnder_ge).trans_eq
      (liminf_add_const atTop _ _ (hupper hU).isCoboundedUnder_ge (hlower hU))
  obtain ⟨κ₀, K, X₀, hκ₀, _, hX₀, hshort⟩ :=
    prime_tail_positive_short_windows_of_attained_zero ρ hρ hβ hmax
  let W₀ := Real.log κ₀
  have hW₀ : 0 < W₀ := Real.log_pos hκ₀
  have hcancel (κ : ℝ) (hκ : 0 < κ) (A : ℝ) : (κ * A) * Real.exp (-Real.log κ) = A := by
    rw [Real.exp_neg, Real.exp_log hκ, mul_comm κ A, mul_assoc, mul_inv_cancel₀ hκ.ne', mul_one]
  have hfreq : ∃ᶠ B : ℝ in atTop, mass p W₀ B ≤ 0 := by
    apply frequently_atTop.mpr
    intro R
    obtain ⟨A, hA, _, hzero⟩ := hshort (max X₀ R) (le_max_left _ _)
    have hA₀ := (show (0 : ℝ) ≤ 2 by norm_num).trans (hX₀.trans ((le_max_left _ _).trans hA.1))
    refine ⟨κ₀ * A, (le_max_right _ _).trans (hA.1.trans
      (le_mul_of_one_le_left hA₀ hκ₀.le)), ?_⟩
    change (∫ x in (κ₀ * A) * Real.exp (-Real.log κ₀)..κ₀ * A, integrand x) /
      (κ₀ * A) ^ p ≤ 0
    rw [hcancel κ₀ (zero_lt_one.trans hκ₀), show (∫ x in A..κ₀ * A, integrand x) = 0 from
      hzero κ₀ ⟨hκ₀.le, le_rfl⟩, zero_div]
  have hsmall : a W₀ = 0 := (liminf_le_of_frequently_le hfreq (hlower hW₀.le)).antisymm (ha hW₀.le)
  obtain ⟨κ, c, S, hκ, hc, hwide⟩ := prime_tail_fixed_ratio_mass_of_zero ρ hρ hβ
  let W₁ := Real.log κ
  have hW₁ : 0 < W₁ := Real.log_pos hκ
  have hlarge : 0 < a W₁ := by
    apply hc.trans_le
    apply le_liminf_of_le (hupper hW₁.le).isCoboundedUnder_ge
    have hleft : Tendsto (fun B : ℝ => B * Real.exp (-W₁)) atTop atTop :=
      tendsto_id.atTop_mul_const (Real.exp_pos _)
    filter_upwards [eventually_ge_atTop S, eventually_gt_atTop (0 : ℝ),
      hleft.eventually_ge_atTop (2 : ℝ)] with B hBS hB hA
    have heq : κ * (B * Real.exp (-W₁)) = B := by
      change κ * (B * Real.exp (-Real.log κ)) = B
      rw [← mul_assoc, hcancel κ (zero_lt_one.trans hκ)]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hB p)).2 (hwide B hBS _ hA heq.le)
  let Z : Set ℝ := {W | 0 ≤ W ∧ a W = 0}
  have hmem : W₀ ∈ Z := ⟨hW₀.le, hsmall⟩
  have hnonempty : Z.Nonempty := ⟨W₀, hmem⟩
  have hbdd : BddAbove Z := ⟨W₁, fun W hW => by
    by_contra! h
    have hmono := (hchange hW₁.le h.le).1
    change 0 ≤ W ∧ a W = 0 at hW
    linarith only [hlarge, hmono, hW.2]⟩
  let Wstar := sSup Z
  have hstar : 0 < Wstar := hW₀.trans_le (le_csSup hbdd hmem)
  have hstarzero : a Wstar = 0 := by
    apply le_antisymm _ (ha hstar.le)
    by_contra! hpos
    obtain ⟨U, hUZ, hU⟩ := exists_lt_of_lt_csSup hnonempty
      (show Wstar - a Wstar / C < sSup Z from sub_lt_self _ (div_pos hpos hC))
    have hUstar : U ≤ Wstar := le_csSup hbdd hUZ
    change 0 ≤ U ∧ a U = 0 at hUZ
    have hbound := (hchange hUZ.1 hUstar).2
    have hstrict : Wstar - U < a Wstar / C := by linarith only [hU]
    have hcontr := (lt_div_iff₀ hC).1 hstrict
    rw [hUZ.2, zero_add] at hbound
    linarith only [hbound, hcontr]
  have hcutoff (W : ℝ) (hW : 0 ≤ W) : a W = 0 ↔ W ≤ Wstar := by
    refine ⟨fun h => le_csSup hbdd (show W ∈ Z from ⟨hW, h⟩), fun h => ?_⟩
    exact (((hchange hW h).1).trans_eq hstarzero).antisymm (ha hW)
  refine ⟨Wstar, ⟨hstar, hcutoff⟩, fun V hV => le_antisymm ?_ ?_⟩
  · exact (hcutoff V hV.1.le).mp ((hV.2 V hV.1.le).mpr le_rfl)
  · exact (hV.2 Wstar hstar.le).mp hstarzero

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedCriticalWidth
