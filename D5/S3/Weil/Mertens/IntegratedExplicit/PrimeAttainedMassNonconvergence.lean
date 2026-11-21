/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeAttainedMassNonconvergence
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeAttainedMassNonconvergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-ratio prime-tail mass has no finite limit at an attained abscissa. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedShortWindows
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeFixedRatioWindowMass

/-! Interval additivity transfers a putative limit to short zero-mass windows
and to wide windows with a positive lower bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedShortWindows
  (prime_tail_positive_short_windows_of_attained_zero)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeFixedRatioWindowMass
  (prime_tail_fixed_ratio_mass_of_zero)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail prime_integrable)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedMassNonconvergence

private noncomputable def density (x : ℝ) : ℝ :=
  max (-primeTail x) 0 / Real.sqrt x

private theorem density_nonneg (x : ℝ) : 0 ≤ density x :=
  div_nonneg (le_max_right _ _) (Real.sqrt_nonneg x)

private theorem density_intervalIntegrable {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    IntervalIntegrable density volume A B := by
  have htail : ContinuousOn primeTail (Ici (1 : ℝ)) :=
    prime_integrable.continuousOn_Ici_primitive_Ioi
  have hc : ContinuousOn density (Ici (1 : ℝ)) :=
    (htail.neg.sup continuousOn_const).div Real.continuous_sqrt.continuousOn
      (fun _ hx => (Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)).ne')
  exact (hc.mono fun _ hx => hA.trans hx.1).intervalIntegrable_of_Icc hAB

private noncomputable def windowMass (p k B : ℝ) : ℝ :=
  (∫ x in B / k..B, density x) / B ^ p

/-- Split a product-ratio window at the endpoint of its outer window. -/
private theorem windowMass_mul (p : ℝ) {k l B : ℝ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hleft : 1 ≤ B / (k * l)) :
    windowMass p (k * l) B =
      windowMass p k B + k ^ (-p) * windowMass p l (B / k) := by
  have hk₀ : 0 < k := zero_lt_one.trans_le hk
  have hl₀ : 0 < l := zero_lt_one.trans_le hl
  have hB : 0 < B := (div_pos_iff_of_pos_right (mul_pos hk₀ hl₀)).mp
    (zero_lt_one.trans_le hleft)
  have hmid : B / k ≤ B := div_le_self hB.le hk
  have hsplit : B / k / l = B / (k * l) := div_div B k l
  have hfirst : B / (k * l) ≤ B / k := by
    rw [← hsplit]
    exact div_le_self (div_nonneg hB.le hk₀.le) hl
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (density_intervalIntegrable hleft hfirst)
    (density_intervalIntegrable (hleft.trans hfirst) hmid)
  simp only [windowMass, hsplit, ← hadd, add_div]
  rw [Real.rpow_neg hk₀.le, Real.div_rpow hB.le hk₀.le]
  field_simp [(Real.rpow_pos_of_pos hk₀ p).ne', (Real.rpow_pos_of_pos hB p).ne']
  exact add_comm _ _

/-- Compare the two splittings of the same product-ratio window. -/
private theorem windowMass_overlap (p : ℝ) {k l B : ℝ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hleft : 1 ≤ B / (k * l)) :
    windowMass p l B - k ^ (-p) * windowMass p l (B / k) =
      windowMass p k B - l ^ (-p) * windowMass p k (B / l) := by
  have hkSplit := windowMass_mul p hk hl hleft
  have hlSplit := windowMass_mul p hl hk (by rwa [mul_comm l k])
  rw [mul_comm l k] at hlSplit
  linarith only [hkSplit, hlSplit]

/-- A bounded error with a vanishing recurrence residual tends to zero. -/
private theorem tendsto_zero_of_stable_delay {ι : Type*} {F : Filter ι} {shift : ι → ι}
    (hshift : Tendsto shift F F) {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    {e : ι → ℝ} {M : ℝ} (hM : ∀ᶠ x in F, |e x| ≤ M)
    (hres : Tendsto (fun x => e x - q * e (shift x)) F (𝓝 0)) :
    Tendsto e F (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hsmall : ∀ᶠ x in F, |e x - q * e (shift x)| ≤ ε / 2 * (1 - q) := by
    filter_upwards [Metric.tendsto_nhds.1 hres _ (mul_pos (half_pos hε) (sub_pos.mpr hq₁))]
      with x hx
    simpa only [Real.dist_eq, sub_zero] using hx.le
  have hiterate (n : ℕ) : ∀ᶠ x in F, |e x| ≤ q ^ n * M + ε / 2 * (1 - q ^ n) := by
    induction n with
    | zero => simpa using hM
    | succ n ih =>
        filter_upwards [hsmall, hshift.eventually ih] with x hresidual hprev
        have hstep : |e x| ≤ |e x - q * e (shift x)| + q * |e (shift x)| := by
          have h := abs_add_le (e x - q * e (shift x)) (q * e (shift x))
          rwa [sub_add_cancel, abs_mul, abs_of_nonneg hq₀] at h
        calc
          |e x| ≤ ε / 2 * (1 - q) + q * (q ^ n * M + ε / 2 * (1 - q ^ n)) :=
            hstep.trans (add_le_add hresidual (mul_le_mul_of_nonneg_left hprev hq₀))
          _ = q ^ (n + 1) * M + ε / 2 * (1 - q ^ (n + 1)) := by rw [pow_succ]; ring
  have hdecay : Tendsto (fun n : ℕ => q ^ n * M) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁).mul_const M
  obtain ⟨n, hn⟩ := (hdecay.eventually_lt_const (half_pos hε)).exists
  filter_upwards [hiterate n] with x hx
  rw [Real.dist_eq, sub_zero]
  have hcorrection := mul_nonneg (half_pos hε).le (pow_nonneg hq₀ n)
  linarith only [hx, hn, hcorrection]

/-- For every prescribed real ratio greater than one, the prime-only negative
mass at the exponent of an attained off-line zero has no finite limit. -/
theorem prime_tail_mass_no_finite_limit_of_attained_zero (ρ : ℂ) (hρ : IsNontrivialZero ρ) :
    let β := ρ.re
    1 / 2 < β → (∀ z : ℂ, IsNontrivialZero z → z.re ≤ β) →
      ∀ (κ L : ℝ), 1 < κ →
        ¬ Tendsto (fun B : ℝ =>
          (∫ x in B / κ..B, max (-primeTail x) 0 / Real.sqrt x) / B ^ (β - 1 / 2))
          atTop (𝓝 L) := by
  dsimp only
  intro hβ hmax κ L hκ
  let p : ℝ := ρ.re - 1 / 2
  change ¬ Tendsto (windowMass p κ) atTop (𝓝 L)
  intro hlim
  obtain ⟨R, K, X₀, hR, _, hX₀, hshort⟩ :=
    prime_tail_positive_short_windows_of_attained_zero ρ hρ hβ hmax
  let ℓ : ℝ := min κ R
  have hℓ : 1 < ℓ := lt_min hκ hR
  have hℓκ : ℓ ≤ κ := min_le_left _ _
  have hℓR : ℓ ≤ R := min_le_right _ _
  have hk₀ : 0 < κ := zero_lt_one.trans hκ
  have hl₀ : 0 < ℓ := zero_lt_one.trans hℓ
  have hshiftκ : Tendsto (fun B : ℝ => B / κ) atTop atTop :=
    (tendsto_div_const_atTop_of_pos hk₀).2 tendsto_id
  have hshiftℓ : Tendsto (fun B : ℝ => B / ℓ) atTop atTop :=
    (tendsto_div_const_atTop_of_pos hl₀).2 tendsto_id
  let q := κ ^ (-p)
  let r := ℓ ^ (-p)
  have hp : 0 < p := sub_pos.mpr hβ
  have hq₀ : 0 ≤ q := (Real.rpow_pos_of_pos hk₀ _).le
  have hq₁ : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hκ (neg_neg_of_pos hp)
  have hr₁ : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hℓ (neg_neg_of_pos hp)
  let C := (1 - r) * L / (1 - q)
  have hC : (1 - q) * C = L - r * L := by
    dsimp only [C]
    rw [mul_div_cancel₀ _ (sub_ne_zero.mpr hq₁.ne')]
    ring
  have hoverlap : ∀ᶠ B in atTop,
      windowMass p ℓ B - q * windowMass p ℓ (B / κ) =
        windowMass p κ B - r * windowMass p κ (B / ℓ) := by
    have hshift : Tendsto (fun B : ℝ => B / (κ * ℓ)) atTop atTop :=
      (tendsto_div_const_atTop_of_pos (mul_pos hk₀ hl₀)).2 tendsto_id
    filter_upwards [hshift.eventually_ge_atTop 1] with B hB
    exact windowMass_overlap p hκ.le hℓ.le hB
  have hdelayed : Tendsto (fun B => windowMass p ℓ B - q * windowMass p ℓ (B / κ))
      atTop (𝓝 (L - r * L)) :=
    (hlim.sub ((hlim.comp hshiftℓ).const_mul r)).congr' (hoverlap.mono fun _ h => h.symm)
  have hbounded : ∀ᶠ B in atTop, 0 ≤ windowMass p ℓ B ∧ windowMass p ℓ B ≤ windowMass p κ B := by
    filter_upwards [hshiftκ.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℝ)] with B hleft hB
    have hB₀ := zero_lt_one.trans_le hB
    have hle : B / κ ≤ B / ℓ := div_le_div_of_nonneg_left hB₀.le hl₀ hℓκ
    have hright : B / ℓ ≤ B := div_le_self hB₀.le hℓ.le
    refine ⟨div_nonneg (intervalIntegral.integral_nonneg_of_forall hright density_nonneg)
      (Real.rpow_nonneg hB₀.le _), ?_⟩
    exact div_le_div_of_nonneg_right
      (intervalIntegral.integral_mono_interval hle hright le_rfl (ae_of_all _ density_nonneg)
        (density_intervalIntegrable hleft (hle.trans hright))) (Real.rpow_nonneg hB₀.le _)
  let e (B : ℝ) := windowMass p ℓ B - C
  have heBound : ∀ᶠ B in atTop, |e B| ≤ L + 1 + |C| := by
    filter_upwards [hbounded, hlim.eventually_lt_const (lt_add_one L)] with B hB hupper
    calc
      |e B| ≤ |windowMass p ℓ B| + |C| := by
        simpa only [e, sub_eq_add_neg, abs_neg] using abs_add_le (windowMass p ℓ B) (-C)
      _ ≤ L + 1 + |C| := by
        rw [abs_of_nonneg hB.1]
        exact add_le_add (hB.2.trans hupper.le) le_rfl
  have heResidual : Tendsto (fun B => e B - q * e (B / κ)) atTop (𝓝 0) := by
    have h := hdelayed.sub_const ((1 - q) * C)
    rw [show L - r * L - (1 - q) * C = 0 by rw [hC, sub_self]] at h
    apply h.congr'
    exact Eventually.of_forall fun B => by dsimp only [e]; ring
  have hℓLimit : Tendsto (windowMass p ℓ) atTop (𝓝 C) := by
    have h := (tendsto_zero_of_stable_delay hshiftκ hq₀ hq₁ heBound heResidual).add_const C
    simpa only [e, zero_add, sub_add_cancel] using h
  have hC₀ : C = 0 := by
    by_contra hne
    obtain ⟨Y, hY⟩ := eventually_atTop.mp
      (Metric.tendsto_nhds.1 hℓLimit |C| (abs_pos.mpr hne))
    let X := max X₀ Y
    obtain ⟨A, hA, _, hzero⟩ := hshort X (le_max_left _ _)
    have hA₀ : 0 ≤ A := by
      have h : 2 ≤ A := hX₀.trans ((le_max_left X₀ Y).trans hA.1)
      linarith
    have hAY : Y ≤ ℓ * A := ((le_max_right X₀ Y).trans hA.1).trans
      (le_mul_of_one_le_left hA₀ hℓ.le)
    have h := hY (ℓ * A) hAY
    have hmass : windowMass p ℓ (ℓ * A) = 0 := by
      have hcancel : ℓ * A / ℓ = A := by field_simp
      simpa only [windowMass, hcancel, density, zero_div] using
        congrArg (fun v : ℝ => v / (ℓ * A) ^ p) (hzero ℓ ⟨hℓ.le, hℓR⟩)
    rw [hmass, Real.dist_eq, zero_sub, abs_neg] at h
    exact (lt_irrefl _ h)
  have hL₀ : L = 0 := by
    have h : (1 - r) * L = 0 := by
      have h' := (div_eq_zero_iff.mp hC₀)
      exact h'.resolve_right (sub_ne_zero.mpr hq₁.ne')
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hr₁.ne')
  rw [hL₀] at hlim
  have hwide (n : ℕ) : Tendsto (windowMass p (κ ^ n)) atTop (𝓝 0) := by
    induction n with
    | zero =>
        apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0)).congr
        intro B
        simp only [pow_zero, windowMass, div_one, intervalIntegral.integral_same, zero_div]
    | succ n ih =>
        have hkn := one_le_pow₀ hκ.le (n := n)
        have hshift : Tendsto (fun B : ℝ => B / (κ * κ ^ n)) atTop atTop :=
          (tendsto_div_const_atTop_of_pos (mul_pos hk₀ (pow_pos hk₀ n))).2 tendsto_id
        have h := hlim.add ((ih.comp hshiftκ).const_mul q)
        rw [mul_zero, add_zero] at h
        apply h.congr'
        filter_upwards [hshift.eventually_ge_atTop 1] with B hB
        rw [pow_succ']
        exact (windowMass_mul p hκ.le hkn hB).symm
  obtain ⟨k, c, S, hk, hc, hlower⟩ := prime_tail_fixed_ratio_mass_of_zero ρ hρ hβ
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt k hκ
  have hshift : Tendsto (fun B : ℝ => B / κ ^ n) atTop atTop :=
    (tendsto_div_const_atTop_of_pos (pow_pos hk₀ n)).2 tendsto_id
  have hcontr : ∀ᶠ _ : ℝ in atTop, False := by
    filter_upwards [(hwide n).eventually_lt_const hc, hshift.eventually_ge_atTop 2,
      eventually_ge_atTop S, eventually_ge_atTop (1 : ℝ)] with B hsmall hA hS hB
    have hratio : k * (B / κ ^ n) ≤ B := by
      calc
        _ ≤ κ ^ n * (B / κ ^ n) := mul_le_mul_of_nonneg_right hn.le (by positivity)
        _ = B := by field_simp
    have h := hlower B hS (B / κ ^ n) hA hratio
    exact hsmall.not_ge ((le_div_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hB) p)).2 h)
  exact hcontr.exists.elim fun _ h => h

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedMassNonconvergence
