/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampleMass
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/QuarticSampleMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted fourth-power sample mass characterizes RH and detects right-of-line zeros. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter MeasureTheory Set
open D5.S3.Arith.Robin.CompleteMertensPeak (Q U)
open D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling (remainder_chord quartic_chord_error)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth (compare_prime_mass)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampleMass

/-- The positive part of the integrated Mangoldt remainder at the fourth power of `n`,
weighted by the reciprocal cube of `n`. -/
def sample (n : ℕ) : ℝ := max (U ((n : ℝ)^4)) 0 / (n : ℝ)^3

/-- The weighted sample mass over the inclusive integer interval from `a` to `b`. -/
def blockMass (a b : ℕ) : ℝ := ∑ n ∈ Finset.Icc a b, sample n

private def density (x : ℝ) : ℝ := max (U x) 0 / x / Real.sqrt x

private lemma integrable_density {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable density volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hx0 := ha.trans_le ((uIcc_of_le hab) ▸ hx).1
  have h : ContinuousAt (fun x => max (U x) 0) x := (U_continuousAt_pos hx0).max continuousAt_const
  exact ((h.div continuousAt_id hx0.ne').div Real.continuous_sqrt.continuousAt
    (Real.sqrt_pos.mpr hx0).ne').continuousWithinAt

private lemma upper_cell {n : ℕ} (hn : 1 ≤ n) :
    (∫ x in (n : ℝ)^4..((n : ℝ)+1)^4, density x) ≤
      15 * sample n + 120 * sample (n+1) + 3375 / (n : ℝ) := by
  let t : ℝ := n
  let A := max (U (t^4)) 0
  let B := max (U ((t+1)^4)) 0
  have ht : 1 ≤ t := by dsimp [t]; exact_mod_cast hn
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hu : t^4 < (t+1)^4 := by gcongr; linarith
  have hA : 0 ≤ A := le_max_right _ _
  have hB : 0 ≤ B := le_max_right _ _
  have hM : 0 ≤ A+B+225*t^2 := by positivity
  have hlen : (t+1)^4-t^4 ≤ 15*t^3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg t), mul_nonneg (sub_nonneg.mpr ht) ht0.le]
  have hmono := intervalIntegral.integral_mono_on hu.le (integrable_density (pow_pos ht0 4) hu.le)
    (intervalIntegrable_const (c := (A+B+225*t^2)/t^6)) (fun x (hx : x ∈ Icc (t^4) ((t+1)^4)) => by
      have hc := remainder_chord (pow_pos ht0 4) hu hx.1 hx.2
        (show U (t^4) ≤ A+B from (le_max_left _ _).trans (le_add_of_nonneg_right hB))
        (show U ((t+1)^4) ≤ A+B from (le_max_left _ _).trans (le_add_of_nonneg_left hA))
      have herr := quartic_chord_error ht le_rfl hu.le le_rfl
      have hmax : max (U x) 0 ≤ A+B+225*t^2 := max_le (by linarith) hM
      have hrt : t^2 ≤ Real.sqrt x := (Real.le_sqrt (sq_nonneg _) ((pow_pos ht0 4).le.trans hx.1)).mpr
        (by simpa only [←pow_mul] using hx.1)
      have hden : t^6 ≤ x * Real.sqrt x := calc
        _ = t^4*t^2 := by ring
        _ ≤ _ := mul_le_mul hx.1 hrt (sq_nonneg _) ((pow_pos ht0 4).le.trans hx.1)
      dsimp only [density]
      rw [div_div]
      exact div_le_div₀ hM hmax (pow_pos ht0 6) hden)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hmajor := hmono.trans (mul_le_mul_of_nonneg_right hlen (div_nonneg hM (pow_pos ht0 6).le))
  have hpow : (t+1)^3 ≤ 8*t^3 := by calc
    _ ≤ (2*t)^3 := pow_le_pow_left₀ (by positivity) (by linarith) _
    _ = _ := by ring
  have hshift : B/t^3 ≤ 8*(B/(t+1)^3) := by
    have hprod := mul_le_mul_of_nonneg_left hpow hB
    field_simp [ht0.ne', (show 0 < t+1 by positivity).ne']
    nlinarith only [hprod]
  change _ ≤ 15*(A/t^3) + 120*(max (U (((n+1:ℕ):ℝ)^4)) 0 / ((n+1:ℕ):ℝ)^3) + 3375/t
  push_cast
  change _ ≤ 15*(A/t^3) + 120*(B/(t+1)^3) + 3375/t
  apply hmajor.trans
  calc
    _ = 15*(A/t^3) + 15*(B/t^3) + 3375/t := by field_simp [ht0.ne']; ring
    _ ≤ _ := by linarith

private lemma log_step {x : ℝ} (hx : 1 ≤ x) :
    1 / (x+1) ≤ Real.log (x+1) - Real.log x ∧
    1 / x ≤ 2 * (Real.log (x+1) - Real.log x) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hx1 : 0 < x+1 := by positivity
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hx1 hx0)
  rw [inv_div, Real.log_div hx1.ne' hx0.ne'] at h
  have heq : 1-x/(x+1) = 1/(x+1) := by field_simp; ring
  rw [heq] at h
  refine ⟨h, ?_⟩
  have hle : 1/x ≤ 2/(x+1) := (div_le_div_iff₀ hx0 hx1).mpr (by linarith)
  calc
    _ ≤ 2/(x+1) := hle
    _ = 2*(1/(x+1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by norm_num)

private lemma block_succ {a b : ℕ} (h : a ≤ b) :
    blockMass a (b+1) = blockMass a b + sample (b+1) := by
  unfold blockMass
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (h.trans (Nat.le_succ _)), Finset.sum_insert]
  · exact add_comm _ _
  · simp

private lemma density_block {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ x in (a : ℝ)^4..(b : ℝ)^4, density x) + 15*sample b ≤
      135*blockMass a b + 6750*(Real.log b - Real.log a) := by
  induction b, hab using Nat.le_induction with
  | base =>
    have hs : 0 ≤ sample a := div_nonneg (le_max_right _ _) (by positivity)
    simp [blockMass]
    linarith
  | succ b hab ih =>
    have h1 := ha.trans hab
    have hb : 1 ≤ (b : ℝ) := by exact_mod_cast h1
    have ha0 : 0 < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
    have hab' : (a : ℝ)^4 ≤ (b : ℝ)^4 := by gcongr
    have hb' : (b : ℝ)^4 ≤ ((b : ℝ)+1)^4 := by gcongr; linarith
    rw [block_succ hab, Nat.cast_succ]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (integrable_density (pow_pos ha0 4) hab') (integrable_density ((pow_pos ha0 4).trans_le hab') hb')]
    have hc := upper_cell h1
    have hl := (log_step hb).2
    simp only [div_eq_mul_inv, one_mul] at hc hl
    linarith only [ih, hc, hl]

open PrimeOnlyTailCorrection (primeTail)

/-- The constant in the logarithmic error is uniform in both ends of the block. -/
theorem prime_mass_le_samples :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      (∫ x in (a : ℝ)^4..(b : ℝ)^4, max (-primeTail x) 0 / Real.sqrt x) + 15 * sample b ≤
        135*blockMass a b + C*(Real.log b - Real.log a) := by
  obtain ⟨c, hc⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨6750+8*|c|, by positivity, ?_⟩
  intro a b ha hab
  have ha2 : 2 ≤ (a : ℝ) := by exact_mod_cast ha
  have ha0 : 0 < (a : ℝ) := by linarith
  have habr : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hb0 := ha0.trans_le habr
  have h2 : 2 ≤ (a : ℝ)^4 := by nlinarith [sq_nonneg ((a : ℝ)^2-1), sq_nonneg ((a : ℝ)-1)]
  have hab' : (a : ℝ)^4 ≤ (b : ℝ)^4 := by gcongr
  have hcmp := (compare_prime_mass (C := |c|) (fun t _ => (hc t).trans
    (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))) (by linarith : 1 ≤ (a : ℝ)^4) hab').2
  have heq : (∫ x in (a : ℝ)^4..(b : ℝ)^4, max (-Q x) 0 / Real.sqrt x) =
      ∫ x in (a : ℝ)^4..(b : ℝ)^4, density x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx2 := h2.trans ((uIcc_of_le hab') ▸ hx).1
    have hx0 : 0 < x := by linarith
    have h := D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
      D5.S3.Weil.Mertens.WeightedPrimeLimit.chebyshev_error_kernel_integrable hx2
    change Q x = _ at h
    have hQ : -Q x = U x / x := by rw [h]; dsimp only [U]; field_simp [hx0.ne']; ring
    dsimp only [density]
    rw [hQ, ← max_div_div_right hx0.le (U x) 0, zero_div]
  rw [heq, Real.log_div (pow_pos hb0 4).ne' (pow_pos ha0 4).ne', Real.log_pow, Real.log_pow] at hcmp
  nlinarith only [hcmp, density_block (by omega : 1 ≤ a) hab]

/-- Under RH, the sample weights on every sufficiently late block are bounded by the harmonic weights. -/
theorem eventual_logarithmic_bound (hRH : RiemannHypothesis) :
    ∀ᶠ a : ℕ in atTop, ∀ b ≥ a,
      blockMass a b < 1/(a : ℝ) + (Real.log b - Real.log a) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (QuarticSampling.rh_iff_eventually_quartic_samples.mp hRH)
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop (1:ℕ)] with a hNa ha
  have hs (n : ℕ) (han : a ≤ n) : sample n < 1/(n : ℝ) := by
    have hn : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    apply (div_lt_div_iff₀ (pow_pos hn 3) hn).mpr
    have H := mul_lt_mul_of_pos_right (max_lt (hN n (hNa.trans han)) (pow_pos hn 2)) hn
    simpa [pow_succ] using H
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simpa [blockMass] using hs a le_rfl
  | succ b hab ih =>
    have hb : 1 ≤ (b : ℝ) := by exact_mod_cast ha.trans hab
    have hnext := hs (b+1) (hab.trans (Nat.le_succ _))
    rw [block_succ hab, Nat.cast_succ]
    rw [Nat.cast_succ] at hnext
    linarith [hnext, (log_step hb).1]

private lemma absorb_log (C : ℝ) (hC : 0 ≤ C) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, 1 + C*Real.log x ≤ x^η := by
  have hpos : 0 < 2*(C+1) := by linarith
  have hl := (isLittleO_log_rpow_atTop hη).bound (inv_pos.mpr hpos)
  filter_upwards [hl, eventually_ge_atTop (1 : ℝ), (tendsto_rpow_atTop hη).eventually_ge_atTop 2] with x hx hx1 hx2
  have hx0 := zero_lt_one.trans_le hx1
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1), abs_of_pos (Real.rpow_pos_of_pos hx0 _)] at hx
  rw [←div_eq_inv_mul] at hx
  have hh := (le_div_iff₀ hpos).mp hx
  nlinarith [Real.log_nonneg hx1]

/-- A right-of-line zero forces a power lower bound on every sufficiently late block,
with an arbitrary positive loss in the exponent. -/
theorem off_line_zero_forces_sample_mass {z : ℂ} (hz : riemannZeta z = 0)
    (hβ : 1/2 < z.re) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, (k : ℝ)^(16*(z.re-1/2)-ε) ≤ blockMass (k^3) (k^4) := by
  let g := z.re-1/2
  have hg : 0 < g := sub_pos.mpr hβ
  let δ := min (ε/2) (4*g)
  have hδ : 0 < δ := lt_min (half_pos hε) (by positivity)
  have hδε : 2*δ ≤ ε := by linarith [min_le_left (ε/2) (4*g)]
  have hδg : δ ≤ 4*g := min_le_right _ _
  let t := 16*g-2*δ
  have ht : 0 < t := by dsimp [t]; linarith
  obtain ⟨C, hC, cmp⟩ := prime_mass_le_samples
  have hlow := PrimeWindowPoleGrowth.off_line_zero_forces_window_mass hz hβ
    (b := (4 : ℝ)/3) (by norm_num) (div_pos hδ (by norm_num : (0 : ℝ) < 12))
  have hY : Tendsto (fun k : ℕ => (k : ℝ)^12) atTop atTop :=
    (tendsto_pow_atTop (by decide : (12:ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hlarge := tendsto_natCast_atTop_atTop.eventually ((tendsto_rpow_atTop hδ).eventually_ge_atTop 136)
  filter_upwards [hY.eventually hlow, hlarge, tendsto_natCast_atTop_atTop.eventually
    (absorb_log C hC ht), eventually_ge_atTop (2:ℕ)] with k hk hbig hlog hk2
  have hk1 : 1 ≤ k := by omega
  have hkreal : 1 ≤ (k : ℝ) := by exact_mod_cast hk1
  have hkpos := zero_lt_one.trans_le hkreal
  have hZ : ((k : ℝ)^12)^((4 : ℝ)/3) = (k : ℝ)^16 := by
    rw [← Real.rpow_natCast (k : ℝ) 12, ← Real.rpow_mul hkpos.le]
    norm_num
  have hexp : ((k : ℝ)^12)^((4 : ℝ)/3*(z.re-1/2)-δ/12) = (k : ℝ)^t*(k : ℝ)^δ := by
    rw [← Real.rpow_natCast (k : ℝ) 12, ← Real.rpow_mul hkpos.le, ← Real.rpow_add hkpos]
    congr 1
    dsimp [t, g]
    ring
  change ((k : ℝ)^12)^((4 : ℝ)/3*(z.re-1/2)-δ/12) ≤ _ at hk
  rw [hexp, hZ] at hk
  have hcmp := cmp (k^3) (k^4) (hk2.trans (le_self_pow₀ hk1 (by decide)))
    (pow_le_pow_right₀ hk1 (by decide))
  push_cast at hcmp
  simp only [← pow_mul, Real.log_pow] at hcmp
  norm_num at hcmp
  have hmul := mul_le_mul_of_nonneg_left hbig (Real.rpow_nonneg hkpos.le t)
  have htarget : (k : ℝ)^(16*(z.re-1/2)-ε) ≤ (k : ℝ)^t :=
    Real.rpow_le_rpow_of_exponent_le hkreal (by change 16*g-ε ≤ 16*g-2*δ; linarith)
  apply htarget.trans
  have hlast : 0 ≤ sample (k ^ 4) := div_nonneg (le_max_right _ _) (by positivity)
  nlinarith only [hmul, hk, hcmp, hlog, hlast]

/-- RH is equivalent to subpower sample mass on arbitrarily late integer blocks
`[k³, k⁴]` for every positive exponent. -/
theorem rh_iff_subpower_sample_mass :
    RiemannHypothesis ↔ ∀ η : ℝ, 0 < η → ∀ A : ℕ, ∃ k ≥ max A 2,
      blockMass (k ^ 3) (k ^ 4) ≤ (k : ℝ) ^ η := by
  constructor
  · intro hRH η hη A
    obtain ⟨N, hN⟩ := eventually_atTop.mp (eventual_logarithmic_bound hRH)
    obtain ⟨T, hT⟩ := eventually_atTop.mp
      (tendsto_natCast_atTop_atTop.eventually (absorb_log 1 (by norm_num) hη))
    let k := max (max A 2) (max N T)
    have hk : max A 2 ≤ k := le_max_left _ _
    have hk1 : 1 ≤ k := by omega
    have h3 : k ≤ k ^ 3 := le_self_pow₀ hk1 (by decide)
    have hNk : N ≤ k := (le_max_left N T).trans (le_max_right _ _)
    have hTk : T ≤ k := (le_max_right N T).trans (le_max_right _ _)
    have hpos : 0 < ((k ^ 3 : ℕ) : ℝ) := by exact_mod_cast (show 0 < k ^ 3 by positivity)
    have hone : 1 ≤ ((k ^ 3 : ℕ) : ℝ) := by exact_mod_cast hk1.trans h3
    have hrecip : 1 / ((k ^ 3 : ℕ) : ℝ) ≤ 1 := (div_le_one hpos).mpr hone
    refine ⟨k, hk, ?_⟩
    have hmass := hN (k ^ 3) (hNk.trans h3) (k ^ 4)
      (pow_le_pow_right₀ hk1 (by decide : 3 ≤ 4))
    push_cast at hmass
    rw [Real.log_pow, Real.log_pow] at hmass
    norm_num at hmass
    have hrecip' : ((k : ℝ) ^ 3)⁻¹ ≤ 1 := by
      simpa only [Nat.cast_pow, one_div] using hrecip
    linarith only [hmass, hrecip', hT k hTk]
  · intro hsmall
    apply D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh
    intro z hz hhalf _
    let η := 4 * (z.re - 1 / 2)
    have hη : 0 < η := mul_pos (by norm_num) (sub_pos.mpr hhalf)
    obtain ⟨T, hT⟩ := eventually_atTop.mp (off_line_zero_forces_sample_mass hz hhalf hη)
    obtain ⟨k, hk, hmass⟩ := hsmall η hη T
    have hk1 : 1 < (k : ℝ) := by
      exact_mod_cast (show 1 < k from lt_of_lt_of_le (by decide) ((le_max_right T 2).trans hk))
    have hstrict : (k : ℝ) ^ η < (k : ℝ) ^ (16 * (z.re - 1 / 2) - η) :=
      Real.rpow_lt_rpow_of_exponent_lt hk1 (by dsimp [η]; linarith)
    exact (not_lt_of_ge ((hT k ((le_max_left T 2).trans hk)).trans hmass)) hstrict

end D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampleMass

#print axioms D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampleMass.prime_mass_le_samples
#print axioms D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampleMass.eventual_logarithmic_bound
#print axioms D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampleMass.off_line_zero_forces_sample_mass
#print axioms D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampleMass.rh_iff_subpower_sample_mass
