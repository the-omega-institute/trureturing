/- GID: D5/S3/Arith/Robin/PriceRecord/RobinMeshLogWindows
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/RobinMeshLogWindows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both critical Robin excursions carry positive gap weight in every late log window. -/

import D5.S3.Analytic.Asymptotics.GapWeightedFourierBlocks
import D5.S3.Arith.Robin.PriceRecord.RobinMeshFourierRecovery
import D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation

/-! Positive gap-weight shares for both critical Robin excursions in late log windows. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Robin.PriceRecord.RobinMeshLogWindows

open GapWeightedFourier (blockAverage gap phase)
open MaximalRealPartProjection (maximalSeries tendsto_exp_mul_tsum_sub_maximalSeries)
open D5.S3.Analytic.Asymptotics.VanishingGapSignTransfer (log_mesh_of_ratio_one)
open D5.S3.Arith.Robin.ActualTwoPriceDefect (strictInteger)
open D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa zero_re_le_abscissa)
open D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff (firstLayerPrice)
open D5.S3.Arith.Robin.PriceRecord.RobinMeshFourierRecovery
  (actual_canonical_samples_fourier_recovery)
open D5.S3.Arith.Robin.PriceRecord.RobinVanishingRelativeGap
  (actual_canonical_samples_signed_asymptotic)
open D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)
open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff actualCoeff_hasSum actualH)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (actualData actualOccurrenceEquiv actualZero)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation (ZeroData.im_ne_zero)
open D5.S3.Weil.ZetaBridge.ZeroDataNonemptyIffInfinite
  (exists_multiplicity hasZetaZeroMultiplicity_iff_analyticOrderAt_eq)

private theorem abs_le_sub_add_excursion {x B c : ℝ} (hc : 0 ≤ c) (hx : |x| ≤ B) :
    |x| ≤ 2 * c - x + (if c < x then 2 * (B - c) else 0) := by
  by_cases h : c < x
  · rw [ite_eq_left h]
    linarith only [hx, le_abs_self x]
  · rw [ite_eq_right h, add_zero]
    have hxc : x ≤ c := le_of_not_gt h
    exact abs_le.mpr ⟨by linarith only [hc], by linarith only [hxc]⟩

/-- A small ordinary mean and a large unit-twisted mean give lower bounds on
the normalized weights of both strict excursions on a finite set. The twisted
sum is divided in `ℂ` by the real total weight, as in a gap-weighted block average. -/
private theorem signed_mass_of_weighted_moments {ι : Type*} (I : Finset ι) {w s : ι → ℝ}
    {u : ι → ℂ} {B c r e : ℝ} (hw : ∀ i ∈ I, 0 ≤ w i)
    (hW : 0 < ∑ i ∈ I, w i) (hc : 0 ≤ c) (hs : ∀ i ∈ I, |s i| ≤ B)
    (hu : ∀ i ∈ I, ‖u i‖ = 1)
    (hmean : |(∑ i ∈ I, w i * s i) / (∑ i ∈ I, w i)| ≤ e)
    (htwist : r ≤ ‖(∑ i ∈ I, (w i : ℂ) * ((s i : ℂ) * u i)) /
      (↑(∑ i ∈ I, w i) : ℂ)‖) :
    (r - e - 2 * c ≤
      2 * (B - c) * ((∑ i ∈ I.filter (fun i => c < s i), w i) / (∑ i ∈ I, w i))) ∧
    (r - e - 2 * c ≤
      2 * (B - c) * ((∑ i ∈ I.filter (fun i => s i < -c), w i) / (∑ i ∈ I, w i))) := by
  let W : ℝ := ∑ i ∈ I, w i
  change 0 < W at hW
  change |(∑ i ∈ I, w i * s i) / W| ≤ e at hmean
  change r ≤ ‖(∑ i ∈ I, (w i : ℂ) * ((s i : ℂ) * u i)) / (W : ℂ)‖ at htwist
  have hnorm : ‖∑ i ∈ I, (w i : ℂ) * ((s i : ℂ) * u i)‖ ≤ ∑ i ∈ I, w i * |s i| := by
    refine norm_sum_le_of_le I fun i hi => ?_
    simp only [norm_mul, Complex.norm_of_nonneg (hw i hi), Complex.norm_real,
      Real.norm_eq_abs, hu i hi, mul_one, le_refl]
  have habs : r ≤ (∑ i ∈ I, w i * |s i|) / W := by
    rw [norm_div, Complex.norm_of_nonneg hW.le] at htwist
    exact htwist.trans (div_le_div_of_nonneg_right hnorm hW.le)
  have positive (t : ι → ℝ) (ht : ∀ i ∈ I, |t i| ≤ B)
      (htmean : |(∑ i ∈ I, w i * t i) / W| ≤ e)
      (htabs : r ≤ (∑ i ∈ I, w i * |t i|) / W) :
      r - e - 2 * c ≤ 2 * (B - c) * ((∑ i ∈ I.filter (fun i => c < t i), w i) / W) := by
    have hsum : (∑ i ∈ I, w i * |t i|) ≤
        (2 * c) * W - (∑ i ∈ I, w i * t i) +
          2 * (B - c) * (∑ i ∈ I.filter (fun i => c < t i), w i) := calc
      _ ≤ ∑ i ∈ I, ((2 * c) * w i - w i * t i +
          (if c < t i then (2 * (B - c)) * w i else 0)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        simpa only [mul_add (w i), mul_sub (w i), mul_ite, mul_zero,
          mul_comm (w i) (2 * c), mul_comm (w i) (2 * (B - c))] using
          mul_le_mul_of_nonneg_left (abs_le_sub_add_excursion hc (ht i hi)) (hw i hi)
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [← Finset.sum_filter (fun i => c < t i) (fun i => (2 * (B - c)) * w i)]
        simp only [← Finset.mul_sum, W]
    have hnormalized := div_le_div_of_nonneg_right hsum hW.le
    simp only [add_div, sub_div, mul_div_assoc, div_self hW.ne', mul_one] at hnormalized
    have hordinary : -e ≤ (∑ i ∈ I, w i * t i) / W := (abs_le.mp htmean).1
    linarith only [htabs.trans hnormalized, hordinary]
  refine ⟨positive s hs hmean habs, ?_⟩
  have hnegative := positive (fun i => -s i)
    (by simpa only [abs_neg] using hs)
    (by simpa only [mul_neg, Finset.sum_neg_distrib, neg_div, abs_neg] using hmean)
    (by simpa only [abs_neg] using habs)
  have hfilter : I.filter (fun i => c < -s i) = I.filter (fun i => s i < -c) := by
    refine Finset.filter_congr fun i _ => ?_
    constructor <;> intro hi <;> linarith only [hi]
  rw [hfilter] at hnegative
  exact hnegative

private theorem first_mesh_crossing {y : ℕ → ℝ} (hm : StrictMono y)
    (hy : Tendsto y atTop atTop) {A : ℕ} {t : ℝ} (hAt : y A < t)
    (hgap : ∀ k ≥ A, gap y k ≤ 1) :
    ∃ a : ℕ, A < a ∧ t ≤ y a ∧ y a < t + 1 ∧ ∀ k, k < a ↔ y k < t := by
  classical
  have he : ∃ k : ℕ, t ≤ y k := ((tendsto_atTop.1 hy) t).exists
  let a := Nat.find he
  have hta : t ≤ y a := Nat.find_spec he
  have ha : A < a := lt_of_not_ge fun h => (hAt.trans_le hta).not_ge (hm.monotone h)
  have hap : a - 1 + 1 = a := Nat.sub_add_cancel (Nat.succ_le_of_lt ((Nat.zero_le A).trans_lt ha))
  have hpred : a - 1 < a := by omega
  have hpredA : A ≤ a - 1 := by omega
  have hprev : y (a - 1) < t := lt_of_not_ge (Nat.find_min he hpred)
  have hcell := hgap (a - 1) hpredA
  rw [gap, hap] at hcell
  refine ⟨a, ha, hta, by linarith only [hprev, hcell], fun k => ⟨?_, ?_⟩⟩
  · exact fun hk => lt_of_not_ge (Nat.find_min he hk)
  · exact fun hk => lt_of_not_ge fun hka => hk.not_ge (hta.trans (hm.monotone hka))

private theorem maximalSeries_eq_phase_sum (c : ℕ → ℂ) (z : ℕ → ℂ) (β t : ℝ) :
    maximalSeries c z β t =
      ∑' j, (if (z j).re = β then c j else 0) * phase (z j).im t := by
  change (∑' j, if (z j).re = β then
    c j * Complex.exp ((t : ℂ) * (z j - (β : ℂ))) else 0) = _
  apply tsum_congr
  intro j
  by_cases hj : (z j).re = β
  · have hz : z j - (β : ℂ) = Complex.I * ((z j).im : ℂ) := by
      apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im, hj]
    have harg : (t : ℂ) * (Complex.I * ((z j).im : ℂ)) =
        Complex.I * ((z j).im : ℂ) * (t : ℂ) := by ring
    simp only [ite_eq_left hj, phase, hz, harg]
  · simp [hj]

/-- Every sufficiently late logarithmic window of one fixed width contains a
positive fraction of the full left-cell gap weight in each strict critical
Robin excursion. The sample indices are exactly the left endpoints in the
window, and the denominator is their total full gap weight. -/
theorem actual_attained_canonical_critical_log_windows {ρ : ℂ}
    (hρ : IsNontrivialZero ρ) (hhalf : 1 / 2 < ρ.re) (hρΘ : ρ.re = zeroAbscissa)
    {N : ℕ → ℕ} (hN : StrictMono N) (hpos : 0 < N 0)
    (hratio : Tendsto (fun k => (N (k + 1) : ℝ) / (N k : ℝ)) atTop (𝓝 1)) :
    let y : ℕ → ℝ := fun k => Real.log (N k : ℝ)
    let s : ℕ → ℝ := fun k => Real.rpow (N k : ℝ) (1 - zeroAbscissa) * y k *
      robinLogMargin (strictInteger (firstLayerPrice ((N k : ℝ) + 1)))
    ∃ T H c d : ℝ, 0 < H ∧ 0 < c ∧ 0 < d ∧ ∀ t ≥ T,
      ∃ a b : ℕ, a < b ∧ (∀ k, k ∈ Finset.Ico a b ↔ t ≤ y k ∧ y k < t + H) ∧
        d ≤ (∑ k ∈ (Finset.Ico a b).filter (fun k => c < s k), gap y k) / (y b - y a) ∧
        d ≤ (∑ k ∈ (Finset.Ico a b).filter (fun k => s k < -c), gap y k) / (y b - y a) := by
  classical
  let y : ℕ → ℝ := fun k => Real.log (N k : ℝ)
  let s : ℕ → ℝ := fun k => Real.rpow (N k : ℝ) (1 - zeroAbscissa) * y k *
      robinLogMargin (strictInteger (firstLayerPrice ((N k : ℝ) + 1)))
  let freq : ℕ → ℝ := fun j => (actualZero j).im
  let coeff : ℕ → ℂ := fun j => if (actualZero j).re = ρ.re then -actualCoeff j else 0
  let S : ℕ → ℂ := fun k => ∑' j, coeff j * phase (freq j) (y k)
  let L : ℂ := -(analyticOrderNatAt riemannZeta ρ : ℂ) / (ρ * (1 - ρ))
  have hstrip (z : ℂ) (hz : IsNontrivialZero z) : z.re ≤ ρ.re :=
    (zero_re_le_abscissa hz).trans_eq hρΘ.symm
  have hx : Tendsto (fun k => (N k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN.tendsto_atTop
  obtain ⟨hy, hgap⟩ := log_mesh_of_ratio_one hx hratio
  change Tendsto y atTop atTop at hy
  change Tendsto (gap y) atTop (𝓝 0) at hgap
  have hm : StrictMono y := by
    intro i j hij
    exact Real.log_lt_log (Nat.cast_pos.mpr (hpos.trans_le (hN.monotone (Nat.zero_le i))))
      (Nat.cast_lt.mpr (hN hij))
  have hz (j : ℕ) : IsNontrivialZero (actualZero j) :=
    actualData.zero_isNontrivial (actualOccurrenceEquiv j).1
  have hc : Summable (fun j => ‖coeff j‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ actualCoeff_hasSum.summable.norm
    intro j
    by_cases hj : (actualZero j).re = ρ.re <;> simp [coeff, hj]
  have hproj := tendsto_exp_mul_tsum_sub_maximalSeries
    (a := fun j => -actualCoeff j) (z := actualZero) (Θ := ρ.re)
    (by simpa only [norm_neg] using actualCoeff_hasSum.summable.norm)
    (fun j => hstrip _ (hz j))
  have hproj' : Tendsto (fun k => -((Real.exp (-ρ.re * y k) : ℂ) * actualH (y k)) - S k)
      atTop (𝓝 0) := by
    apply (hproj.comp hy).congr
    intro k
    simp only [Function.comp_apply, actualH, S, coeff, freq, maximalSeries_eq_phase_sum,
      neg_mul, tsum_neg, mul_neg]
  have hsample : Tendsto (fun k => (s k : ℂ) + (Real.exp (-ρ.re * y k) : ℂ) * actualH (y k))
      atTop (𝓝 0) := by
    simpa only [s, y, hρΘ, ite_eq_right (hρΘ ▸ hhalf.ne'), Complex.ofReal_zero, sub_zero] using
      actual_canonical_samples_signed_asymptotic hhalf.le hρ.2.2 hstrip hN.tendsto_atTop
  have he : Tendsto (fun k => (s k : ℂ) - S k) atTop (𝓝 0) := by
    have hcombined := hsample.add hproj'
    rw [zero_add] at hcombined
    exact hcombined.congr (fun k => by ring)
  have hfiber_zero : (∑' j, if freq j = 0 then coeff j else 0) = 0 := by
    have him (j : ℕ) : freq j ≠ 0 :=
      ZeroData.im_ne_zero actualData (actualOccurrenceEquiv j).1 (hz j)
    simp [him]
  have hfiber : (∑' j, if freq j = ρ.im then coeff j else 0) = L := by
    have hsum := GapWeightedFourier.tendsto_average_modulated_series hm hy hgap
      coeff freq hc ρ.im he
      (show ∀ k, (s k : ℂ) = S k + ((s k : ℂ) - S k) from fun k => by ring)
    have hactual : Tendsto (GapWeightedFourier.average y
        (fun k => (s k : ℂ) * phase (-ρ.im) (y k))) atTop (𝓝 L) := by
      simpa only [s, y, L, ← hρΘ, ite_eq_right hhalf.ne', Complex.ofReal_zero, sub_zero] using
        actual_canonical_samples_fourier_recovery ρ hhalf.le hρ.2.2 hstrip hN hpos hratio
    exact tendsto_nhds_unique hsum hactual
  have hL : L ≠ 0 := by
    obtain ⟨m, hmultiplicity⟩ := exists_multiplicity hρ
    have horder : analyticOrderNatAt riemannZeta ρ = m := by
      have h := (hasZetaZeroMultiplicity_iff_analyticOrderAt_eq hρ).mp hmultiplicity
      simp [analyticOrderNatAt, h]
    have hmcast : (m : ℂ) ≠ 0 := by exact_mod_cast hmultiplicity.1.ne'
    have hρ0 : ρ ≠ 0 := fun h => hρ.2.1.ne' (by simpa using congrArg Complex.re h)
    have hρ1 : ρ ≠ 1 := fun h => hρ.2.2.ne (by simpa using congrArg Complex.re h)
    dsimp only [L]
    rw [horder]
    exact div_ne_zero (neg_ne_zero.mpr hmcast) (mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1.symm))
  have hLpos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  let ε : ℝ := ‖L‖ / 8
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨A₀, H₀, hH₀, hplain⟩ :=
    GapWeightedFourier.eventually_blockAverage_modulated_series hm hgap coeff freq hc 0
      (fun k => (s k : ℂ)) he hε
  obtain ⟨A₁, H₁, _, htwist⟩ :=
    GapWeightedFourier.eventually_blockAverage_modulated_series hm hgap coeff freq hc ρ.im
      (fun k => (s k : ℂ)) he hε
  have hunit (ν t : ℝ) : ‖phase ν t‖ = 1 := by
    rw [phase, mul_assoc, ← Complex.ofReal_mul, Complex.norm_exp_I_mul_ofReal]
  let B : ℝ := (∑' j, ‖coeff j‖) + ‖L‖ + 1
  have hB : 0 < B - ε := by
    have hcpos : 0 ≤ ∑' j, ‖coeff j‖ := tsum_nonneg fun j => norm_nonneg _
    dsimp [B, ε]
    linarith only [hcpos, hLpos]
  obtain ⟨A₂, hA₂⟩ := eventually_atTop.1
    ((tendsto_zero_iff_norm_tendsto_zero.mp he).eventually (gt_mem_nhds zero_lt_one))
  obtain ⟨A₃, hA₃⟩ := eventually_atTop.1 (hgap.eventually (gt_mem_nhds zero_lt_one))
  let A : ℕ := max (max A₀ A₁) (max A₂ A₃)
  let H : ℝ := max H₀ H₁ + 1
  let d : ℝ := (‖L‖ / 2) / (2 * (B - ε))
  have hH : 0 < H := by dsimp [H]; linarith only [hH₀, le_max_left H₀ H₁]
  refine ⟨y (A + 1), H, ε, d, hH, hε, by dsimp [d]; positivity, fun t ht => ?_⟩
  have hAt : y A < t := (hm (Nat.lt_succ_self A)).trans_le ht
  have hgap₁ (k : ℕ) (hk : A ≤ k) : gap y k ≤ 1 :=
    (hA₃ k (le_trans (le_max_right A₂ A₃) (le_trans (le_max_right _ _) hk))).le
  obtain ⟨a, ha, _, hat, hleft⟩ := first_mesh_crossing hm hy hAt hgap₁
  obtain ⟨b, _, htb, _, hright⟩ :=
    first_mesh_crossing hm hy (hAt.trans (lt_add_of_pos_right t hH)) hgap₁
  have hspan : max H₀ H₁ ≤ y b - y a := by dsimp [H] at htb; linarith only [htb, hat]
  have hab : a < b := lt_of_not_ge fun h =>
    (show y a < y b by linarith only [hspan, hH₀, le_max_left H₀ H₁]).not_ge (hm.monotone h)
  refine ⟨a, b, hab, fun k => ?_, ?_⟩
  · rw [Finset.mem_Ico, hright]
    have hk : a ≤ k ↔ t ≤ y k := by
      rw [← not_lt, ← not_lt, hleft]
    rw [hk]
  · let I := Finset.Ico a b
    have hW : (∑ k ∈ I, gap y k) = y b - y a := Finset.sum_Ico_sub (f := y) hab.le
    have hposW : 0 < (∑ k ∈ I, gap y k) := by rw [hW]; exact sub_pos.mpr (hm hab)
    have hbound (k : ℕ) (hk : k ∈ I) : |s k| ≤ B := by
      have hak : A ≤ k := ha.le.trans (Finset.mem_Ico.mp hk).1
      have happrox := hA₂ k (le_trans (le_max_left A₂ A₃) (le_trans (le_max_right _ _) hak))
      have hS : ‖S k‖ ≤ ∑' j, ‖coeff j‖ :=
        tsum_of_norm_bounded hc.hasSum (fun j => by rw [norm_mul, hunit, mul_one])
      have hs := (norm_sub_le_norm_sub_add_norm_sub (s k : ℂ) (S k) 0)
      simp only [sub_zero, Complex.norm_real, Real.norm_eq_abs] at hs
      dsimp [B]
      linarith only [hs, happrox, hS, hLpos]
    have hmean := hplain (a := a) (b := b)
      ((le_max_left A₀ A₁).trans ((le_max_left _ _).trans ha.le)) hab
      ((le_max_left H₀ H₁).trans hspan)
    simp only [hfiber_zero, sub_zero, neg_zero, phase, Complex.ofReal_zero, mul_zero,
      zero_mul, Complex.exp_zero, mul_one] at hmean
    have hmean' : |(∑ k ∈ I, gap y k * s k) / (∑ k ∈ I, gap y k)| ≤ ε := by
      rw [hW]
      simpa only [blockAverage, ← Complex.ofReal_mul, ← Complex.ofReal_sum, ← Complex.ofReal_div,
        Complex.norm_real, Real.norm_eq_abs, I] using hmean
    have hmode := htwist (a := a) (b := b)
      ((le_max_right A₀ A₁).trans ((le_max_left _ _).trans ha.le)) hab
      ((le_max_right H₀ H₁).trans hspan)
    rw [hfiber] at hmode
    have hlower : ‖L‖ - ε ≤ ‖blockAverage y (fun k => (s k : ℂ) * phase (-ρ.im) (y k)) a b‖ := by
      have hh := norm_sub_norm_le L (blockAverage y (fun k => (s k : ℂ) * phase (-ρ.im) (y k)) a b)
      rw [norm_sub_rev] at hh
      linarith only [hh, hmode]
    obtain ⟨hp, hn⟩ := signed_mass_of_weighted_moments I (r := ‖L‖ - ε)
      (w := gap y) (s := s) (u := fun k => phase (-ρ.im) (y k))
      (fun k _ => sub_nonneg.mpr (hm (Nat.lt_succ_self k)).le)
      hposW hε.le hbound (fun k _ => hunit _ _) hmean' (by rw [hW]; exact hlower)
    rw [hW] at hp hn
    have hre : ‖L‖ - ε - ε - 2 * ε = ‖L‖ / 2 := by dsimp [ε]; ring
    rw [hre] at hp hn
    have hden : 0 < 2 * (B - ε) := by positivity
    exact ⟨(div_le_iff₀' hden).2 hp, (div_le_iff₀' hden).2 hn⟩

end D5.S3.Arith.Robin.PriceRecord.RobinMeshLogWindows
