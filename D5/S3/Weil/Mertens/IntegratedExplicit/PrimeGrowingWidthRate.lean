/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthRate
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthRate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A critical spectral gap gives a positive logarithmic prime-tail phase error. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeCriticalResidual
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeGrowingWidthCluster

/-! The signed root-scale correction accumulates where the leading profile is nonpositive. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZeroSum (IsNontrivialZero)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimeGrowingWidthRate

open MaximalRealPartProjection (maximalSeries summable_norm_maximalTerm)
open PrimeOnlyTailCorrection (primeTail prime_integrable prime_power_window_correction)
open PrimePhaseCluster (phaseOrbit phaseProfile phaseProfile_continuous phaseProfile_on_orbit
  phaseWindow phaseWindow_continuous primeMass_exp_substitution signedInput
  prime_tail_mass_cluster_iff_of_upper_bound)
open PrimeGrowingWidthCluster (coeffMass phaseDensity phaseDensity_bound phaseDensity_continuous
  phaseWindowInfinite phaseWindowInfinite_sub_window)
open PrimeCriticalResidual (rootTerm norm_rootTerm summable_norm_rootTerm
  scaled_shift_eq_rootTerm eventually_prime_tail_root_scale)
open PrimeAttainedCriticalWidth (prime_tail_zero_liminf_iff_le_critical_width)
open PrimeAttainedShortWindows (unaveraged_formula)
open ActualFilteredExplicitFormula (averagedActualCorrection averagedActualCorrection_bounds)
open ZeroAbscissaPower (actual_zero)

private def profile (β u : ℝ) : ℝ := phaseProfile Complex.re β (phaseOrbit u) 0

private def correctionDensity (β u : ℝ) : ℝ :=
  Real.exp ((β - 1 / 2) * u) * (max (-signedInput β u) 0 - max (-profile β u) 0)

private theorem profile_eq (β u : ℝ) :
    profile β u = -(maximalSeries actualCoeff actualZero β u).re := by
  simpa only [profile, add_zero] using phaseProfile_on_orbit β u 0

private theorem profile_negative_continuous (β : ℝ) :
    Continuous (fun u => max (-profile β u) 0) := by
  apply Continuous.max _ continuous_const
  exact ((phaseProfile_continuous Complex.re β).comp
    ((show Continuous phaseOrbit by unfold phaseOrbit; fun_prop).prodMk continuous_const)).neg

private theorem correctionDensity_continuousOn (β : ℝ) :
    ContinuousOn (correctionDensity β) (Ici 0) := by
  have hq : ContinuousOn (signedInput β) (Ici 0) := by
    unfold signedInput
    exact (by fun_prop : Continuous fun u : ℝ => Real.exp ((1 - β) * u)).continuousOn.mul
      (prime_integrable.continuousOn_Ici_primitive_Ioi.comp Real.continuous_exp.continuousOn
        (fun _ hu => Real.one_le_exp hu))
  unfold correctionDensity
  exact (by fun_prop : Continuous fun u : ℝ => Real.exp ((β - 1 / 2) * u)).continuousOn.mul
    ((hq.neg.sup continuousOn_const).sub (profile_negative_continuous β).continuousOn)

private theorem root_spectral_bound {β γ u : ℝ} (hu : 0 ≤ u)
    (hmax : ∀ k : ℕ, (actualZero k).re ≤ β)
    (hbelow : ∀ k : ℕ, (actualZero k).re < β → (actualZero k).re ≤ γ) :
    ‖(Real.exp (-u / 2) : ℂ) * actualH u -
        (Real.exp ((β - 1 / 2) * u) : ℂ) * maximalSeries actualCoeff actualZero β u‖ ≤
      coeffMass * Real.exp ((γ - 1 / 2) * u) := by
  let lower : Set ℕ := {k | (actualZero k).re < β}
  have hroot := (summable_norm_rootTerm u).of_norm
  have hline := ((summable_norm_maximalTerm (z := actualZero) (Θ := β)
    actualCoeff_hasSum.summable.norm u).of_norm).mul_left
      (Real.exp ((β - 1 / 2) * u) : ℂ)
  have hscaled : (Real.exp (-u / 2) : ℂ) * actualH u = ∑' k, rootTerm u k := by
    rw [actualH, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    have hzero : (0 - 1 / 2 : ℝ) * u = -u / 2 := by ring
    simpa only [hzero, Complex.ofReal_zero, sub_zero] using scaled_shift_eq_rootTerm 0 u k
  have hsplit :
      (∑' k, rootTerm u k) -
        (Real.exp ((β - 1 / 2) * u) : ℂ) * maximalSeries actualCoeff actualZero β u =
      ∑' k : lower, rootTerm u k := by
    rw [maximalSeries, ← tsum_mul_left, ← hroot.tsum_sub hline, tsum_subtype]
    apply tsum_congr
    intro k
    change rootTerm u k - (Real.exp ((β - 1 / 2) * u) : ℂ) *
      (if (actualZero k).re = β then
        actualCoeff k * Complex.exp ((u : ℂ) * (actualZero k - (β : ℂ))) else 0) =
        lower.indicator (rootTerm u) k
    by_cases heq : (actualZero k).re = β
    · have hk : k ∉ lower := fun h => (ne_of_lt h) heq
      rw [ite_eq_left heq, scaled_shift_eq_rootTerm, sub_self, indicator_of_notMem hk]
    · have hk : k ∈ lower := lt_of_le_of_ne (hmax k) heq
      rw [ite_eq_right heq, mul_zero, sub_zero, indicator_of_mem hk]
  rw [hscaled, hsplit]
  calc
    _ ≤ ∑' k : lower, ‖rootTerm u k‖ :=
      norm_tsum_le_tsum_norm ((summable_norm_rootTerm u).subtype lower)
    _ ≤ ∑' k : lower, ‖actualCoeff k‖ * Real.exp ((γ - 1 / 2) * u) := by
      refine Summable.tsum_le_tsum (fun k => ?_) ((summable_norm_rootTerm u).subtype lower)
        ((actualCoeff_hasSum.summable.norm.subtype lower).mul_right _)
      rw [norm_rootTerm]
      gcongr
      exact hbelow k k.2
    _ = (∑' k : lower, ‖actualCoeff k‖) * Real.exp ((γ - 1 / 2) * u) := tsum_mul_right
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (actualCoeff_hasSum.summable.norm.tsum_subtype_le _ lower fun _ => norm_nonneg _)
      (Real.exp_nonneg _)

private theorem signed_error_bound {β γ : ℝ} (hγ : 1 / 2 ≤ γ)
    (hmax : ∀ z : ℂ, IsNontrivialZero z → z.re ≤ β)
    (hbelow : ∀ z : ℂ, IsNontrivialZero z → z.re < β → z.re ≤ γ) :
    ∃ K > (0 : ℝ), ∀ᶠ u : ℝ in atTop,
      |Real.exp ((β - 1 / 2) * u) * (signedInput β u - profile β u)| ≤
        K * Real.exp ((γ - 1 / 2) * u) := by
  let L := Real.log (2 * Real.pi)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hpower := (prime_power_window_correction.1.comp Real.tendsto_exp_atTop).eventually
    (gt_mem_nhds (by norm_num : (2 : ℝ) < 3))
  have hpower' := (prime_power_window_correction.1.comp Real.tendsto_exp_atTop).eventually
    (lt_mem_nhds (by norm_num : (0 : ℝ) < 2))
  refine ⟨coeffMass + L + 3, by dsimp [coeffMass]; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.log 2), hpower, hpower'] with u hu hp₁ hp₀
  have hu₀ : 0 ≤ u := (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hu
  have hdirac : Measure.dirac (0 : ℝ) (Icc 0 0) = 1 :=
    Measure.dirac_apply_of_mem (show (0 : ℝ) ∈ Icc 0 0 from ⟨le_rfl, le_rfl⟩)
  let E := Real.exp (u / 2)
  let S := Real.exp ((β - 1 / 2) * u)
  let R := averagedActualCorrection (Measure.dirac 0) u
  let Z := (Real.exp (-u / 2) : ℂ) * actualH u -
    (S : ℂ) * maximalSeries actualCoeff actualZero β u
  let P := E * (Q (Real.exp u) - primeTail (Real.exp u))
  have hsqrt : Real.sqrt (Real.exp u) = E := by rw [Real.sqrt_eq_rpow, ← Real.exp_mul]; congr 1; ring
  change Real.sqrt (Real.exp u) * (Q (Real.exp u) - primeTail (Real.exp u)) < 3 at hp₁
  change 0 < Real.sqrt (Real.exp u) * (Q (Real.exp u) - primeTail (Real.exp u)) at hp₀
  rw [hsqrt] at hp₁ hp₀
  have hR := averagedActualCorrection_bounds _ hdirac hu₀
  change -(L * Real.exp (-u)) ≤ R ∧ R ≤ 0 at hR
  have hER : |E * R| ≤ L := by
    rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _), abs_of_nonpos hR.2]
    calc
      _ ≤ E * (L * Real.exp (-u)) :=
        mul_le_mul_of_nonneg_left (neg_le_of_neg_le hR.1) (Real.exp_nonneg _)
      _ = L * Real.exp (-u / 2) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
      _ ≤ L := mul_le_of_le_one_right hL (Real.exp_le_one_iff.mpr (by linarith))
  have hE₁ : S * Real.exp ((1 - β) * u) = E := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE₂ : E * Real.exp (-u) = Real.exp (-u / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hres : S * (signedInput β u - profile β u) = -Z.re + E * R - P := by
    rw [signedInput, profile_eq, sub_neg_eq_add, mul_add, ← mul_assoc, hE₁]
    have hQ := unaveraged_formula hu
    change Q (Real.exp u) = _ + R at hQ
    have hQscaled := congrArg (E * ·) hQ
    simp only [mul_add, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, mul_neg] at hQscaled
    dsimp only [Z, P]
    rw [Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, ← hE₂]
    linarith only [hQscaled]
  have hZ : ‖Z‖ ≤ coeffMass * Real.exp ((γ - 1 / 2) * u) :=
    root_spectral_bound hu₀ (fun k => hmax _ (actual_zero k))
      (fun k => hbelow _ (actual_zero k))
  have hweight : 1 ≤ Real.exp ((γ - 1 / 2) * u) :=
    Real.one_le_exp (mul_nonneg (sub_nonneg.mpr hγ) hu₀)
  rw [hres]
  calc
    _ ≤ |-Z.re| + |E * R| + |P| :=
      have htriangle : |(-Z.re + E * R) - P| ≤ |-Z.re + E * R| + |P| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (-Z.re + E * R) 0 P
      htriangle.trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ (coeffMass * Real.exp ((γ - 1 / 2) * u) + L) + 3 := by
      rw [abs_neg, abs_of_nonneg (show 0 ≤ P from hp₀.le)]
      exact add_le_add (add_le_add ((Complex.abs_re_le_norm _).trans hZ) hER) hp₁.le
    _ ≤ _ := by nlinarith only [hweight, mul_nonneg hL (sub_nonneg.mpr hweight)]

private theorem eventually_signed_margin {β : ℝ} (hβ : 1 / 2 < β)
    (hmax : ∀ z : ℂ, IsNontrivialZero z → z.re ≤ β)
    (hgap : ∀ z : ℂ, IsNontrivialZero z → z.re < β → z.re ≤ 1 / 2) :
    ∀ᶠ u : ℝ in atTop, Real.exp ((β - 1 / 2) * u) * (signedInput β u - profile β u) ≤ -1 := by
  have hempty : IsEmpty {k : ℕ // 1 / 2 < (actualZero k).re ∧ (actualZero k).re < β} :=
    ⟨fun k => (not_lt_of_ge (hgap _ (actual_zero k) k.2.2)) k.2.1⟩
  filter_upwards [eventually_prime_tail_root_scale.2 1 (by norm_num)
    (by linarith only [firstLiMass_lt_one])] with u hu
  have h := hu β hβ hmax
  rw [tsum_empty, add_zero] at h
  rw [signedInput, profile_eq, mul_sub, ← mul_assoc, ← Real.exp_add,
    show (β - 1 / 2) * u + (1 - β) * u = u / 2 by ring]
  linarith only [h]

private theorem wide_profile_mass (ρ : ℂ) (hρ : IsNontrivialZero ρ)
    (hβ : 1 / 2 < ρ.re) (hmax : ∀ z : ℂ, IsNontrivialZero z → z.re ≤ ρ.re) :
    ∃ W > (0 : ℝ), ∃ m > (0 : ℝ), ∀ t : ℝ,
      m ≤ ∫ u in (t - W)..t, max (-profile ρ.re u) 0 := by
  let β := ρ.re
  obtain ⟨Wstar, ⟨hstar, hwidth⟩, _⟩ :=
    prime_tail_zero_liminf_iff_le_critical_width ρ hρ hβ hmax
  let W := Wstar + 1
  have hW : 0 < W := by dsimp [W]; positivity
  let mass (B : ℝ) :=
    (∫ x in B * Real.exp (-W)..B, max (-primeTail x) 0 / Real.sqrt x) / B ^ (β - 1 / 2)
  have hlim : Filter.liminf mass atTop ≠ 0 := fun h =>
    (show ¬ W ≤ Wstar by dsimp [W]; linarith) ((hwidth W hW.le).1 h)
  have hpos (h : ℕ → Circle) (hh : h ∈ closure (range phaseOrbit)) :
      0 < phaseWindow Complex.re β W h := by
    have hnonneg : 0 ≤ phaseWindow Complex.re β W h :=
      intervalIntegral.integral_nonneg hW.le fun s _ => (phaseDensity_bound _ _ _ s).1
    refine lt_of_le_of_ne hnonneg ?_
    intro heq
    have hcl : MapClusterPt 0 atTop mass :=
      (prime_tail_mass_cluster_iff_of_upper_bound β hβ hmax W hW.le 0).2 ⟨h, hh, heq⟩
    have hev : ∀ᶠ B : ℝ in atTop, 0 ≤ mass B := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
      have hAB : B * Real.exp (-W) ≤ B := mul_le_of_le_one_right hB.le
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hW.le))
      exact div_nonneg (intervalIntegral.integral_nonneg_of_forall hAB
        PrimeAttainedCriticalWidth.integrand_nonneg) (Real.rpow_nonneg hB.le _)
    have hcobdd : atTop.IsCoboundedUnder (· ≥ ·) mass := .of_frequently_le
      ((hcl.frequently (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).mono fun _ hB => hB.le)
    exact hlim ((hcl.liminf_le (isBoundedUnder_of_eventually_ge hev)).antisymm
      (le_liminf_of_le hcobdd hev))
  have hH : (closure (range phaseOrbit)).Nonempty :=
    ⟨phaseOrbit 0, subset_closure (mem_range_self _)⟩
  obtain ⟨h, hh, hmin⟩ := isClosed_closure.isCompact.exists_isMinOn hH
    (phaseWindow_continuous β W).continuousOn
  refine ⟨W, hW, phaseWindow Complex.re β W h, hpos h hh, fun t => ?_⟩
  have horbit := hmin (subset_closure (mem_range_self t))
  have htranslate (s : ℝ) :
      phaseProfile Complex.re β (phaseOrbit t) (-s) = profile β (t - s) := by
    rw [profile_eq, phaseProfile_on_orbit, sub_eq_add_neg]
  refine horbit.trans ?_
  unfold phaseWindow
  calc
    _ ≤ ∫ s in 0..W, max (-profile β (t - s)) 0 := by
      apply intervalIntegral.integral_mono_on hW.le
        ((phaseDensity_continuous _ _ _).intervalIntegrable _ _)
        (((profile_negative_continuous β).comp (by fun_prop)).intervalIntegrable _ _)
      intro s hs
      rw [phaseDensity, htranslate]
      exact mul_le_of_le_one_left (le_max_right _ _)
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hs.1))
    _ = _ := by
      simpa only [sub_zero] using intervalIntegral.integral_comp_sub_left
        (a := 0) (b := W) (fun u => max (-profile β u) 0) t

private theorem correction_minorant {s q f d M : ℝ} (hs : 0 < s) (hd : 0 < d)
    (hM : 0 ≤ M) (hf : max (-f) 0 ≤ M) (hgap : s * (q - f) ≤ -d) :
    d / (M + 1) * max (-f) 0 ≤ s * (max (-q) 0 - max (-f) 0) := by
  have hqf : q ≤ f := sub_nonpos.mp (nonpos_of_mul_nonpos_right (hgap.trans (neg_nonpos.mpr hd.le)) hs)
  by_cases hsign : f ≤ 0
  · rw [max_eq_left (neg_nonneg.mpr hsign)] at hf ⊢
    rw [max_eq_left (neg_nonneg.mpr (hqf.trans hsign))]
    have hden : 0 < M + 1 := by positivity
    calc
      _ ≤ d / (M + 1) * (M + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hd.le hden.le)
      _ = d := div_mul_cancel₀ _ hden.ne'
      _ ≤ _ := by rw [show -q - -f = -(q - f) by ring, mul_neg]; linarith
  · rw [max_eq_right (neg_nonpos.mpr (le_of_not_ge hsign)), mul_zero, sub_zero]
    exact mul_nonneg hs.le (le_max_right _ _)

private theorem correction_abs_le (β u : ℝ) :
    |correctionDensity β u| ≤
      |Real.exp ((β - 1 / 2) * u) * (signedInput β u - profile β u)| := by
  have hlip := abs_max_sub_max_le_abs (-signedInput β u) (-profile β u) (0 : ℝ)
  have heq : -signedInput β u - -profile β u = -(signedInput β u - profile β u) := by ring
  rw [heq, abs_neg] at hlip
  rw [correctionDensity, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left hlip (abs_nonneg _)

private theorem integral_affine_lower_of_window {D : ℝ → ℝ} {T W m : ℝ}
    (hW : 0 < W) (hm : 0 < m)
    (hint : ∀ a b : ℝ, T ≤ a → a ≤ b → IntervalIntegrable D volume a b)
    (hnonneg : ∀ u ≥ T, 0 ≤ D u)
    (hwindow : ∀ a ≥ T, m ≤ ∫ u in a..(a + W), D u)
    {t : ℝ} (ht : T ≤ t) :
    m / W * (t - T - W) ≤ ∫ u in T..t, D u := by
  let n := ⌊(t - T) / W⌋₊
  let e (j : ℕ) := T + (j : ℝ) * W
  have hfloor : (n : ℝ) ≤ (t - T) / W := Nat.floor_le (div_nonneg (sub_nonneg.mpr ht) hW.le)
  have hnext : (t - T) / W < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hbase (j : ℕ) : T ≤ e j := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hW.le)
  have hstep (j : ℕ) : e (j + 1) = e j + W := by dsimp [e]; push_cast; ring
  have hsum (j : ℕ) : (j : ℝ) * m ≤ ∫ u in T..(e j), D u := by
    induction j with
    | zero => simp [e]
    | succ j ih =>
      have hord : e j ≤ e (j + 1) := by rw [hstep]; linarith
      have hadj := intervalIntegral.integral_add_adjacent_intervals
        (hint T (e j) le_rfl (hbase j)) (hint (e j) (e (j + 1)) (hbase j) hord)
      have hwin := hwindow (e j) (hbase j)
      rw [← hstep] at hwin
      rw [← hadj, Nat.cast_succ, add_mul, one_mul]
      exact add_le_add ih hwin
  have hend : e n ≤ t := by dsimp [e]; linarith only [(le_div_iff₀ hW).1 hfloor]
  have hrem : 0 ≤ ∫ u in (e n)..t, D u :=
    intervalIntegral.integral_nonneg hend fun u hu => hnonneg u ((hbase n).trans hu.1)
  have hlength : t - T - W ≤ (n : ℝ) * W := by linarith only [(div_lt_iff₀ hW).1 hnext]
  calc
    _ ≤ m / W * ((n : ℝ) * W) := mul_le_mul_of_nonneg_left hlength (by positivity)
    _ = (n : ℝ) * m := by field_simp
    _ ≤ _ := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hint T (e n) le_rfl (hbase n)) (hint (e n) t (hbase n) hend)]
      exact (hsum n).trans (le_add_of_nonneg_right hrem)

private theorem prime_mass_sub_phase_window {β a B : ℝ} (ha : 2 ≤ a) (hab : a ≤ B) :
    (∫ x in a..B, max (-primeTail x) 0 / Real.sqrt x) -
      B ^ (β - 1 / 2) *
        phaseWindow Complex.re β (Real.log B - Real.log a) (phaseOrbit (Real.log B)) =
    ∫ u in Real.log a..Real.log B, correctionDensity β u := by
  have ha₀ : 0 < a := (by norm_num : (0 : ℝ) < 2).trans_le ha
  have hB₀ : 0 < B := ha₀.trans_le hab
  let t := Real.log B
  let W := t - Real.log a
  let p := β - 1 / 2
  have hW : 0 ≤ W := sub_nonneg.mpr (Real.log_le_log ha₀ hab)
  have ha₁ : 1 ≤ a := one_le_two.trans ha
  have haLog : 0 ≤ Real.log a := Real.log_nonneg ha₁
  have hWt : W ≤ t := sub_le_self _ haLog
  have htW : t - W = Real.log a := by dsimp [W]; ring
  have hleft : Real.exp t * Real.exp (-W) = a := by
    rw [← Real.exp_add, ← sub_eq_add_neg, htW, Real.exp_log ha₀]
  have hBexp : Real.exp t = B := Real.exp_log hB₀
  have hmass := primeMass_exp_substitution β W t hW hWt
  rw [hleft, hBexp] at hmass
  have hmass' := (div_eq_iff (Real.rpow_pos_of_pos hB₀ p).ne').1 hmass
  let f (s : ℝ) := Real.exp (-p * s) * max (-signedInput β (t - s)) 0
  let g (s : ℝ) := phaseDensity Complex.re β (phaseOrbit t) s
  have hfi : IntervalIntegrable f volume 0 W := by
    apply ContinuousOn.intervalIntegrable_of_Icc hW
    have hq : ContinuousOn (fun s => signedInput β (t - s)) (Icc 0 W) := by
      unfold signedInput
      exact (by fun_prop : Continuous fun s : ℝ => Real.exp ((1 - β) * (t - s))).continuousOn.mul
        (prime_integrable.continuousOn_Ici_primitive_Ioi.comp
          (by fun_prop : Continuous fun s : ℝ => Real.exp (t - s)).continuousOn
          (fun s hs => Real.one_le_exp (sub_nonneg.mpr (hs.2.trans hWt))))
    exact (by fun_prop : Continuous fun s : ℝ => Real.exp (-p * s)).continuousOn.mul
      (hq.neg.sup continuousOn_const)
  have hgi : IntervalIntegrable g volume 0 W :=
    (phaseDensity_continuous _ _ _).intervalIntegrable _ _
  change (∫ x in a..B, _) - B ^ p * (∫ s in 0..W, g s) =
    ∫ u in Real.log a..t, correctionDensity β u
  change (∫ x in a..B, _) = (∫ s in 0..W, f s) * B ^ p at hmass'
  rw [hmass', mul_comm (∫ s in 0..W, f s), ← mul_sub, ← intervalIntegral.integral_sub hfi hgi,
    ← intervalIntegral.integral_const_mul]
  have hreflect := intervalIntegral.integral_comp_sub_left
    (a := 0) (b := W) (correctionDensity β) t
  rw [htW, sub_zero] at hreflect
  rw [← hreflect]
  apply intervalIntegral.integral_congr
  intro s _
  have hphase : phaseProfile Complex.re β (phaseOrbit t) (-s) = profile β (t - s) := by
    rw [profile_eq, phaseProfile_on_orbit, sub_eq_add_neg]
  have hscale : B ^ p * Real.exp (-p * s) = Real.exp (p * (t - s)) := by
    rw [Real.rpow_def_of_pos hB₀, ← Real.exp_add]
    congr 1
    dsimp [t]
    ring
  change B ^ p * (Real.exp (-p * s) * max (-signedInput β (t - s)) 0 -
    Real.exp (-p * s) * max (-phaseProfile Complex.re β (phaseOrbit t) (-s)) 0) = _
  rw [hphase, ← mul_sub, ← mul_assoc, hscale]
  rfl

private theorem omitted_phase_mass_bound {β a B : ℝ} (hβ : 1 / 2 < β)
    (ha : 0 < a) (hB : 0 < B) :
    let p := β - 1 / 2
    let h := phaseOrbit (Real.log B)
    let V := B ^ p *
      (phaseWindowInfinite Complex.re β h - phaseWindow Complex.re β (Real.log B - Real.log a) h)
    0 ≤ V ∧ V ≤ coeffMass / p * a ^ p := by
  dsimp only
  let p := β - 1 / 2
  let W := Real.log B - Real.log a
  let h := phaseOrbit (Real.log B)
  have htail := phaseWindowInfinite_sub_window hβ W h
  refine ⟨mul_nonneg (Real.rpow_nonneg hB.le _) htail.1, ?_⟩
  calc
    _ ≤ B ^ p * (coeffMass / p * Real.exp (-p * W)) :=
      mul_le_mul_of_nonneg_left htail.2 (Real.rpow_nonneg hB.le _)
    _ = _ := by
      rw [mul_left_comm, Real.rpow_def_of_pos hB, ← Real.exp_add, Real.rpow_def_of_pos ha]
      congr 2
      dsimp [W]
      ring

/-- With an attained maximal abscissa above one half and all strictly lower
zeros on or left of the critical line, the cumulative phase error is positive
and bounded above and below by positive multiples of the logarithm. -/
theorem prime_tail_cumulative_error_log_order (ρ : ℂ) (hρ : IsNontrivialZero ρ) :
    let realPart := Complex.re
    let β := realPart ρ
    1 / 2 < β →
    (∀ z : ℂ, IsNontrivialZero z → realPart z ≤ β) →
    (∀ z : ℂ, IsNontrivialZero z → realPart z < β → realPart z ≤ 1 / 2) →
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ B₀ : ℝ, ∀ B ≥ B₀,
      let error := (∫ x in (2 : ℝ)..B, max (-primeTail x) 0 / Real.sqrt x) -
        B ^ (β - 1 / 2) * phaseWindowInfinite realPart β (phaseOrbit (Real.log B))
      c * Real.log B ≤ error ∧ error ≤ C * Real.log B := by
  dsimp only
  intro hβ hmax hgap
  let β := ρ.re
  let p := β - 1 / 2
  let F (u : ℝ) := max (-profile β u) 0
  let D := correctionDensity β
  obtain ⟨K, hK, hbound⟩ := signed_error_bound (le_refl (1 / 2 : ℝ)) hmax hgap
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (Real.log 2)).and ((eventually_signed_margin hβ hmax hgap).and hbound))
  let U := max (Real.log 2) T
  have hU : Real.log 2 ≤ U := le_max_left _ _
  have hU₀ : 0 ≤ U := (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hU
  have hM : 0 ≤ coeffMass := tsum_nonneg (fun _ => norm_nonneg _)
  have hF (u : ℝ) : F u ≤ coeffMass := by
    simpa [phaseDensity, profile, F] using
      (phaseDensity_bound Complex.re β (phaseOrbit u) 0).2
  let η := 1 / (coeffMass + 1)
  have hη : 0 < η := by positivity
  have hpoint (u : ℝ) (hu : U ≤ u) : η * F u ≤ D u ∧ D u ≤ K := by
    obtain ⟨_, hsign, habs⟩ := hT u ((le_max_right _ _).trans hu)
    refine ⟨correction_minorant (Real.exp_pos _) zero_lt_one hM (hF u) hsign, ?_⟩
    exact (le_abs_self (D u)).trans ((correction_abs_le β u).trans (by simpa using habs))
  have hint (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable D volume a b :=
    ((correctionDensity_continuousOn β).mono (fun _ hx => ha.trans hx.1)
      ).intervalIntegrable_of_Icc hab
  obtain ⟨W, hW, m, hm, hwindow⟩ := wide_profile_mass ρ hρ hβ hmax
  have hwin (a : ℝ) (ha : U ≤ a) : η * m ≤ ∫ u in a..(a + W), D u := by
    have hab : a ≤ a + W := le_add_of_nonneg_right hW.le
    have hf := hwindow (a + W)
    rw [add_sub_cancel_right] at hf
    calc
      _ ≤ η * ∫ u in a..(a + W), F u := mul_le_mul_of_nonneg_left hf hη.le
      _ = ∫ u in a..(a + W), η * F u := (intervalIntegral.integral_const_mul _ _).symm
      _ ≤ _ := intervalIntegral.integral_mono_on hab
        (((profile_negative_continuous β).const_mul η).intervalIntegrable _ _)
        (hint _ _ (hU₀.trans ha) hab) (fun u hu => (hpoint u (ha.trans hu.1)).1)
  let c := η * m / W / 2
  let C := K + 1
  let H := ∫ u in Real.log 2..U, D u
  let J := coeffMass / p * (2 : ℝ) ^ p
  have hc : 0 < c := by positivity
  have hC : 0 < C := by positivity
  have hlate : ∀ᶠ B : ℝ in atTop,
      let error := (∫ x in (2 : ℝ)..B, max (-primeTail x) 0 / Real.sqrt x) -
        B ^ p * phaseWindowInfinite Complex.re β (phaseOrbit (Real.log B))
      c * Real.log B ≤ error ∧ error ≤ C * Real.log B := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop U,
      Real.tendsto_log_atTop.eventually_ge_atTop (H - K * U),
      Real.tendsto_log_atTop.eventually_ge_atTop ((2 * c * (U + W) + J - H) / c)]
      with B hB hlog hupper hlower
    let t := Real.log B
    let V := B ^ p * (phaseWindowInfinite Complex.re β (phaseOrbit t) -
      phaseWindow Complex.re β (t - Real.log 2) (phaseOrbit t))
    have hV : 0 ≤ V ∧ V ≤ J :=
      omitted_phase_mass_bound hβ (by norm_num) ((by norm_num : (0 : ℝ) < 2).trans_le hB)
    have hidentity := prime_mass_sub_phase_window (β := β) (a := 2) le_rfl hB
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hint _ _ (Real.log_nonneg (by norm_num)) hU) (hint _ _ hU₀ hlog)] at hidentity
    have herror :
        (∫ x in (2 : ℝ)..B, max (-primeTail x) 0 / Real.sqrt x) -
          B ^ p * phaseWindowInfinite Complex.re β (phaseOrbit t) =
          H + (∫ u in U..t, D u) - V := by
      dsimp only [V, H, D, t, p]
      rw [mul_sub]
      linarith only [hidentity]
    dsimp only
    rw [herror]
    have hi := integral_affine_lower_of_window hW (mul_pos hη hm)
      (fun a b ha hab => hint a b (hU₀.trans ha) hab)
      (fun u hu => (mul_nonneg hη.le (le_max_right _ _)).trans (hpoint u hu).1) hwin hlog
    have hj : (∫ u in U..t, D u) ≤ K * (t - U) := by
      rw [mul_comm, ← smul_eq_mul, ← intervalIntegral.integral_const]
      exact intervalIntegral.integral_mono_on hlog (hint _ _ hU₀ hlog) intervalIntegrable_const
        (fun u hu => (hpoint u hu.1).2)
    have haff : 2 * c * (t - U - W) ≤ ∫ u in U..t, D u := by
      dsimp only [c]
      linarith only [hi]
    change (2 * c * (U + W) + J - H) / c ≤ t at hlower
    have hthreshold := (div_le_iff₀ hc).1 hlower
    change H - K * U ≤ t at hupper
    change c * t ≤ H + (∫ u in U..t, D u) - V ∧
      H + (∫ u in U..t, D u) - V ≤ C * t
    constructor
    · linarith only [haff, hthreshold, hV.2]
    · dsimp only [C]
      linarith only [hj, hupper, hV.1]
  exact ⟨c, hc, C, hC, eventually_atTop.mp hlate⟩

private theorem correction_global_bound {β γ : ℝ} (hγ : 1 / 2 ≤ γ)
    (hmax : ∀ z : ℂ, IsNontrivialZero z → z.re ≤ β)
    (hbelow : ∀ z : ℂ, IsNontrivialZero z → z.re < β → z.re ≤ γ) :
    ∃ K > (0 : ℝ), ∀ u ≥ Real.log 2,
      |correctionDensity β u| ≤ K * Real.exp ((γ - 1 / 2) * u) := by
  obtain ⟨K, hK, hev⟩ := signed_error_bound hγ hmax hbelow
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  let U := max (Real.log 2) T
  let f (u : ℝ) := |correctionDensity β u| / Real.exp ((γ - 1 / 2) * u)
  have hU : Real.log 2 ≤ U := le_max_left _ _
  have hf : ContinuousOn f (Icc (Real.log 2) U) := by
    refine (((correctionDensity_continuousOn β).mono ?_).abs).div
      (by fun_prop) (fun _ _ => (Real.exp_pos _).ne')
    exact fun _ hu => (Real.log_nonneg (by norm_num)).trans hu.1
  obtain ⟨u₀, hu₀, hpeak⟩ := isCompact_Icc.exists_isMaxOn
    ⟨Real.log 2, le_rfl, hU⟩ hf
  refine ⟨max K (f u₀), hK.trans_le (le_max_left _ _), fun u hu => ?_⟩
  by_cases huU : U ≤ u
  · exact (correction_abs_le β u).trans ((hT u ((le_max_right _ _).trans huU)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)))
  · have h : f u ≤ max K (f u₀) :=
      (show f u ≤ f u₀ from hpeak ⟨hu, le_of_not_ge huU⟩).trans (le_max_right _ _)
    exact (div_le_iff₀ (Real.exp_pos _)).1 h

/-- The normalized phase approximation is uniform in the left endpoint.
A strictly supercritical lower spectral ceiling gives a difference of endpoint
powers. At the critical ceiling, the integrated root-scale error is proportional
to log width. -/
theorem prime_tail_window_error_of_lower_spectral_bound (β γ : ℝ) :
    let realPart := Complex.re
    1 / 2 ≤ γ → γ < β →
    (∀ z : ℂ, IsNontrivialZero z → realPart z ≤ β) →
    (∀ z : ℂ, IsNontrivialZero z → realPart z < β → realPart z ≤ γ) →
    ∃ K > (0 : ℝ), ∀ B : ℝ, ∀ a ∈ Icc 2 B,
      let p := β - 1 / 2
      let r := γ - 1 / 2
      let error := (∫ x in a..B, max (-primeTail x) 0 / Real.sqrt x) / B ^ p -
        phaseWindowInfinite realPart β (phaseOrbit (Real.log B))
      |error| ≤ K * ((a / B) ^ p +
        if γ = 1 / 2 then B ^ (-p) * Real.log (B / a) else (B ^ r - a ^ r) / B ^ p) := by
  dsimp only
  intro hγ hγβ hmax hbelow
  let p := β - 1 / 2
  let r := γ - 1 / 2
  have hβ : 1 / 2 < β := hγ.trans_lt hγβ
  have hp : 0 < p := sub_pos.mpr hβ
  obtain ⟨K, hK, hcorr⟩ := correction_global_bound hγ hmax hbelow
  let k := if γ = 1 / 2 then K else K / r
  have hk : 0 < k := by
    dsimp [k]
    split_ifs with heq
    · exact hK
    · exact div_pos hK (sub_pos.mpr (lt_of_le_of_ne hγ (Ne.symm heq)))
  refine ⟨max (coeffMass / p) k, hk.trans_le (le_max_right _ _), fun B a ha => ?_⟩
  have ha₀ : 0 < a := (by norm_num : (0 : ℝ) < 2).trans_le ha.1
  have hB₀ : 0 < B := ha₀.trans_le ha.2
  have hlog : Real.log a ≤ Real.log B := Real.log_le_log ha₀ ha.2
  have hloga : Real.log 2 ≤ Real.log a := Real.log_le_log (by norm_num) ha.1
  let t := Real.log B
  let v := Real.log a
  let h := phaseOrbit t
  let N := ∫ x in a..B, max (-primeTail x) 0 / Real.sqrt x
  let V := B ^ p * (phaseWindowInfinite Complex.re β h - phaseWindow Complex.re β (t - v) h)
  let R := if γ = 1 / 2 then B ^ (-p) * Real.log (B / a) else (B ^ r - a ^ r) / B ^ p
  have hBpow : 0 < B ^ p := Real.rpow_pos_of_pos hB₀ _
  have hV : 0 ≤ V ∧ V ≤ coeffMass / p * a ^ p := omitted_phase_mass_bound hβ ha₀ hB₀
  have hfund := prime_mass_sub_phase_window (β := β) ha.1 ha.2
  have hdiff : N - B ^ p * phaseWindowInfinite Complex.re β h =
      (∫ u in v..t, correctionDensity β u) - V := by
    dsimp only [N, V, h, t, v, p]
    rw [mul_sub]
    linarith only [hfund]
  have hci : ContinuousOn (correctionDensity β) (Icc v t) :=
    (correctionDensity_continuousOn β).mono
      (fun _ hu => (Real.log_nonneg (by norm_num)).trans (hloga.trans hu.1))
  have he : Continuous fun u : ℝ => Real.exp (r * u) := by fun_prop
  have hint :
      |∫ u in v..t, correctionDensity β u| ≤ K * (∫ u in v..t, Real.exp (r * u)) := by
    rw [← intervalIntegral.integral_const_mul]
    exact (intervalIntegral.abs_integral_le_integral_abs hlog).trans
      (intervalIntegral.integral_mono_on hlog (hci.abs.intervalIntegrable_of_Icc hlog)
        ((he.const_mul K).intervalIntegrable _ _)
        (fun u hu => hcorr u (hloga.trans hu.1)))
  have hrate : K * (∫ u in v..t, Real.exp (r * u)) / B ^ p ≤ k * R := by
    by_cases heq : γ = 1 / 2
    · have hz : r = 0 := sub_eq_zero.mpr heq
      simp only [hz, zero_mul, Real.exp_zero, intervalIntegral.integral_const, smul_eq_mul, mul_one]
      dsimp only [k, R]
      rw [ite_eq_left heq, ite_eq_left heq, Real.log_div hB₀.ne' ha₀.ne', Real.rpow_neg hB₀.le]
      dsimp only [t, v]
      exact le_of_eq (by ring)
    · have hr : 0 < r := sub_pos.mpr (lt_of_le_of_ne hγ (Ne.symm heq))
      have heqint : r * (∫ u in v..t, Real.exp (r * u)) =
          Real.exp (r * t) - Real.exp (r * v) := by
        rw [intervalIntegral.mul_integral_comp_mul_left (f := Real.exp), integral_exp]
      have hIntegral : (∫ u in v..t, Real.exp (r * u)) = (B ^ r - a ^ r) / r := by
        apply (eq_div_iff hr.ne').2
        rw [mul_comm, heqint, Real.rpow_def_of_pos hB₀, Real.rpow_def_of_pos ha₀,
          mul_comm (Real.log B) r, mul_comm (Real.log a) r]
      dsimp only [k, R]
      rw [ite_eq_right heq, ite_eq_right heq, hIntegral]
      exact le_of_eq (by ring)
  have hR : 0 ≤ R := by
    dsimp only [R]
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg hB₀.le _)
        (Real.log_nonneg ((le_div_iff₀ ha₀).2 (by simpa using ha.2)))
    · exact div_nonneg
        (sub_nonneg.mpr (Real.rpow_le_rpow ha₀.le ha.2 (sub_nonneg.mpr hγ))) hBpow.le
  change |N / B ^ p - phaseWindowInfinite Complex.re β h| ≤
    max (coeffMass / p) k * ((a / B) ^ p + R)
  have hnormalize : N / B ^ p - phaseWindowInfinite Complex.re β h =
      (N - B ^ p * phaseWindowInfinite Complex.re β h) / B ^ p := by
    rw [sub_div, mul_div_cancel_left₀ _ hBpow.ne']
  rw [hnormalize, hdiff]
  calc
    _ ≤ |∫ u in v..t, correctionDensity β u| / B ^ p + V / B ^ p := by
      rw [abs_div, abs_of_pos hBpow, ← add_div]
      apply div_le_div_of_nonneg_right _ hBpow.le
      have hn : |(∫ u in v..t, correctionDensity β u) - V| ≤
          |∫ u in v..t, correctionDensity β u| + |V| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (∫ u in v..t, correctionDensity β u) 0 V
      simpa only [abs_of_nonneg hV.1] using hn
    _ ≤ k * R + (coeffMass / p) * (a / B) ^ p := by
      apply add_le_add ((div_le_div_of_nonneg_right hint hBpow.le).trans hrate)
      rw [Real.div_rpow ha₀.le hB₀.le, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right hV.2 hBpow.le
    _ ≤ _ := by
      rw [mul_add, add_comm (k * R)]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (div_nonneg ha₀.le hB₀.le) p))
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hR)

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeGrowingWidthRate
