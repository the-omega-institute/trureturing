/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeCriticalResidual
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeCriticalResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A root-scale margin turns zero-mass windows into wider zero cluster values. -/

import D5.S3.Analytic.Laplace.MaximalRealPartProjection
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualZeroLaplace
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster
import D5.S3.Weil.Mertens.ZeroAbscissaPower

/-! The prime-power correction supplies a negative margin at the square-root scale. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q U)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZeroSum (IsNontrivialZero)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimeCriticalResidual

open MaximalRealPartProjection
  (maximalSeries summable_norm_maximalTerm uniformContinuous_maximalSeries)
open PrimeOnlyTailCorrection (primeTail prime_integrable prime_power_window_correction)
open PrimePhaseCluster (phaseOrbit phaseProfile phaseProfile_on_orbit phaseWindow
  prime_tail_mass_cluster_iff_of_upper_bound)
open ZeroAbscissaPower (actual_zero primitive_eq_negative_tail)

def rootTerm (t : ℝ) (k : ℕ) : ℂ :=
  actualCoeff k * Complex.exp ((t : ℂ) * (actualZero k - 1 / 2))

theorem norm_rootTerm (t : ℝ) (k : ℕ) :
    ‖rootTerm t k‖ = ‖actualCoeff k‖ * Real.exp (((actualZero k).re - 1 / 2) * t) := by
  have hre : ((1 / 2 : ℂ)).re = (1 / 2 : ℝ) := by norm_num
  rw [rootTerm, norm_mul, Complex.norm_exp, Complex.re_ofReal_mul, Complex.sub_re, hre, mul_comm t]

theorem summable_norm_rootTerm (t : ℝ) : Summable (fun k => ‖rootTerm t k‖) := by
  refine (actualCoeff_hasSum.summable.norm.mul_right (Real.exp (|t| / 2))).of_norm_bounded ?_
  intro k
  rw [norm_norm, norm_rootTerm]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  obtain ⟨hpos, hlt⟩ := (actual_zero k).2
  have hcentered : |(actualZero k).re - 1 / 2| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    _ ≤ |((actualZero k).re - 1 / 2) * t| := le_abs_self _
    _ = |(actualZero k).re - 1 / 2| * |t| := abs_mul _ _
    _ ≤ 1 / 2 * |t| := mul_le_mul_of_nonneg_right hcentered (abs_nonneg _)
    _ = |t| / 2 := by ring

theorem scaled_shift_eq_rootTerm (β t : ℝ) (k : ℕ) :
    (Real.exp ((β - 1 / 2) * t) : ℂ) *
      (actualCoeff k * Complex.exp ((t : ℂ) * (actualZero k - (β : ℂ)))) = rootTerm t k := by
  rw [rootTerm, Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private def strictLeft : Set ℕ := {k | (actualZero k).re < 1 / 2}

private def halfLine : Set ℕ := {k | (actualZero k).re = 1 / 2}

private def strictLeftMass (t : ℝ) : ℝ := ∑' k : strictLeft, ‖rootTerm t k‖

private theorem strictLeftMass_tendsto_zero : Tendsto strictLeftMass atTop (𝓝 0) := by
  have hterm (k : strictLeft) : Tendsto (fun t : ℝ => ‖rootTerm t k.1‖) atTop (𝓝 0) := by
    have hneg : (actualZero k.1).re - 1 / 2 < 0 := sub_neg.mpr k.2
    have harg := tendsto_id.const_mul_atTop_of_neg hneg
    simpa only [norm_rootTerm, Function.comp_def, id_eq, mul_zero] using
      (Real.tendsto_exp_atBot.comp harg).const_mul ‖actualCoeff k.1‖
  have hdom : ∀ᶠ t : ℝ in atTop, ∀ k : strictLeft, ‖‖rootTerm t k.1‖‖ ≤ ‖actualCoeff k.1‖ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht k
    rw [norm_norm, norm_rootTerm]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr k.2.le) ht))
  have hsum := tendsto_tsum_of_dominated_convergence
    (actualCoeff_hasSum.summable.norm.subtype strictLeft) hterm hdom
  rw [tsum_zero] at hsum
  exact hsum

private theorem halfLine_mass_le (t : ℝ) :
    (∑' k : halfLine, ‖rootTerm t k.1‖) ≤ firstLiMass := by
  have hpos (k : ℕ) : 0 < (actualCoeff k).re := by
    obtain ⟨h0, h1⟩ := (actual_zero k).2
    exact (heightRefinement_pairWeight_strip h0 h1).1
  have hmass : HasSum (fun k => (actualCoeff k).re) firstLiMass := by
    simpa only [Complex.ofReal_re] using Complex.hasSum_re actualCoeff_hasSum
  calc
    _ = ∑' k : halfLine, (actualCoeff k.1).re := by
      refine tsum_congr fun k => ?_
      have hline : (actualZero k.1).re = 1 / 2 := k.2
      have him : (actualCoeff k.1).im = 0 := by
        simp only [actualCoeff, one_div, Complex.inv_im, Complex.mul_im,
          Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hline]
        ring_nf
      rw [norm_rootTerm, hline, sub_self, zero_mul, Real.exp_zero, mul_one,
        ← Complex.abs_re_eq_norm.mpr him, abs_of_pos (hpos k.1)]
    _ ≤ ∑' k : ℕ, (actualCoeff k).re :=
      hmass.summable.tsum_subtype_le _ halfLine (fun k => (hpos k).le)
    _ = firstLiMass := hmass.tsum_eq

private theorem root_zero_sum_bound {t β : ℝ} (hβ : 1 / 2 < β)
    (hmax : ∀ k : ℕ, (actualZero k).re ≤ β) :
    -((Real.exp (-t / 2) : ℂ) * actualH t).re ≤
      Real.exp ((β - 1 / 2) * t) * (-(maximalSeries actualCoeff actualZero β t).re) +
        (∑' k : {k : ℕ // 1 / 2 < (actualZero k).re ∧ (actualZero k).re < β},
          ‖actualCoeff k.1‖ * Real.exp (((actualZero k.1).re - 1 / 2) * t)) +
        (firstLiMass + strictLeftMass t) := by
  classical
  let lower : Set ℕ := {k | (actualZero k).re ≤ 1 / 2}
  let intermediate : Set ℕ := {k | 1 / 2 < (actualZero k).re ∧ (actualZero k).re < β}
  let scale := Real.exp ((β - 1 / 2) * t)
  have hline := (summable_norm_maximalTerm (z := actualZero) (Θ := β)
    actualCoeff_hasSum.summable.norm t).of_norm
  have hroot := (summable_norm_rootTerm t).of_norm
  have hscaled : (Real.exp (-t / 2) : ℂ) * actualH t = ∑' k, rootTerm t k := by
    rw [actualH, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    have hzero : (0 - 1 / 2 : ℝ) * t = -t / 2 := by ring
    simpa only [hzero, Complex.ofReal_zero, sub_zero] using scaled_shift_eq_rootTerm 0 t k
  have hsplit : (∑' k, rootTerm t k) =
      (scale : ℂ) * maximalSeries actualCoeff actualZero β t +
        (∑' k : lower, rootTerm t k) + (∑' k : intermediate, rootTerm t k) := by
    rw [maximalSeries, ← tsum_mul_left, tsum_subtype, tsum_subtype,
      ← (hline.mul_left _).tsum_add (hroot.indicator lower),
      ← ((hline.mul_left _).add (hroot.indicator lower)).tsum_add (hroot.indicator intermediate)]
    refine tsum_congr fun k => ?_
    change rootTerm t k = (scale : ℂ) * (if (actualZero k).re = β then
      actualCoeff k * Complex.exp ((t : ℂ) * (actualZero k - (β : ℂ))) else 0) +
      lower.indicator (rootTerm t) k + intermediate.indicator (rootTerm t) k
    by_cases heq : (actualZero k).re = β
    · have hlo : k ∉ lower := fun hk => (not_le.mpr hβ) (heq ▸ hk)
      have hmid : k ∉ intermediate := fun hk => (lt_irrefl β) (heq ▸ hk.2)
      rw [indicator_of_notMem hlo, indicator_of_notMem hmid, add_zero, add_zero]
      simpa only [ite_eq_left heq] using (scaled_shift_eq_rootTerm β t k).symm
    · by_cases hlo : (actualZero k).re ≤ 1 / 2
      · have hmid : k ∉ intermediate := fun hk => (not_lt.mpr hlo) hk.1
        rw [indicator_of_mem (show k ∈ lower from hlo), indicator_of_notMem hmid]
        simp only [ite_eq_right heq, mul_zero, zero_add, add_zero]
      · have hmid : k ∈ intermediate := ⟨lt_of_not_ge hlo, lt_of_le_of_ne (hmax k) heq⟩
        rw [indicator_of_notMem (show k ∉ lower from hlo), indicator_of_mem hmid]
        simp only [ite_eq_right heq, mul_zero, zero_add]
  have hlower : halfLine ∪ strictLeft = lower := by
    ext k
    change (actualZero k).re = 1 / 2 ∨ (actualZero k).re < 1 / 2 ↔
      (actualZero k).re ≤ 1 / 2
    exact or_comm.trans le_iff_lt_or_eq.symm
  have hdisjoint : Disjoint halfLine strictLeft :=
    Set.disjoint_left.mpr fun _ heq hlt => (ne_of_lt hlt) heq
  have hlow : -(∑' k : lower, rootTerm t k).re ≤ firstLiMass + strictLeftMass t := by
    refine (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans ?_)
    calc
      _ ≤ ∑' k : lower, ‖rootTerm t k.1‖ :=
        norm_tsum_le_tsum_norm ((summable_norm_rootTerm t).subtype lower)
      _ = (∑' k : halfLine, ‖rootTerm t k.1‖) + strictLeftMass t := by
        rw [← hlower, strictLeftMass]
        exact Summable.tsum_union_disjoint hdisjoint
          ((summable_norm_rootTerm t).subtype halfLine) ((summable_norm_rootTerm t).subtype strictLeft)
      _ ≤ _ := add_le_add (halfLine_mass_le t) le_rfl
  have hmid : -(∑' k : intermediate, rootTerm t k).re ≤
      ∑' k : intermediate, ‖actualCoeff k.1‖ * Real.exp (((actualZero k.1).re - 1 / 2) * t) := by
    refine (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans ?_)
    calc
      _ ≤ ∑' k : intermediate, ‖rootTerm t k‖ :=
        norm_tsum_le_tsum_norm ((summable_norm_rootTerm t).subtype intermediate)
      _ = _ := tsum_congr fun k => norm_rootTerm t k
  rw [hscaled, hsplit, Complex.add_re, Complex.add_re, Complex.re_ofReal_mul]
  change _ ≤ scale * _ + (∑' k : intermediate, _) + _
  linarith only [hlow, hmid]

private theorem complete_tail_root_bound {t : ℝ} (ht : Real.log 2 ≤ t) :
    Real.exp (t / 2) * Q (Real.exp t) ≤ -((Real.exp (-t / 2) : ℂ) * actualH t).re := by
  have htpos : 0 < t := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le ht
  have hx : 2 ≤ Real.exp t := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr ht
  have hQ := (div_eq_iff (Real.exp_pos t).ne').mp (primitive_eq_negative_tail hx)
  have hQ' : Q (Real.exp t) * Real.exp t = -U (Real.exp t) := by linarith only [hQ]
  have hformula := congrArg Complex.re (actual_integrated_explicit_formula htpos)
  simp only [Complex.ofReal_re] at hformula
  have hlog : 1 ≤ Real.log (2 * Real.pi) := by
    refine (show 1 ≤ Real.log 3 by linarith [Real.log_three_gt_d9]).trans ?_
    exact Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_three])
  have htriv := trivialT_le_mass htpos.le
  have hlog2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have hscale : Real.exp (t / 2) = Real.exp (-t / 2) * Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hscale, mul_assoc, mul_comm (Real.exp t), hQ', Complex.re_ofReal_mul, ← mul_neg]
  exact mul_le_mul_of_nonneg_left (by linarith only [hformula, htriv, hlog, hlog2])
    (Real.exp_nonneg _)

/-- The intermediate zero mass converges absolutely, with each analytic occurrence counted.
For each positive margin below `2 - firstLiMass`, one late threshold works
for every upper bound `β > 1/2` on the real parts of the nontrivial zeros. -/
theorem eventually_prime_tail_root_scale :
    let lineRealPart := Complex.re
    (∀ β t : ℝ, Summable
      (fun k : {k : ℕ // 1 / 2 < (actualZero k).re ∧ (actualZero k).re < β} =>
        ‖actualCoeff k.1‖ * Real.exp (((actualZero k.1).re - 1 / 2) * t))) ∧
    ∀ d : ℝ, 0 < d → d < 2 - firstLiMass →
      ∀ᶠ t : ℝ in atTop, ∀ β : ℝ, 1 / 2 < β →
        (∀ z : ℂ, IsNontrivialZero z → z.re ≤ β) →
        Real.exp (t / 2) * primeTail (Real.exp t) ≤
          Real.exp ((β - 1 / 2) * t) * (-lineRealPart (maximalSeries actualCoeff actualZero β t)) +
            (∑' k : {k : ℕ // 1 / 2 < (actualZero k).re ∧ (actualZero k).re < β},
              ‖actualCoeff k.1‖ * Real.exp (((actualZero k.1).re - 1 / 2) * t)) - d := by
  dsimp only
  refine ⟨fun β t => ?_, ?_⟩
  · exact ((summable_norm_rootTerm t).subtype
      {k : ℕ | 1 / 2 < (actualZero k).re ∧ (actualZero k).re < β}).congr
      (fun k => norm_rootTerm t k.val)
  · intro d _ hd
    have hpower := prime_power_window_correction.1.comp Real.tendsto_exp_atTop
    have hbudget : Tendsto
        (fun t : ℝ => Real.sqrt (Real.exp t) * (Q (Real.exp t) - primeTail (Real.exp t)) -
          strictLeftMass t) atTop (𝓝 2) := by
      simpa only [Function.comp_def, sub_zero] using hpower.sub strictLeftMass_tendsto_zero
    have hgap := hbudget.eventually_const_lt (show d + firstLiMass < 2 by linarith only [hd])
    filter_upwards [eventually_ge_atTop (Real.log 2), hgap] with t ht hgap β hβ hmax
    have hsqrt : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
      congr 1
      ring
    rw [hsqrt, mul_sub] at hgap
    have hcomplete := complete_tail_root_bound ht
    have hzeros := root_zero_sum_bound (t := t) hβ (fun k => hmax _ (actual_zero k))
    linarith only [hgap, hcomplete, hzeros]

private theorem continuousOn_prime_mass_density :
    ContinuousOn (fun x : ℝ => max (-primeTail x) 0 / Real.sqrt x) (Ici 1) :=
  (prime_integrable.continuousOn_Ici_primitive_Ioi.neg.sup continuousOn_const).div
    Real.continuous_sqrt.continuousOn
    (fun _ hx => (Real.sqrt_pos.mpr (zero_lt_one.trans_le (mem_Ici.mp hx))).ne')

/-- A late window with zero prime-tail mass and intermediate zero sum below `d`
throughout gives a zero cluster value at a strictly wider width. For each admissible
margin `d`, one left endpoint threshold works for every real-part upper bound and width. -/
theorem prime_tail_mass_pos_or_intermediate_or_wider_zero_cluster :
    let scale := Real.exp
    ∀ d : ℝ, 0 < d → d < 2 - firstLiMass →
      ∃ T : ℝ, ∀ β : ℝ, 1 / 2 < β → (∀ z : ℂ, IsNontrivialZero z → z.re ≤ β) →
        ∀ t W : ℝ, 0 < W → T ≤ t - W →
          0 < (∫ x in scale (t - W)..scale t, max (-primeTail x) 0 / Real.sqrt x) ∨
          (∃ u ∈ Icc (t - W) t, d ≤
            ∑' k : {k : ℕ // 1 / 2 < (actualZero k).re ∧ (actualZero k).re < β},
              ‖actualCoeff k.1‖ * scale (((actualZero k.1).re - 1 / 2) * u)) ∨
          ∃ W' > W, MapClusterPt 0 atTop (fun B : ℝ =>
            (∫ x in scale (Real.log B - W')..B, max (-primeTail x) 0 / Real.sqrt x) /
              scale (Real.log B * (β - 1 / 2))) := by
  dsimp only
  intro d hdpos hd
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_prime_tail_root_scale.2 d hdpos hd)
  refine ⟨max T 0, ?_⟩
  intro β hβ hmax t W hW hlate
  by_cases hmass : 0 < (∫ x in Real.exp (t - W)..Real.exp t, max (-primeTail x) 0 / Real.sqrt x)
  · exact Or.inl hmass
  right
  by_cases hinter : ∃ u ∈ Icc (t - W) t, d ≤
      ∑' k : {k : ℕ // 1 / 2 < (actualZero k).re ∧ (actualZero k).re < β},
        ‖actualCoeff k.1‖ * Real.exp (((actualZero k.1).re - 1 / 2) * u)
  · exact Or.inl hinter
  right
  have hends : Real.exp (t - W) < Real.exp t := Real.exp_lt_exp.mpr (sub_lt_self t hW)
  have hleft : 1 ≤ Real.exp (t - W) :=
    Real.one_le_exp ((le_max_right T 0).trans hlate)
  have htail (u : ℝ) (hu : u ∈ Icc (t - W) t) : 0 ≤ primeTail (Real.exp u) := by
    by_contra! hneg
    apply hmass
    have hx : Real.exp u ∈ Icc (Real.exp (t - W)) (Real.exp t) :=
      ⟨Real.exp_le_exp.mpr hu.1, Real.exp_le_exp.mpr hu.2⟩
    exact intervalIntegral.integral_pos hends
      (continuousOn_prime_mass_density.mono (fun _ hy => hleft.trans hy.1))
      (fun _ _ => div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _))
      ⟨Real.exp u, hx, div_pos ((neg_pos.mpr hneg).trans_le (le_max_left _ _))
        (Real.sqrt_pos.mpr (Real.exp_pos u))⟩
  let profile (u : ℝ) := -(maximalSeries actualCoeff actualZero β u).re
  have hpositive (u : ℝ) (hu : u ∈ Icc (t - W) t) : 0 < profile u := by
    have hroot := hT u (((le_max_left T 0).trans hlate).trans hu.1) β hβ hmax
    change _ ≤ Real.exp ((β - 1 / 2) * u) * profile u + _ - d at hroot
    have hsum := lt_of_not_ge (fun h => hinter ⟨u, hu, h⟩)
    have hscaled : 0 < Real.exp ((β - 1 / 2) * u) * profile u := by
      linarith only [hroot, hsum, mul_nonneg (Real.exp_nonneg (u / 2)) (htail u hu)]
    exact pos_of_mul_pos_right hscaled (Real.exp_nonneg _)
  have hcontinuous : Continuous profile := by
    unfold profile
    exact (Complex.continuous_re.comp
      (uniformContinuous_maximalSeries (z := actualZero) (Θ := β)
        actualCoeff_hasSum.summable.norm).continuous).neg
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
    (hcontinuous.continuousAt.eventually
      (lt_mem_nhds (hpositive (t - W) ⟨le_rfl, sub_le_self t hW.le⟩)))
  let W' := W + δ / 2
  have hww' : W < W' := lt_add_of_pos_right W (half_pos hδ)
  have hW' : 0 ≤ W' := (hW.trans hww').le
  have hphase : phaseWindow Complex.re β W' (phaseOrbit t) = 0 := by
    unfold phaseWindow
    trans (∫ _ in (0 : ℝ)..W', (0 : ℝ))
    · apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hW'] at hs
      have hspos : 0 < profile (t - s) := by
        by_cases hsW : s ≤ W
        · exact hpositive _ ⟨sub_le_sub_left hsW _, sub_le_self _ hs.1⟩
        · apply hball
          rw [Real.dist_eq, abs_lt]
          constructor <;> dsimp [W'] at hs <;> linarith only [hs.2, lt_of_not_ge hsW, hδ]
      change Real.exp _ * max (-phaseProfile Complex.re β (phaseOrbit t) (-s)) 0 = 0
      rw [phaseProfile_on_orbit, ← sub_eq_add_neg]
      change Real.exp _ * max (-profile (t - s)) 0 = 0
      rw [max_eq_right (neg_nonpos.mpr hspos.le), mul_zero]
    · simp
  have hcluster := (prime_tail_mass_cluster_iff_of_upper_bound β hβ hmax W' hW' 0).2
    ⟨phaseOrbit t, subset_closure (mem_range_self t), hphase.symm⟩
  refine ⟨W', hww', hcluster.congrFun ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
  simp only [sub_eq_add_neg, Real.exp_add, Real.exp_log hB, Real.rpow_def_of_pos hB]

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeCriticalResidual
