/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeCriticalTwoLines
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeCriticalTwoLines
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint two-line contacts give late negative prime-tail points. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster

/-! Separate the two actual lines before rescaling the remaining prime tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimeCriticalTwoLines

open ActualFilteredExplicitFormula (averagedActualCorrection averagedActualCorrection_bounds)
open MaximalRealPartProjection
open PrimeAttainedShortWindows (dirac_zero_support unaveraged_formula normalized_prime_power_error)
open PrimeOnlyTailCorrection (primeTail prime_integrable)
open PrimePhaseCluster

/-- After subtracting the full upper line, the prime tail at the subleading scale
is approximated by its actual subleading-line profile. -/
theorem prime_tail_two_line_approx (β γ : ℝ) :
    let profile := phaseProfile Complex.re
    1 / 2 < γ → γ < β →
    (∀ z : ℂ, IsNontrivialZero z → z.re ≤ β) →
    (∀ z : ℂ, IsNontrivialZero z → z.re < β → z.re ≤ γ) →
    Tendsto (fun t : ℝ => Real.exp ((1 - γ) * t) * primeTail (Real.exp t) -
      Real.exp ((β - γ) * t) * profile β (phaseOrbit t) 0 - profile γ (phaseOrbit t) 0)
      atTop (𝓝 0) := by
  dsimp only
  intro hγ hγβ hmax hcut
  have hγ₀ : 0 < γ := by linarith only [hγ]
  have hzero (k : ℕ) := actualData.zero_isNontrivial (actualOccurrenceEquiv k).1
  -- A discarded occurrence contributes zero and its replacement coordinate obeys the new bound.
  let a (k : ℕ) := if (actualZero k).re = β then 0 else actualCoeff k
  let z (k : ℕ) := if (actualZero k).re = β then 0 else actualZero k
  have hnorm (k : ℕ) : ‖a k‖ ≤ ‖actualCoeff k‖ := by
    unfold a
    split_ifs <;> simp
  have ha := actualCoeff_hasSum.summable.norm.of_nonneg_of_le
    (fun k : ℕ => norm_nonneg (a k)) hnorm
  have hz (k : ℕ) : (z k).re ≤ γ := by
    unfold z
    split_ifs with hk
    · simpa using hγ₀.le
    · exact hcut _ (hzero k) (lt_of_le_of_ne (hmax _ (hzero k)) hk)
  have hgamma (t : ℝ) : maximalSeries a z γ t = maximalSeries actualCoeff actualZero γ t := by
    unfold maximalSeries
    apply tsum_congr
    intro k
    change (if (z k).re = γ then a k * Complex.exp ((t : ℂ) * (z k - γ)) else 0) =
      if (actualZero k).re = γ then
        actualCoeff k * Complex.exp ((t : ℂ) * (actualZero k - γ)) else 0
    by_cases hk : (actualZero k).re = β
    · simp [a, z, hk, ne_of_gt hγβ]
    · simp [a, z, hk]
  have hsplit (t : ℝ) :
      actualH t = (Real.exp (β * t) : ℂ) * maximalSeries actualCoeff actualZero β t +
        ∑' k, a k * Complex.exp ((t : ℂ) * z k) := by
    have htop := (summable_norm_maximalTerm (z := actualZero) (Θ := β)
      actualCoeff_hasSum.summable.norm t).of_norm.mul_left (Real.exp (β * t) : ℂ)
    have hrest : Summable (fun k => a k * Complex.exp ((t : ℂ) * z k)) := by
      apply (actualH_summable t).norm.of_norm_bounded
      intro k
      by_cases hk : (actualZero k).re = β <;> simp [a, z, hk]
    unfold actualH maximalSeries
    rw [← tsum_mul_left, ← htop.tsum_add hrest]
    apply tsum_congr
    intro k
    change _ = (Real.exp (β * t) : ℂ) *
        (if (actualZero k).re = β then
          actualCoeff k * Complex.exp ((t : ℂ) * (actualZero k - β)) else 0) +
        a k * Complex.exp ((t : ℂ) * z k)
    by_cases hk : (actualZero k).re = β
    · simp only [a, hk, ite_eq_left, zero_mul, add_zero, Complex.ofReal_exp]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    · simp [a, z, hk]
  have hproj := (Complex.continuous_re.tendsto 0).comp
    (tendsto_exp_mul_tsum_sub_maximalSeries ha hz)
  have hreal : Tendsto (fun t : ℝ =>
      -((Real.exp (-γ * t) : ℂ) * (∑' k, a k * Complex.exp ((t : ℂ) * z k)) -
        maximalSeries actualCoeff actualZero γ t).re) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.zero_re, neg_zero, hgamma] using hproj.neg
  let corr := averagedActualCorrection (Measure.dirac (0 : ℝ))
  have hscale (t : ℝ) : Real.exp ((1 - γ) * t) * Real.exp (-t) = Real.exp (-γ * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcorr : Tendsto (fun t : ℝ => Real.exp ((1 - γ) * t) * corr t) atTop (𝓝 0) := by
    have hdecay := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hγ₀))
    have hbound : Tendsto (fun t : ℝ => Real.log (2 * Real.pi) * Real.exp (-γ * t))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, id_eq, mul_zero] using
        hdecay.const_mul (Real.log (2 * Real.pi))
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    obtain ⟨hlower, hupper⟩ :=
      averagedActualCorrection_bounds (Measure.dirac 0) dirac_zero_support ht
    rw [Real.norm_eq_abs, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) hupper)]
    calc
      _ ≤ -(Real.exp ((1 - γ) * t) * -(Real.log (2 * Real.pi) * Real.exp (-t))) :=
        neg_le_neg (mul_le_mul_of_nonneg_left hlower (Real.exp_nonneg _))
      _ = _ := by rw [← hscale t]; ring
  have h := (hreal.add hcorr).sub (normalized_prime_power_error hγ)
  rw [add_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (Real.log 2)] with t ht
  rw [unaveraged_formula ht, phaseProfile_on_orbit, phaseProfile_on_orbit, add_zero, hsplit t]
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, corr]
  have hfactor : Real.exp (-γ * t) * Real.exp (β * t) = Real.exp ((β - γ) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  linear_combination
    ((maximalSeries actualCoeff actualZero β t).re) * hfactor +
    ((Real.exp (β * t) * (maximalSeries actualCoeff actualZero β t).re +
      (∑' k, a k * Complex.exp ((t : ℂ) * z k)).re)) * hscale t

private theorem exists_nonpos_on_window_of_cutoff {β W : ℝ}
    (hW : 0 < W) (hβ : 1 / 2 < β)
    (hmax : ∀ z : ℂ, IsNontrivialZero z → z.re ≤ β)
    (hcutoff : ∀ V > W, Filter.liminf (fun B : ℝ =>
      (∫ x in B * Real.exp (-V)..B, max (-primeTail x) 0 / Real.sqrt x) /
        B ^ (β - 1 / 2)) atTop ≠ 0)
    {h : ℕ → Circle} (hh : h ∈ closure (range phaseOrbit)) :
    ∃ s ∈ Icc (0 : ℝ) W, phaseProfile Complex.re β h (-s) ≤ 0 := by
  by_contra! hpos
  let f (s : ℝ) := phaseProfile Complex.re β h (-s)
  have hf : Continuous f :=
    (phaseProfile_continuous Complex.re β).comp (continuous_const.prodMk continuous_neg)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_lt continuous_const hf) W
    (hpos W ⟨hW.le, le_rfl⟩)
  let V := W + ε / 2
  have hWV : W < V := lt_add_of_pos_right _ (half_pos hε)
  have hV : 0 < V := hW.trans hWV
  have hwide (s : ℝ) (hs : s ∈ Icc (0 : ℝ) V) : 0 < f s := by
    by_cases hsW : s ≤ W
    · exact hpos s ⟨hs.1, hsW⟩
    · apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hsW))]
      dsimp [V] at hs
      linarith only [hs.2, hε]
  have hwindow : phaseWindow Complex.re β V h = 0 := by
    unfold phaseWindow
    calc
      _ = ∫ s in 0..V, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hV.le] at hs
        change Real.exp (-(β - 1 / 2) * s) * max (-f s) 0 = 0
        rw [max_eq_right (neg_nonpos.mpr (hwide s hs).le), mul_zero]
      _ = 0 := intervalIntegral.integral_zero
  let mass (B : ℝ) :=
    (∫ x in B * Real.exp (-V)..B, max (-primeTail x) 0 / Real.sqrt x) / B ^ (β - 1 / 2)
  have hcluster : MapClusterPt 0 atTop mass :=
    (prime_tail_mass_cluster_iff_of_upper_bound β hβ hmax V hV.le 0).mpr
      ⟨h, hh, hwindow.symm⟩
  have hnonneg : ∀ᶠ B in atTop, 0 ≤ mass B := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    have hAB : B * Real.exp (-V) ≤ B :=
      mul_le_of_le_one_right hB (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hV.le))
    exact div_nonneg (intervalIntegral.integral_nonneg_of_forall hAB
      (fun x => div_nonneg (le_max_right _ _) (Real.sqrt_nonneg x)))
      (Real.rpow_nonneg hB _)
  have hlower := isBoundedUnder_of_eventually_ge hnonneg
  have hfreq := hcluster.frequently (Iio_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one))
  have hcb : (atTop : Filter ℝ).IsCoboundedUnder (· ≥ ·) mass := by
    refine ⟨1, fun b hb => ?_⟩
    have hb' : ∀ᶠ B in atTop, b ≤ mass B := hb
    obtain ⟨B, hB, hBb⟩ := (hfreq.and_eventually hb').exists
    exact hBb.trans hB.le
  exact hcutoff V hWV ((hcluster.liminf_le hlower).antisymm (le_liminf_of_le hcb hnonneg))

/-- The continuous minimum of the two profiles is uniformly negative on the
compact graph of first-profile minimizers. -/
private theorem uniform_contact_gap {X : Type*} [TopologicalSpace X]
    {H : Set X} {L : Set ℝ} (hH : IsCompact H) (hHne : H.Nonempty)
    (hL : IsCompact L) (hLne : L.Nonempty)
    {f g : X × ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hnonpos : ∀ h ∈ H, ∃ s ∈ L, f (h, s) ≤ 0)
    (hsign : ∀ h ∈ H, ∀ s ∈ L, f (h, s) = 0 →
      (∀ v ∈ L, 0 ≤ f (h, v)) → g (h, s) < 0) :
    ∃ d > 0, ∃ C : ℝ, ∀ h ∈ H, ∃ s ∈ L,
      f (h, s) ≤ 0 ∧ g (h, s) ≤ C ∧ (f (h, s) ≤ -d ∨ g (h, s) ≤ -d) := by
  let G : Set (X × ℝ) := H ×ˢ L ∩ ⋂ v : L, {p | f p ≤ f (p.1, v)}
  have hG : IsCompact G :=
    (hH.prod hL).inter_right (isClosed_iInter fun v =>
      isClosed_le hf (hf.comp (continuous_fst.prodMk continuous_const)))
  have hfiber (h : X) (hh : h ∈ H) : ∃ s : ℝ, (h, s) ∈ G := by
    obtain ⟨s, hs, hmin⟩ := hL.exists_isMinOn hLne
      (hf.comp (continuous_const.prodMk continuous_id)).continuousOn
    exact ⟨s, ⟨hh, hs⟩, mem_iInter.mpr fun v => hmin v.2⟩
  obtain ⟨h, hh⟩ := hHne
  obtain ⟨s, hs⟩ := hfiber h hh
  have hGne : G.Nonempty := ⟨(h, s), hs⟩
  have hf₀ (p : X × ℝ) (hp : p ∈ G) : f p ≤ 0 := by
    obtain ⟨v, hv, hfv⟩ := hnonpos p.1 hp.1.1
    exact (mem_iInter.mp hp.2 ⟨v, hv⟩).trans hfv
  have hneg (p : X × ℝ) (hp : p ∈ G) : min (f p) (g p) < 0 := by
    rcases (hf₀ p hp).lt_or_eq with hlt | heq
    · exact (min_le_left _ _).trans_lt hlt
    · have hγ := hsign p.1 hp.1.1 p.2 hp.1.2 heq fun v hv =>
        heq ▸ (mem_iInter.mp hp.2 ⟨v, hv⟩ : f p ≤ f (p.1, v))
      exact (min_le_right _ _).trans_lt hγ
  obtain ⟨p, hp, hbest⟩ := hG.exists_isMaxOn hGne (hf.min hg).continuousOn
  obtain ⟨q, _, hbound⟩ := hG.exists_isMaxOn hGne hg.continuousOn
  refine ⟨-min (f p) (g p), neg_pos.mpr (hneg p hp), g q, fun h hh => ?_⟩
  obtain ⟨s, hs⟩ := hfiber h hh
  have hle : min (f (h, s)) (g (h, s)) ≤ min (f p) (g p) := hbest hs
  exact ⟨s, hs.1.2, hf₀ _ hs, hbound hs, min_le_iff.mp (by rwa [neg_neg])⟩

/-- A strict joint contact sign gives a uniform negative point and positive
negative-part mass in each late window. The first profile must attain a
nonpositive value in every phase window, as it does at the critical cutoff. -/
theorem prime_tail_negative_windows_of_two_line_contact (β γ W : ℝ) :
    let profile := phaseProfile Complex.re
    0 < W → 1 / 2 < γ → γ < β →
    (∀ z : ℂ, IsNontrivialZero z → z.re ≤ β) →
    (∀ z : ℂ, IsNontrivialZero z → z.re < β → z.re ≤ γ) →
    ((∀ h ∈ closure (range phaseOrbit), ∃ s ∈ Icc (0 : ℝ) W, profile β h (-s) ≤ 0) ∨
      (∀ V > W, Filter.liminf (fun B : ℝ =>
        (∫ x in B * Real.exp (-V)..B, max (-primeTail x) 0 / Real.sqrt x) /
          B ^ (β - 1 / 2)) atTop ≠ 0)) →
    (∀ h ∈ closure (range phaseOrbit), ∀ s ∈ Icc (0 : ℝ) W,
      profile β h (-s) = 0 →
      (∀ v ∈ Icc (0 : ℝ) W, 0 ≤ profile β h (-v)) →
      profile γ h (-s) < 0) →
    ∃ c > 0, ∃ T : ℝ, ∀ t ≥ T,
      (∃ u ∈ Icc (t - W) t, Real.exp ((1 - γ) * u) * primeTail (Real.exp u) ≤ -c) ∧
      0 < ∫ x in Real.exp t * Real.exp (-W)..Real.exp t, max (-primeTail x) 0 / Real.sqrt x := by
  dsimp only
  intro hW hγ hγβ hmax hcut hwidth hcontact
  have hH (t : ℝ) : phaseOrbit t ∈ closure (range phaseOrbit) :=
    subset_closure (mem_range_self t)
  have hnonpos : ∀ h ∈ closure (range phaseOrbit), ∃ s ∈ Icc (0 : ℝ) W,
      phaseProfile Complex.re β h (-s) ≤ 0 :=
    hwidth.elim id fun hcutoff _ hh =>
      exists_nonpos_on_window_of_cutoff hW (hγ.trans hγβ) hmax hcutoff hh
  have hcont (α : ℝ) : Continuous (fun p : (ℕ → Circle) × ℝ =>
      phaseProfile Complex.re α p.1 (-p.2)) :=
    (phaseProfile_continuous Complex.re α).comp (continuous_fst.prodMk continuous_snd.neg)
  obtain ⟨d, hd, C, hgap⟩ := uniform_contact_gap isClosed_closure.isCompact ⟨_, hH 0⟩
    isCompact_Icc ⟨0, le_rfl, hW.le⟩ (hcont β) (hcont γ) hnonpos hcontact
  have happrox := prime_tail_two_line_approx β γ hγ hγβ hmax hcut
  obtain ⟨E, hE⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp happrox (d / 2) (half_pos hd))
  have hscale : Tendsto (fun u : ℝ => Real.exp ((β - γ) * u)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (sub_pos.mpr hγβ))
  obtain ⟨A, hA⟩ := eventually_atTop.mp (hscale.eventually_ge_atTop ((C + d) / d))
  refine ⟨d / 2, half_pos hd, max 0 (max A E) + W, fun t ht => ?_⟩
  obtain ⟨s, hs, hfs, hgs, hsign⟩ := hgap (phaseOrbit t) (hH t)
  let u := t - s
  have hu : u ∈ Icc (t - W) t := ⟨sub_le_sub_left hs.2 _, sub_le_self _ hs.1⟩
  have hE' : E ≤ u := (le_max_right A E).trans ((le_max_right _ _).trans
    (le_sub_iff_add_le.mpr ht |>.trans hu.1))
  have hA' : A ≤ u := (le_max_left A E).trans ((le_max_right _ _).trans
    (le_sub_iff_add_le.mpr ht |>.trans hu.1))
  have horbit (α : ℝ) : phaseProfile Complex.re α (phaseOrbit u) 0 =
      phaseProfile Complex.re α (phaseOrbit t) (-s) := by
    rw [phaseProfile_on_orbit, phaseProfile_on_orbit, add_zero, ← sub_eq_add_neg]
  have herr := hE u hE'
  simp only [Real.dist_eq, sub_zero, horbit] at herr
  have hsum : Real.exp ((β - γ) * u) * phaseProfile Complex.re β (phaseOrbit t) (-s) +
      phaseProfile Complex.re γ (phaseOrbit t) (-s) ≤ -d := by
    rcases hsign with hfs' | hgs'
    · have hdom := (div_le_iff₀ hd).mp (hA u hA')
      have hprod := mul_le_mul_of_nonneg_left hfs' (Real.exp_nonneg ((β - γ) * u))
      linarith only [hdom, hprod, hgs]
    · have hprod := mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg ((β - γ) * u)) hfs
      linarith only [hprod, hgs']
  have htail : Real.exp ((1 - γ) * u) * primeTail (Real.exp u) ≤ -(d / 2) := by
    have hupper := (le_abs_self _).trans herr.le
    linarith only [hupper, hsum]
  refine ⟨⟨u, hu, htail⟩, ?_⟩
  have htailneg : primeTail (Real.exp u) < 0 := by
    by_contra! h
    exact (htail.trans_lt (neg_lt_zero.mpr (half_pos hd))).not_ge
      (mul_nonneg (Real.exp_nonneg _) h)
  rw [← Real.exp_add, ← sub_eq_add_neg]
  have hleft : 1 ≤ Real.exp (t - W) :=
    Real.one_le_exp (sub_nonneg.mpr ((le_add_of_nonneg_left (le_max_left _ _)).trans ht))
  have hone (x : ℝ) (hx : x ∈ Icc (Real.exp (t - W)) (Real.exp t)) : 1 ≤ x :=
    hleft.trans hx.1
  apply intervalIntegral.integral_pos (Real.exp_lt_exp.mpr (sub_lt_self _ hW))
  · exact ((prime_integrable.continuousOn_Ici_primitive_Ioi.mono hone).neg.sup
      continuousOn_const).div Real.continuous_sqrt.continuousOn
      (fun x hx => (Real.sqrt_pos.mpr (zero_lt_one.trans_le (hone x hx))).ne')
  · exact fun x _ => div_nonneg (le_max_right _ _) (Real.sqrt_nonneg x)
  · exact ⟨Real.exp u, ⟨Real.exp_le_exp.mpr hu.1, Real.exp_le_exp.mpr hu.2⟩,
      div_pos ((neg_pos.mpr htailneg).trans_le (le_max_left _ _))
        (Real.sqrt_pos.mpr (Real.exp_pos _))⟩

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeCriticalTwoLines
