/- GID: D5/S3/Quantum/Information/InfiniteCalibrationControl
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/InfiniteCalibrationControl
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One positive parameter gives strictly feasible analytic control with exact infinite calibration jets. -/

import D5.S3.Quantum.Information.FiniteCalibrationControl

open Set Filter
open scoped Topology

namespace D5.S3.Quantum.Information.InfiniteCalibrationControl
noncomputable section
open D5.S3.Quantum.Information.FiniteCalibrationControl

def omega (b p : ℝ) := 2 * Real.pi * b / (1-p)
def amplitude (b p : ℝ) := (1-p) / (4 * Real.pi * b * p)
def phaseH (b p : ℝ) := 1 + amplitude b p * Real.sin (omega b p)
def phaseD (b p : ℝ) := (Real.sin ((1/2 : ℝ) * omega b p))^2
def phaseControl (a δ b k p : ℝ) :=
  (phaseH b p + k * center a δ * phaseD b p) / (1 + k * phaseD b p)
def phaseNode (b : ℝ) (n : ℕ) : ℝ := 1 - b / (n : ℝ)

/-- Strict physicality, analyticity, and exactly the positive-natural calibration jets
for one positive real control parameter. -/
def InfiniteScalarControl (a δ b k : ℝ) : Prop :=
  0 < k ∧
  (∀ p ∈ Ioo a 1, 0 < phaseControl a δ b k p ∧
    (radius a δ p)^2 * energy a δ (phaseControl a δ b k p) < 1) ∧
  AnalyticOnNhd ℝ (phaseControl a δ b k) (Ioo a 1) ∧
  (∀ p ∈ Ioo a 1,
    (phaseControl a δ b k p = 1 ∧ deriv (phaseControl a δ b k) p = beta p) ↔
      ∃ n : ℕ, 0 < n ∧ p = phaseNode b n)

/-- A single positive real parameter realizes full physicality on the whole open
interval and exactly the infinite sequence of simultaneous value and derivative jets. -/
theorem result (a δ b : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hδ : 0 < δ) (hδL : δ < (1-a)/4) (hδa : δ < (1-a^2)/16)
    (hb : 0 < b) (hbδ : b < 1 - a/(1-δ)) :
    ∃ k : ℝ, InfiniteScalarControl a δ b k := by
  have hUniform :
      ∃ k : ℝ, 0 < k ∧ ∀ p ∈ Ioo a 1,
        0 < phaseControl a δ b k p ∧
        (radius a δ p)^2 * energy a δ (phaseControl a δ b k p) < 1 := by
    classical
    have hL : 0 < L a := sub_pos.mpr ha1
    have hlam : 0 < lam a δ := by unfold lam L; linarith only [hδL, ha1]
    have hδ1 : 0 < 1-δ := by unfold L at hL; linarith only [hδL, ha]
    have hc : 0 < center a δ := div_pos hlam hL
    have hc1 : center a δ < 1 := by
      rw [FiniteCalibrationControl.center, div_lt_one hL]; unfold lam; linarith only [hδ]
    have hc34 : (3:ℝ)/4 < center a δ := by
      rw [FiniteCalibrationControl.center, lt_div_iff₀ hL]; unfold lam L; linarith only [hδL]
    have hradius : ∀ p ∈ Icc a 1,
        (radius a δ p)^2 = a / lam a δ * ((1-p)/p) := by
      intro p hp
      unfold radius
      rw [mul_pow, Real.sq_sqrt (le_of_lt (div_pos ha hlam)),
        Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hp.2) (le_of_lt (ha.trans_le hp.1)))]
    have hrbound : ∀ p ∈ Icc a 1, (radius a δ p)^2 ≤ 1 / center a δ := by
      intro p hp
      rw [hradius p hp]
      have hp0 : 0 < p := ha.trans_le hp.1
      have hcEq : 1 / center a δ = L a / lam a δ := by unfold FiniteCalibrationControl.center; field_simp
      rw [hcEq]
      calc
        a / lam a δ * ((1-p)/p) = (a*(1-p)/p) / lam a δ := by ring
        _ ≤ L a / lam a δ := by
          apply (div_le_div_iff_of_pos_right hlam).mpr
          apply (div_le_iff₀ hp0).mpr
          unfold L
          nlinarith only [hp.1]
    have hec : energy a δ (center a δ) =
        (center a δ)^2 + (1-center a δ)^2/4 := by
      unfold energy gamma FiniteCalibrationControl.center
      field_simp [ne_of_gt hL, ne_of_gt hlam, ne_of_gt hδ]
      unfold lam
      ring
    have hcenter : ∀ p ∈ Icc a 1,
        (radius a δ p)^2 * energy a δ (center a δ) < 1 := by
      intro p hp
      have heg : 0 ≤ energy a δ (center a δ) := by
        unfold energy; positivity
      calc
        _ ≤ (1 / center a δ) * energy a δ (center a δ) :=
          mul_le_mul_of_nonneg_right (hrbound p hp) heg
        _ < 1 := by
          rw [hec, one_div_mul_eq_div, div_lt_one hc]
          nlinarith only [hc34, hc1]
    have henergyconv : ConvexOn ℝ (Ioi 0) (energy a δ) := by
      have hv : ConvexOn ℝ (Ioi 0) (fun x : ℝ => x+x⁻¹-2) := by
        have hi : ConvexOn ℝ (Ioi 0) (fun x : ℝ => x⁻¹) := by
          simpa using (convexOn_zpow (-1 : ℤ) : ConvexOn ℝ (Ioi 0) (fun x : ℝ => x^(-1 : ℤ)))
        simpa only [Pi.add_apply, id_eq, sub_eq_add_neg] using!
          ((convexOn_id (convex_Ioi (0:ℝ))).add hi).add (convexOn_const (-2) (convex_Ioi (0:ℝ)))
      have hv0 : ∀ ⦃x : ℝ⦄, x ∈ Ioi 0 → 0 ≤ x+x⁻¹-2 := by
        intro x hx
        have hx0 : 0 < x := hx
        have hh := sq_nonneg (x-1)
        have hinv : x*x⁻¹=1 := mul_inv_cancel₀ (ne_of_gt hx0)
        nlinarith only [hh, hinv, hx0]
      have hs := hv.pow hv0 2
      have hsq := (convexOn_pow (𝕜 := ℝ) 2).subset Ioi_subset_Ici_self (convex_Ioi (0:ℝ))
      simpa only [energy, Pi.pow_apply, Pi.add_apply, smul_eq_mul] using! hsq.add (hs.smul (sq_nonneg (gamma a δ)))
    have henergycont : ∀ s : ℝ, 0 < s → ContinuousAt (energy a δ) s := by
      intro s hs
      unfold energy
      fun_prop (disch := exact ne_of_gt hs)
    let c : ℝ := center a δ
    let f : ℝ → ℝ → ℝ := phaseControl a δ b
    have hDnonneg : ∀ p, 0 ≤ phaseD b p := fun p => sq_nonneg _
    have hden : ∀ k : ℝ, 0 ≤ k → ∀ p : ℝ, 0 < 1+k*phaseD b p := by
      intro k hk p
      have := mul_nonneg hk (hDnonneg p)
      linarith only [this]
    have hrcont : ∀ p : ℝ, 0 < p → ContinuousAt (fun x => (radius a δ x)^2) p := by
      intro p hp
      unfold radius
      fun_prop (disch := exact ne_of_gt hp)
    have hmix : ∀ p x y t : ℝ, 0 < x → 0 < y →
        (radius a δ p)^2*energy a δ x < 1 →
        (radius a δ p)^2*energy a δ y < 1 →
        0 < t → t ≤ 1 →
        0 < t*x+(1-t)*y ∧
        (radius a δ p)^2*energy a δ (t*x+(1-t)*y) < 1 := by
      intro p x y t hx hy hex hey ht ht1
      have hnt : 0 ≤ 1-t := sub_nonneg.mpr ht1
      have hcv := henergyconv.2 hx hy ht.le hnt (by ring : t+(1-t)=1)
      simp only [smul_eq_mul] at hcv
      have hmul := mul_le_mul_of_nonneg_left hcv (sq_nonneg (radius a δ p))
      have hstrict := mul_lt_mul_of_pos_left hex ht
      have hweak := mul_le_mul_of_nonneg_left hey.le hnt
      constructor
      · linarith only [mul_pos ht hx, mul_nonneg hnt hy.le]
      · nlinarith only [hmul, hstrict, hweak]
    have hmixform : ∀ k p : ℝ, 0 ≤ k →
        f k p = (1/(1+k*phaseD b p))*phaseH b p +
          (1-1/(1+k*phaseD b p))*c := by
      intro k p hk
      dsimp [f, phaseControl, c]
      field_simp [ne_of_gt (hden k hk p)]
      <;> ring
    have hHgood : ∀ k p : ℝ, 0 < k → p ∈ Icc a 1 →
        0 < phaseH b p → (radius a δ p)^2*energy a δ (phaseH b p) < 1 →
        0 < f k p ∧ (radius a δ p)^2*energy a δ (f k p) < 1 := by
      intro k p hk hp hHp hHg
      rw [hmixform k p hk.le]
      apply hmix p (phaseH b p) c (1/(1+k*phaseD b p)) hHp hc hHg (hcenter p hp)
      · exact one_div_pos.mpr (hden k hk.le p)
      · apply (div_le_one (hden k hk.le p)).mpr
        have := mul_nonneg hk.le (hDnonneg p)
        linarith only [this]
    have hamp0 : Tendsto (amplitude b) (𝓝 1) (𝓝 0) := by
      have hcont : ContinuousAt (amplitude b) 1 := by
        unfold amplitude
        fun_prop (disch := positivity)
      simpa [amplitude] using hcont.tendsto
    have hprod0 : Tendsto (fun p => amplitude b p * Real.sin (omega b p))
        (𝓝 1) (𝓝 0) := by
      apply squeeze_zero_norm (a := fun p => |amplitude b p|)
      · intro p
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
      · simpa using hamp0.abs
    have hHlim : Tendsto (phaseH b) (𝓝 1) (𝓝 1) := by
      simpa only [add_zero] using! ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝 1) (𝓝 1)).add hprod0)
    have hRlim : Tendsto (fun p => (radius a δ p)^2) (𝓝 1) (𝓝 0) := by
      simpa [radius] using (hrcont 1 (by norm_num)).tendsto
    have hphyslim : Tendsto (fun p => (radius a δ p)^2*energy a δ (phaseH b p))
        (𝓝 1) (𝓝 0) := by
      simpa using hRlim.mul ((henergycont 1 (by norm_num)).tendsto.comp hHlim)
    have htail_event : ∀ᶠ p in 𝓝 (1:ℝ),
        0 < phaseH b p ∧ (radius a δ p)^2*energy a δ (phaseH b p) < 1 := by
      filter_upwards [hHlim.eventually (lt_mem_nhds (by norm_num : (0:ℝ)<1)),
        hphyslim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with p hp hg
      exact ⟨hp, hg⟩
    obtain ⟨ε, hε, hεgood⟩ := Metric.eventually_nhds_iff.mp htail_event
    let q : ℝ := max a (1-ε/2)
    have hqa : a ≤ q := le_max_left _ _
    have hq1 : q < 1 := max_lt ha1 (by linarith only [hε])
    have htail : ∀ k p : ℝ, 0 < k → q < p → p < 1 →
        0 < f k p ∧ (radius a δ p)^2*energy a δ (f k p) < 1 := by
      intro k p hk hqp hp1
      have hpε : dist p 1 < ε := by
        rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hp1)]
        have hqε : 1-ε/2 ≤ q := le_max_right _ _
        linarith only [hqε, hqp, hε]
      have hh := hεgood hpε
      exact hHgood k p hk ⟨hqa.trans hqp.le, hp1.le⟩ hh.1 hh.2
    have hzero : ∀ p ∈ Icc a q, phaseD b p = 0 →
        phaseH b p = 1 ∧ (radius a δ p)^2 < 1 := by
      intro p hp hD
      have hp0 : 0 < p := ha.trans_le hp.1
      have hp1 : p < 1 := hp.2.trans_lt hq1
      have h1p : 0 < 1-p := sub_pos.mpr hp1
      have hsin : Real.sin ((1/2:ℝ)*omega b p) = 0 := by
        exact (sq_eq_zero_iff).mp hD
      have hsfull : Real.sin (omega b p) = 0 := by
        have ht := Real.sin_two_mul ((1/2:ℝ)*omega b p)
        rw [hsin] at ht
        convert ht using 1 <;> ring
      have hH : phaseH b p = 1 := by simp [phaseH, hsfull]
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
      have hwpos : 0 < (1/2:ℝ)*omega b p := by
        unfold omega
        positivity
      have hnpos : (0:ℝ) < n := by nlinarith only [Real.pi_pos, hn, hwpos]
      have hnZ : 0 < n := by exact_mod_cast hnpos
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show (1:ℤ) ≤ n by omega)
      have hratio : b/(1-p) = (n:ℝ) := by
        apply (mul_left_cancel₀ (ne_of_gt Real.pi_pos))
        calc
          Real.pi * (b/(1-p)) = (1/2:ℝ)*omega b p := by unfold omega; ring
          _ = Real.pi * (n:ℝ) := by rw [← hn]; ring
      have hb1p : 1-p ≤ b := by
        have hrat : 1 ≤ b/(1-p) := by rw [hratio]; exact hn1
        have := (le_div_iff₀ h1p).mp hrat
        linarith only [this]
      have hthreshold : a/(1-δ) < p := by linarith only [hbδ, hb1p]
      refine ⟨hH, ?_⟩
      rw [hradius p ⟨hp.1, hp1.le⟩]
      have hh := (div_lt_iff₀ hδ1).mp hthreshold
      calc
        a / lam a δ * ((1-p)/p) = a*(1-p)/(lam a δ*p) := by ring
        _ < 1 := by
          rw [div_lt_one (mul_pos hlam hp0)]
          unfold lam L
          nlinarith only [hh]
    have hfcont : ∀ k p : ℝ, 0 ≤ k → 0 < p → p < 1 → ContinuousAt (f k) p := by
      intro k p hk hp hp1
      have hHc : ContinuousAt (phaseH b) p := by
        unfold phaseH amplitude omega
        fun_prop (disch := positivity)
      have hDc : ContinuousAt (phaseD b) p := by
        unfold phaseD omega
        fun_prop (disch := exact ne_of_gt (sub_pos.mpr hp1))
      exact (hHc.add ((continuousAt_const.mul continuousAt_const).mul hDc)).div
        (continuousAt_const.add (continuousAt_const.mul hDc)) (ne_of_gt (hden k hk p))
    have hfmono : ∀ k l : ℝ, 0 < k → k ≤ l → ∀ p : ℝ,
        0 < f k p → (radius a δ p)^2*energy a δ (f k p) < 1 →
        (radius a δ p)^2*energy a δ c < 1 →
        0 < f l p ∧ (radius a δ p)^2*energy a δ (f l p) < 1 := by
      intro k l hk hkl p hpos hgood hcgood
      have hl : 0 ≤ l := hk.le.trans hkl
      let t := (1+k*phaseD b p)/(1+l*phaseD b p)
      have ht : 0 < t := div_pos (hden k hk.le p) (hden l hl p)
      have ht1 : t ≤ 1 := by
        apply (div_le_one (hden l hl p)).mpr
        nlinarith only [mul_nonneg (sub_nonneg.mpr hkl) (hDnonneg p)]
      have heq : f l p = t*f k p+(1-t)*c := by
        dsimp [f, phaseControl, t, c]
        field_simp [ne_of_gt (hden k hk.le p), ne_of_gt (hden l hl p),
          show 1+phaseD b p*k ≠ 0 by nlinarith only [hden k hk.le p]]
        ring
      rw [heq]
      exact hmix p (f k p) c t hpos hc hgood hcgood ht ht1
    have hfpoint : ∀ p ∈ Icc a q, ∃ k : ℝ, 0 < k ∧ 0 < f k p ∧
        (radius a δ p)^2*energy a δ (f k p) < 1 := by
      intro p hp
      by_cases hz : phaseD b p = 0
      · have hn := hzero p hp hz
        have hf : ∀ k, f k p = 1 := by intro k; simp [f, phaseControl, hz, hn.1]
        refine ⟨1, by norm_num, ?_, ?_⟩
        · rw [hf]; norm_num
        · rw [hf]
          simpa only [energy, inv_one, one_pow, show (1:ℝ)+1-2=0 by norm_num,
            zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero, mul_one] using hn.2
      · have hP2 : 0 < phaseD b p := lt_of_le_of_ne (hDnonneg p) (Ne.symm hz)
        have htop : Tendsto (fun k : ℝ => 1+k*phaseD b p) atTop atTop :=
          tendsto_const_nhds.add_atTop ((tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop).atTop_mul_const hP2)
        have ht : Tendsto (fun k : ℝ => c+(phaseH b p-c)/(1+k*phaseD b p)) atTop (𝓝 c) := by
          simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop htop)
        have ht' : Tendsto (fun k : ℝ => f k p) atTop (𝓝 c) := by
          apply ht.congr'
          filter_upwards [eventually_gt_atTop (0:ℝ)] with k hk
          dsimp [f, phaseControl, c]
          field_simp [ne_of_gt (hden k hk.le p)]
          ring
        have hevent : ∀ᶠ k : ℝ in atTop, 0 < k ∧ 0 < f k p ∧
            (radius a δ p)^2*energy a δ (f k p) < 1 := by
          have hp0 := ht'.eventually (lt_mem_nhds hc)
          have hlim := ((henergycont c hc).tendsto.comp ht').const_mul ((radius a δ p)^2)
          have hp1 := hlim.eventually (gt_mem_nhds (hcenter p ⟨hp.1, hp.2.trans hq1.le⟩))
          filter_upwards [eventually_gt_atTop (0:ℝ), hp0, hp1] with k hk hkp hk1
          exact ⟨hk, hkp, hk1⟩
        exact hevent.exists
    let U : {k : ℝ // 0 < k} → Set ℝ := fun k =>
      {p | 0 < p ∧ p < 1 ∧ (radius a δ p)^2*energy a δ c < 1 ∧
        0 < f k p ∧ (radius a δ p)^2*energy a δ (f k p) < 1}
    have hUopen : ∀ k, IsOpen (U k) := by
      intro k
      apply isOpen_iff_mem_nhds.mpr
      intro p hp
      have hfc := hfcont k p k.property.le hp.1 hp.2.1
      have hr := hrcont p hp.1
      have hcc := hr.mul_const (energy a δ c)
      have hpc := hr.mul ((henergycont (f k p) hp.2.2.2.1).comp hfc)
      filter_upwards [lt_mem_nhds hp.1, gt_mem_nhds hp.2.1,
        hcc.eventually_lt continuousAt_const hp.2.2.1,
        continuousAt_const.eventually_lt hfc hp.2.2.2.1,
        hpc.eventually_lt continuousAt_const hp.2.2.2.2] with x hx hx0 hx1 hx2 hx3
      exact ⟨hx, hx0, hx1, hx2, hx3⟩
    have hUcover : Icc a q ⊆ ⋃ k, U k := by
      intro p hp
      obtain ⟨k, hk, hkp, hkg⟩ := hfpoint p hp
      exact mem_iUnion.mpr ⟨⟨k,hk⟩, ha.trans_le hp.1, hp.2.trans_lt hq1,
        hcenter p ⟨hp.1, hp.2.trans hq1.le⟩, hkp, hkg⟩
    have hUdirect : Directed (· ⊆ ·) U := by
      intro i j
      let k : {k : ℝ // 0 < k} := ⟨max i.val j.val, lt_max_iff.mpr (Or.inl i.property)⟩
      refine ⟨k, ?_, ?_⟩
      · intro p hp
        exact ⟨hp.1, hp.2.1, hp.2.2.1, hfmono i k i.property (le_max_left _ _) p
          hp.2.2.2.1 hp.2.2.2.2 hp.2.2.1⟩
      · intro p hp
        exact ⟨hp.1, hp.2.1, hp.2.2.1, hfmono j k j.property (le_max_right _ _) p
          hp.2.2.2.1 hp.2.2.2.2 hp.2.2.1⟩
    obtain ⟨k, hkall⟩ := isCompact_Icc.elim_directed_cover U hUopen hUcover hUdirect
    refine ⟨k, k.property, ?_⟩
    intro p hp
    by_cases hpq : p ≤ q
    · exact (hkall ⟨hp.1.le, hpq⟩).2.2.2
    · exact htail k p k.property (lt_of_not_ge hpq) hp.2

  have hJets :
      ∀ k : ℝ, 0 < k →
        AnalyticOnNhd ℝ (phaseControl a δ b k) (Ioo a 1) ∧
        (∀ p ∈ Ioo a 1,
          (phaseControl a δ b k p = 1 ∧ deriv (phaseControl a δ b k) p = beta p) ↔
            ∃ n : ℕ, 0 < n ∧ p = phaseNode b n) := by
    have analytic_fragment (a δ b k : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
        AnalyticOnNhd ℝ (phaseControl a δ b k) (Ioo a 1) := by
      intro p hp
      have hp0 : p ≠ 0 := ne_of_gt (ha.trans hp.1)
      have hp1 : 1-p ≠ 0 := ne_of_gt (sub_pos.mpr hp.2)
      have hb0 : b ≠ 0 := ne_of_gt hb
      have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      have hden : 1 + k * phaseD b p ≠ 0 := by
        have : 0 < 1 + k * phaseD b p := by unfold phaseD; positivity
        exact ne_of_gt this
      unfold phaseControl phaseH phaseD amplitude omega at *
      fun_prop (disch := positivity)


    have root_deriv (a δ b k p : ℝ) (hb : 0 < b) (hk : 0 < k)
        (hp0 : 0 < p) (hp1 : p < 1) (hs : phaseControl a δ b k p = 1) :
        HasDerivAt (phaseControl a δ b k)
          (((-1 / (4 * Real.pi * b * p^2)) * Real.sin (omega b p) +
            amplitude b p * Real.cos (omega b p) * (2 * Real.pi * b / (1-p)^2) -
            k * (1-center a δ) * Real.sin ((1/2:ℝ) * omega b p) *
              Real.cos ((1/2:ℝ) * omega b p) * (2 * Real.pi * b / (1-p)^2)) /
            (1 + k * phaseD b p)) p := by
      have hpz : p ≠ 0 := ne_of_gt hp0
      have hqz : 1-p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
      have hbz : b ≠ 0 := ne_of_gt hb
      have hpiz : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      have hden : 1 + k * phaseD b p ≠ 0 := by
        have : 0 < 1 + k * phaseD b p := by unfold phaseD; positivity
        exact ne_of_gt this
      have hw : HasDerivAt (omega b) (2 * Real.pi * b / (1-p)^2) p := by
        convert! (hasDerivAt_const p (2 * Real.pi * b)).div
          ((hasDerivAt_id p).const_sub 1) hqz using 1 <;>
          (try dsimp [omega]) <;> field_simp <;> ring
      have hA : HasDerivAt (amplitude b) (-1 / (4 * Real.pi * b * p^2)) p := by
        convert! ((hasDerivAt_id p).const_sub 1).div
          ((hasDerivAt_id p).const_mul (4 * Real.pi * b))
          (by positivity : 4 * Real.pi * b * p ≠ 0) using 1 <;>
          (try dsimp [amplitude]) <;> field_simp <;> ring
      have hD : HasDerivAt (phaseD b)
          (Real.sin ((1/2:ℝ) * omega b p) * Real.cos ((1/2:ℝ) * omega b p) *
            (2 * Real.pi * b / (1-p)^2)) p := by
        convert! ((hw.const_mul (1/2:ℝ)).sin.pow 2) using 1 <;>
          (try dsimp [phaseD]) <;> ring
      have hH : HasDerivAt (phaseH b)
          ((-1 / (4 * Real.pi * b * p^2)) * Real.sin (omega b p) +
            amplitude b p * Real.cos (omega b p) * (2 * Real.pi * b / (1-p)^2)) p := by
        convert! (hA.mul hw.sin).const_add 1 using 1 <;> (try dsimp [phaseH]) <;> ring
      have hnum : phaseH b p + k * center a δ * phaseD b p = 1 + k * phaseD b p := by
        exact (div_eq_one_iff_eq hden).mp hs
      convert! (hH.add (hD.const_mul (k * center a δ))).div
        ((hD.const_mul k).const_add 1) hden using 1
      simp only [Pi.add_apply] at *
      rw [hnum]
      field_simp
      ring


    have sine_zero_locus (b p : ℝ) (hb : 0 < b) (hp : p < 1) :
        Real.sin ((1/2:ℝ) * omega b p) = 0 ↔
          ∃ n : ℕ, 0 < n ∧ p = phaseNode b n := by
      have hq : 0 < 1-p := sub_pos.mpr hp
      have ht : 0 < (1/2:ℝ) * omega b p := by unfold omega; positivity
      constructor
      · intro hs
        obtain ⟨z, hz⟩ := Real.sin_eq_zero_iff.mp hs
        have hzpos : (0:ℝ) < z := by
          have : 0 < (z:ℝ) * Real.pi := by rw [hz]; exact ht
          exact (mul_pos_iff_of_pos_right Real.pi_pos).mp this
        have hzi : (0:ℤ) < z := by exact_mod_cast hzpos
        have hcast : (z.toNat:ℝ) = (z:ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hzi.le
        have hn : 0 < z.toNat := by omega
        refine ⟨z.toNat, hn, ?_⟩
        have hzrel : (z:ℝ) * (1-p) = b := by
          dsimp [omega] at hz
          have hh := (eq_div_iff (ne_of_gt hq)).mp
            (show (z:ℝ) * Real.pi = Real.pi * b / (1-p) by convert hz using 1 <;> ring)
          nlinarith only [Real.pi_pos, hh]
        unfold phaseNode
        rw [hcast]
        field_simp [ne_of_gt hzpos]
        nlinarith only [hzrel]
      · rintro ⟨n, hn, rfl⟩
        have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
        have hw : (1/2:ℝ) * omega b (phaseNode b n) = (n:ℝ) * Real.pi := by
          unfold omega phaseNode
          field_simp [hn0, ne_of_gt hb]
          ring
        rw [hw]
        exact Real.sin_nat_mul_pi n

    have nonnode_root_negative (a δ b k p : ℝ)
        (ha1 : a < 1) (hδ : 0 < δ) (hb : 0 < b) (hk : 0 < k)
        (hp0 : 0 < p) (hp1 : p < 1) (hs : phaseControl a δ b k p = 1)
        (hsn : Real.sin ((1/2:ℝ) * omega b p) ≠ 0) :
        deriv (phaseControl a δ b k) p < 0 := by
      let t := (1/2:ℝ) * omega b p
      let A := amplitude b p
      let Ap := -1 / (4 * Real.pi * b * p^2)
      let w := 2 * Real.pi * b / (1-p)^2
      let c := k * (1-center a δ)
      have hA : 0 < A := by dsimp [A, amplitude]; positivity
      have hAp : Ap < 0 := by dsimp [Ap]; apply div_neg_of_neg_of_pos (by norm_num); positivity
      have hw : 0 < w := by dsimp [w]; positivity
      have hc : 0 < c := by
        have hc1 : center a δ < 1 := by
          unfold FiniteCalibrationControl.center lam L
          rw [div_lt_one (sub_pos.mpr ha1)]
          linarith only [hδ]
        exact mul_pos hk (sub_pos.mpr hc1)
      have hden : 0 < 1 + k * phaseD b p := by unfold phaseD; positivity
      have htw : omega b p = 2*t := by dsimp [t]; ring
      have hsin : Real.sin (omega b p) = 2 * Real.sin t * Real.cos t := by
        rw [htw, Real.sin_two_mul]
      have hcos : Real.cos (omega b p) = (Real.cos t)^2 - (Real.sin t)^2 := by
        rw [htw, Real.cos_two_mul']
      have hroot : 2*A*Real.cos t = c*Real.sin t := by
        have hh := (div_eq_one_iff_eq (ne_of_gt hden)).mp hs
        change 1 + A * Real.sin (omega b p) + k * center a δ * (Real.sin t)^2 =
          1 + k * (Real.sin t)^2 at hh
        rw [hsin] at hh
        have hh' : Real.sin t * (2*A*Real.cos t - c*Real.sin t) = 0 := by
          dsimp [c]
          nlinarith only [hh]
        exact sub_eq_zero.mp ((mul_eq_zero.mp hh').resolve_left hsn)
      have hsc : 0 < Real.sin t * Real.cos t := by
        have hh := congrArg (fun x : ℝ => x * Real.sin t) hroot
        have hpos : 0 < c*(Real.sin t)^2 := mul_pos hc (sq_pos_of_ne_zero hsn)
        have hm : 0 < (2*A) * (Real.sin t * Real.cos t) := by nlinarith only [hh, hpos]
        exact (mul_pos_iff_of_pos_left (by positivity : 0 < 2*A)).mp hm
      have hnum : Ap * Real.sin (omega b p) + A * Real.cos (omega b p) * w -
          c * Real.sin t * Real.cos t * w = 2*Ap*(Real.sin t*Real.cos t)-A*w := by
        rw [hsin, hcos]
        have hh := congrArg (fun x : ℝ => x * Real.cos t * w) hroot
        have hid := congrArg (fun x : ℝ => A*w*x) (Real.sin_sq_add_cos_sq t)
        nlinarith only [hh, hid]
      have hd := (root_deriv a δ b k p hb hk hp0 hp1 hs).deriv
      change deriv (phaseControl a δ b k) p =
        (Ap * Real.sin (omega b p) + A * Real.cos (omega b p) * w -
          c * Real.sin t * Real.cos t * w) / (1 + k * phaseD b p) at hd
      rw [hd, hnum]
      apply div_neg_of_neg_of_pos _ hden
      have hneg : 2*Ap*(Real.sin t*Real.cos t) < 0 :=
        mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hAp) hsc
      have hpos := mul_pos hA hw
      linarith only [hneg, hpos]


    have zero_sine_jet (a δ b k p : ℝ) (hb : 0 < b) (hk : 0 < k)
        (hp0 : 0 < p) (hp1 : p < 1)
        (hz : Real.sin ((1/2:ℝ) * omega b p) = 0) :
        phaseControl a δ b k p = 1 ∧ deriv (phaseControl a δ b k) p = beta p := by
      have htw : omega b p = 2*((1/2:ℝ)*omega b p) := by ring
      have hsin : Real.sin (omega b p) = 0 := by
        conv_lhs => rw [htw, Real.sin_two_mul, hz]
        ring
      have hcos : Real.cos (omega b p) = 1 := by
        conv_lhs => rw [htw, Real.cos_two_mul_eq_one_sub, hz]
        ring
      have hD : phaseD b p = 0 := by unfold phaseD; rw [hz]; norm_num
      have hH : phaseH b p = 1 := by simp [phaseH, hsin]
      have hs : phaseControl a δ b k p = 1 := by simp [phaseControl, hD, hH]
      refine ⟨hs, ?_⟩
      rw [(root_deriv a δ b k p hb hk hp0 hp1 hs).deriv, hsin, hcos, hz, hD]
      simp only [mul_zero, zero_mul, zero_add, add_zero, mul_one, sub_zero, div_one]
      unfold amplitude beta
      field_simp [ne_of_gt hb, ne_of_gt hp0, ne_of_gt (sub_pos.mpr hp1),
        ne_of_gt Real.pi_pos]
      ring
    intro k hk
    refine ⟨analytic_fragment a δ b k ha hb hk, ?_⟩
    intro p hp
    have hp0 : 0 < p := ha.trans hp.1
    constructor
    · rintro ⟨hs, hd⟩
      apply (sine_zero_locus b p hb hp.2).mp
      by_contra hsn
      have hneg := nonnode_root_negative a δ b k p ha1 hδ hb hk hp0 hp.2 hs hsn
      have hq : 0 < 1-p := sub_pos.mpr hp.2
      have hbeta : 0 < beta p := by unfold beta; positivity
      rw [hd] at hneg
      exact (not_lt_of_gt hbeta) hneg
    · intro hn
      exact zero_sine_jet a δ b k p hb hk hp0 hp.2 ((sine_zero_locus b p hb hp.2).mpr hn)

  obtain ⟨k, hk, hphysical⟩ := hUniform
  exact ⟨k, hk, hphysical, hJets k hk⟩

end
end D5.S3.Quantum.Information.InfiniteCalibrationControl
