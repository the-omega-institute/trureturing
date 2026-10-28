/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeTwoMomentRecovery
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeTwoMomentRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two response moments determine actual posteriors of one installed depth prior. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.Order.IntermediateValue

/-! Two response moments identify actual finite-history posteriors of one installed prior. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeTwoMomentRecovery

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open NativeConditionalControl.DepthLaw NativeConditionalControl.Prefix
open FourthSegmentLawRecovery.RealAtoms NativeObserverJointLaw

private def logTilt (a b c x : ℝ) : ℝ := a * Real.log x + b * Real.log (1 - x) + c

private theorem log_tilt_continuous (a b c : ℝ) :
    ContinuousOn (logTilt a b c) (Ioo 0 1) := by
  apply ContinuousOn.add _ continuousOn_const
  apply ContinuousOn.add
  · exact continuousOn_const.mul (Real.continuousOn_log.mono (fun x hx => hx.1.ne'))
  · apply continuousOn_const.mul
    apply ContinuousOn.log (continuousOn_const.sub continuousOn_id)
    intro x hx
    exact (sub_pos.mpr hx.2).ne'

private theorem log_tilt_positive_convex (a b c : ℝ) (ha : 0 ≤ a) :
    Convex ℝ {x ∈ Ioo 0 1 | 0 < logTilt a b c x} := by
  by_cases hb : 0 ≤ b
  · have hl : ConcaveOn ℝ (Ioo (0 : ℝ) 1) Real.log :=
      strictConcaveOn_log_Ioi.concaveOn.subset (fun _ hx => hx.1) (convex_Ioo _ _)
    have hr : ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun x => Real.log (1 - x)) := by
      refine ⟨convex_Ioo _ _, ?_⟩
      intro x hx y hy u v hu hv huv
      have h := strictConcaveOn_log_Ioi.concaveOn.2
        (sub_pos.mpr hx.2) (sub_pos.mpr hy.2) hu hv huv
      have he : u * (1 - x) + v * (1 - y) = 1 - (u * x+v * y) := by nlinarith
      simpa only [smul_eq_mul, he] using h
    have h := ((hl.smul ha).add (hr.smul hb)).add_const c
    exact h.convex_gt 0
  · have hm : MonotoneOn (logTilt a b c) (Ioo 0 1) := by
      intro x hx y hy hxy
      have hl := Real.strictMonoOn_log.monotoneOn hx.1 hy.1 hxy
      have hr := Real.strictMonoOn_log.monotoneOn
        (sub_pos.mpr hy.2) (sub_pos.mpr hx.2) (by linarith : 1 - y ≤ 1 - x)
      have h1 := mul_le_mul_of_nonneg_left hl ha
      have h2 := mul_le_mul_of_nonpos_left hr (le_of_not_ge hb)
      dsimp [logTilt]
      linarith
    apply (convex_iff_ordConnected).mpr
    constructor
    intro x hx y hy z hz
    exact ⟨⟨hx.1.1.trans_le hz.1, hz.2.trans_lt hy.1.2⟩,
      hx.2.trans_le (hm hx.1
        ⟨hx.1.1.trans_le hz.1, hz.2.trans_lt hy.1.2⟩ hz.1)⟩

private theorem positive_interval_separator (a b c : ℝ) (ha : 0 ≤ a)
    (hne : ∃ x ∈ Ioo 0 1, 0 < logTilt a b c x) :
    ∃ l u : ℝ, ∀ x ∈ Ioo 0 1,
      (0 < logTilt a b c x → 0 < (x - l) * (u - x)) ∧
      (logTilt a b c x ≤ 0 → (x - l) * (u - x) ≤ 0) := by
  let S := {x ∈ Ioo (0 : ℝ) 1 | 0 < logTilt a b c x}
  have hS : S.Nonempty := hne
  have hb : BddBelow S := ⟨0, fun _ hx => hx.1.1.le⟩
  have hu : BddAbove S := ⟨1, fun _ hx => hx.1.2.le⟩
  have hc : IsConnected S :=
    ⟨hS, (log_tilt_positive_convex a b c ha).isPreconnected⟩
  have hopen : IsOpen S := by
    exact (log_tilt_continuous a b c).isOpen_inter_preimage isOpen_Ioo isOpen_Ioi
  refine ⟨sInf S, sSup S, ?_⟩
  intro x hx
  constructor
  · intro hg
    obtain ⟨v, w, ⟨hvx, hxw⟩, hsub⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds ⟨hx, hg⟩)
    obtain ⟨y, hvy, hyx⟩ := exists_between hvx
    obtain ⟨z, hxz, hzw⟩ := exists_between hxw
    have hyl : sInf S ≤ y := csInf_le hb (hsub ⟨hvy, hyx.trans hxw⟩)
    have hzu : z ≤ sSup S := le_csSup hu (hsub ⟨hvx.trans hxz, hzw⟩)
    exact mul_pos (sub_pos.mpr (hyl.trans_lt hyx))
      (sub_pos.mpr (hxz.trans_le hzu))
  · intro hg
    by_cases hl : x ≤ sInf S
    · have hxu : x ≤ sSup S := hl.trans (csInf_le_csSup hS hb hu)
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hl) (sub_nonneg.mpr hxu)
    · have hul : sSup S ≤ x := by
        by_contra hh
        have hp := hc.Ioo_csInf_csSup_subset hb hu
          ⟨lt_of_not_ge hl, lt_of_not_ge hh⟩
        exact (not_lt_of_ge hg) hp.2
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (le_of_not_ge hl))
        (sub_nonpos.mpr hul)

private theorem normalizer_real_pos (μ : PMF Depth) (h : List Operation)
    (c : AcquiredNativeState) (hc : run h = some c) :
    0 < (normalizer μ h).toReal := by
  have hn := normalizer_bounds μ h c hc
  exact ENNReal.toReal_pos hn.1.ne'
    (ne_top_of_le_ne_top ENNReal.one_ne_top hn.2)

private theorem posterior_real (μ : PMF Depth) (h : List Operation)
    (c : AcquiredNativeState) (hc : run h = some c) (k : Depth) :
    (posterior μ h c hc k).toReal = (μ k).toReal *
      (rate k : ℝ) ^ (readLetters h).count 0 *
      (1 - (rate k : ℝ)) ^ (readLetters h).count 1 / (normalizer μ h).toReal := by
  rw [posterior, PMF.normalize_apply]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv]
  change (μ k).toReal * (likelihood h k).toReal * (normalizer μ h).toReal⁻¹ = _
  rw [likelihood, word_counts]
  simp [ENNReal.toReal_mul, ENNReal.toReal_pow, alphaMass, betaMass, div_eq_mul_inv,
    mul_assoc]

private theorem posterior_log (μ : PMF Depth) (h : List Operation)
    (c : AcquiredNativeState) (hc : run h = some c) (k : Depth) (hk : μ k ≠ 0) :
    0 < (posterior μ h c hc k).toReal ∧
    Real.log (posterior μ h c hc k).toReal = Real.log (μ k).toReal +
      ((readLetters h).count 0 : ℝ) * Real.log (rate k : ℝ) +
      ((readLetters h).count 1 : ℝ) * Real.log (1 - (rate k : ℝ)) -
      Real.log (normalizer μ h).toReal := by
  have hm := ENNReal.toReal_pos hk (μ.apply_ne_top k)
  have hr := ratio_interior k
  change 0 < (rate k : ℝ) ∧ (rate k : ℝ) < 1 at hr
  have hb : 0 < 1-(rate k : ℝ) := sub_pos.mpr hr.2
  have hn := normalizer_real_pos μ h c hc
  rw [posterior_real]
  refine ⟨div_pos (mul_pos (mul_pos hm (pow_pos hr.1 _)) (pow_pos hb _)) hn, ?_⟩
  rw [Real.log_div (mul_pos (mul_pos hm (pow_pos hr.1 _)) (pow_pos hb _)).ne' hn.ne',
    Real.log_mul (mul_pos hm (pow_pos hr.1 _)).ne' (pow_pos hb _).ne',
    Real.log_mul hm.ne' (pow_pos hr.1 _).ne', Real.log_pow, Real.log_pow]

private theorem second_summable (ν : PMF Depth) :
    Summable (fun k => (ν k).toReal * (rate k : ℝ) ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
    (fun k => ?_) (pmf_real_summable ν)
  exact mul_le_of_le_one_right ENNReal.toReal_nonneg
    (pow_le_one₀ (rate k).property.1 (rate k).property.2)

private theorem quadratic_expectation (ν : PMF Depth) (l u : ℝ) :
    Summable (fun k => (ν k).toReal * ((rate k : ℝ) - l) * (u - (rate k : ℝ))) ∧
    (∑' k, (ν k).toReal * ((rate k : ℝ) - l) * (u - (rate k : ℝ))) =
      -(∑' k, (ν k).toReal * (rate k : ℝ) ^ 2) +
        (u + l) * (∑' k, (ν k).toReal * (rate k : ℝ)) - u * l := by
  have he : (fun k => (ν k).toReal * ((rate k : ℝ) - l) * (u - (rate k : ℝ))) =
      (fun k => -((ν k).toReal * (rate k : ℝ) ^ 2) +
        (u + l) * ((ν k).toReal * (rate k : ℝ)) - (u * l) * (ν k).toReal) := by
    funext k
    ring
  rw [he]
  have h1 := (second_summable ν).neg
  have h2 := (mean_summable ν).mul_left (u + l)
  have h0 := (pmf_real_summable ν).mul_left (u * l)
  exact ⟨(h1.add h2).sub h0, by
    rw [(h1.add h2).tsum_sub h0, h1.tsum_add h2]
    simp only [tsum_neg, tsum_mul_left, pmf_real_sum, mul_one]⟩

set_option maxHeartbeats 1200000 in
private theorem ordered_counts_unique (μ : PMF Depth) (s t : ActivePhase)
    (H : PhaseHistory s) (G : PhaseHistory t)
    (hA : (readLetters G.val.1).count 0 ≤ (readLetters H.val.1).count 0)
    (h1 : (∑' k, (posterior μ H.val.1 H.val.2 H.property.1 k).toReal * (rate k : ℝ)) =
      ∑' k, (posterior μ G.val.1 G.val.2 G.property.1 k).toReal * (rate k : ℝ))
    (h2 : (∑' k, (posterior μ H.val.1 H.val.2 H.property.1 k).toReal * (rate k : ℝ) ^ 2) =
      ∑' k, (posterior μ G.val.1 G.val.2 G.property.1 k).toReal * (rate k : ℝ) ^ 2) :
    posterior μ H.val.1 H.val.2 H.property.1 =
      posterior μ G.val.1 G.val.2 G.property.1 := by
  classical
  let ν := posterior μ H.val.1 H.val.2 H.property.1
  let ρ := posterior μ G.val.1 G.val.2 G.property.1
  let a : ℝ := ((readLetters H.val.1).count 0 : ℝ)-((readLetters G.val.1).count 0 : ℝ)
  let b : ℝ := ((readLetters H.val.1).count 1 : ℝ)-((readLetters G.val.1).count 1 : ℝ)
  let c : ℝ := Real.log (normalizer μ G.val.1).toReal -
    Real.log (normalizer μ H.val.1).toReal
  have ha : 0 ≤ a := sub_nonneg.mpr (by exact_mod_cast hA)
  have hlog (k : Depth) (hk : μ k ≠ 0) :
      0 < (ν k).toReal ∧ 0 < (ρ k).toReal ∧
      logTilt a b c (rate k) = Real.log (ν k).toReal - Real.log (ρ k).toReal := by
    obtain ⟨hn, hln⟩ := posterior_log μ H.val.1 H.val.2 H.property.1 k hk
    obtain ⟨hr, hlr⟩ := posterior_log μ G.val.1 G.val.2 G.property.1 k hk
    refine ⟨hn, hr, ?_⟩
    rw [hln, hlr]
    dsimp [logTilt, a, b, c]
    ring
  have hzero (k : Depth) (hk : μ k = 0) : (ν k).toReal = 0 ∧ (ρ k).toReal = 0 := by
    simp [ν, ρ, posterior_real, hk]
  by_contra hne
  have hp : ∃ k, (ρ k).toReal < (ν k).toReal := by
    by_contra hh
    push Not at hh
    apply hne
    ext k
    apply (ENNReal.toReal_eq_toReal_iff' (ν.apply_ne_top k) (ρ.apply_ne_top k)).mp
    apply le_antisymm (hh k)
    by_contra hk
    have hi := (pmf_real_summable ν).tsum_lt_tsum hh (lt_of_not_ge hk)
      (pmf_real_summable ρ)
    rw [pmf_real_sum, pmf_real_sum] at hi
    exact (lt_irrefl (1 : ℝ)) hi
  obtain ⟨k₀, hk₀⟩ := hp
  have hμ₀ : μ k₀ ≠ 0 := by
    intro hh
    obtain ⟨hn, hr⟩ := hzero k₀ hh
    rw [hn, hr] at hk₀
    exact lt_irrefl _ hk₀
  have hg₀ : 0 < logTilt a b c (rate k₀) := by
    obtain ⟨hn, hr, he⟩ := hlog k₀ hμ₀
    rw [he]
    exact sub_pos.mpr (Real.log_lt_log hr hk₀)
  obtain ⟨l, u, hsep⟩ := positive_interval_separator a b c ha
    ⟨rate k₀, ratio_interior k₀, hg₀⟩
  let f : Depth → ℝ := fun k => (ν k).toReal * ((rate k : ℝ) - l) * (u - (rate k : ℝ)) -
    (ρ k).toReal * ((rate k : ℝ) - l) * (u - (rate k : ℝ))
  have hf : Summable f := (quadratic_expectation ν l u).1.sub
    (quadratic_expectation ρ l u).1
  have hf0 : ∑' k, f k = 0 := by
    change (∑' k, ((ν k).toReal * ((rate k : ℝ) - l) * (u - (rate k : ℝ)) -
      (ρ k).toReal * ((rate k : ℝ) - l) * (u - (rate k : ℝ)))) = 0
    rw [(quadratic_expectation ν l u).1.tsum_sub (quadratic_expectation ρ l u).1,
      (quadratic_expectation ν l u).2, (quadratic_expectation ρ l u).2, h1, h2]
    ring
  have hnonneg (k : Depth) : 0 ≤ f k := by
    have hsp := hsep (rate k) (ratio_interior k)
    have he : f k = ((ν k).toReal - (ρ k).toReal) * (((rate k : ℝ) - l) * (u - (rate k : ℝ))) := by
      dsimp [f]
      ring
    rw [he]
    by_cases hk : μ k = 0
    · obtain ⟨hn, hr⟩ := hzero k hk
      rw [hn, hr, sub_self, zero_mul]
    · obtain ⟨hn, hr, he⟩ := hlog k hk
      by_cases hg : 0 < logTilt a b c (rate k)
      · apply mul_nonneg _ (hsp.1 hg).le
        apply sub_nonneg.mpr
        exact (Real.log_le_log_iff hr hn).mp (by linarith)
      · apply mul_nonneg_of_nonpos_of_nonpos _ (hsp.2 (le_of_not_gt hg))
        apply sub_nonpos.mpr
        exact (Real.log_le_log_iff hn hr).mp (by linarith)
  have hstrict : 0 < f k₀ := by
    have hsp := (hsep (rate k₀) (ratio_interior k₀)).1 hg₀
    have he : f k₀ = ((ν k₀).toReal - (ρ k₀).toReal)*
        (((rate k₀ : ℝ) - l) * (u - (rate k₀ : ℝ))) := by dsimp [f]; ring
    rw [he]
    exact mul_pos (sub_pos.mpr hk₀) hsp
  have := hf.tsum_pos hnonneg k₀ hstrict
  rw [hf0] at this
  exact lt_irrefl _ this

/-- The same installed prior is essential. Both histories are unrestricted
actual finite acquired histories, possibly in different active phases. -/
theorem same_prior_two_moments_posterior_unique (μ : PMF Depth) (s t : ActivePhase)
    (H : PhaseHistory s) (G : PhaseHistory t)
    (h1 : (∑' k, (posterior μ H.val.1 H.val.2 H.property.1 k).toReal * (rate k : ℝ)) =
      ∑' k, (posterior μ G.val.1 G.val.2 G.property.1 k).toReal * (rate k : ℝ))
    (h2 : (∑' k, (posterior μ H.val.1 H.val.2 H.property.1 k).toReal * (rate k : ℝ) ^ 2) =
      ∑' k, (posterior μ G.val.1 G.val.2 G.property.1 k).toReal * (rate k : ℝ) ^ 2) :
    posterior μ H.val.1 H.val.2 H.property.1 =
      posterior μ G.val.1 G.val.2 G.property.1 := by
  rcases le_total ((readLetters G.val.1).count 0) ((readLetters H.val.1).count 0) with h | h
  · exact ordered_counts_unique μ s t H G h h1 h2
  · exact (ordered_counts_unique μ t s G H h h1.symm h2.symm).symm

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeTwoMomentRecovery
