/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ShortGapTenThirds
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ShortGapTenThirds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Negative mixed derivative of the original refined BMV kernel on the wider short-gap strip. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactGap
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapImprovedSlope
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapTenThirdsNormalization
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapTenThirdsRadical
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapTenThirdsSign

open Filter
open scoped BigOperators Topology

namespace RefinedBMV.PositiveCenter.CompactGap

open private rate c W X rate_pos gap_pos W_pos
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactGapIdentities

/-- The mixed derivative is negative at every positive gap through two from lower coordinate ten thirds. -/
theorem logKernel_shortGap_mixed_from_ten_thirds {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 10 / 3 ≤ u) (huv : u < v) (hdmax : v - u ≤ 2) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  let h := rate p
  let d := v - u
  let Z : ℝ → ℝ := fun t ↦ Real.sqrt (X h t)
  let P : ℝ → ℝ := fun t ↦ upperTailGap h t / Real.sqrt (W h t)
  let V : ℝ → ℝ := fun t ↦ 1 / Real.sqrt (W h t)
  let α : ℝ → ℝ := fun t ↦ deriv P t / P t
  let β : ℝ → ℝ := fun t ↦ deriv V t / V t
  let J := RefinedBMV.PositiveCenter.shortGapJ p
  have hp₀ : 0 < p := by omega
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp₀
  have hh := rate_pos hp₀
  have hreal : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hhp : h ≤ 3 / 11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hreal
  have hu₀ : 0 < u := by linarith
  have hv₀ := hu₀.trans huv
  have hv := hu.trans huv.le
  have hd : 0 < d := sub_pos.mpr huv
  have hU := shortGapNormalization_bounds_of_ten_thirds_le hp hu
  have hV := shortGapNormalization_bounds_of_ten_thirds_le hp hv
  have hα : 0 ≤ α u := hU.1.le
  have hβ : β v ≤ 0 := (hV.2.2.2.2.1.trans_lt hV.2.2.2.2.2).le
  have hαu : α u ≤ 1 / (2 * u) := hU.2.1.trans hU.2.2.1
  have hαv : α v ≤ 1 / (2 * v) := hV.2.1.trans hV.2.2.1
  have hαβ : α u - β v ≤ 1 / 2 :=
    shortGapNormalization_slopeDifference_le_half_of_ten_thirds_le hp hu huv
  have hαsmall : α u ≤ 3 / 20 := hαu.trans (by
    apply (div_le_iff₀ (show 0 < 2 * u by positivity)).mpr
    linarith only [hu])
  have hq := shortGapQuotient_weighted_pos_from_ten_thirds hh hhp hu hα hαsmall
  have hg : (β v - (3 / 2 + h)) * Real.exp (-(3 / 2 + h) * d) *
      (deriv (shortGapQuotient h) u + (α u + (3 / 2 + h)) * shortGapQuotient h u) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hβ, hh]) (Real.exp_pos _).le) hq.le
  have hJloc : shortGapJ h =ᶠ[𝓝 d] J := by
    filter_upwards [eventually_gt_nhds hd] with t ht
    unfold J
    rw [shortGapJ_eq_sqrt hp₀ ht]
    have hj : 0 ≤ shortGapJ h t :=
      div_nonneg (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)) (gap_pos hp₀ ht).le
    have hsq : shortGapJ h t ^ 2 = c h * Real.exp t * compositionMoment p 0 t :=
      shortGapJ_sq hp₀ ht
    change shortGapJ h t = Real.sqrt (c h * Real.exp t * compositionMoment p 0 t)
    rw [← hsq, Real.sqrt_sq hj]
  obtain ⟨hD, hH⟩ := shortGap_profile_signs hp
  have hcancel : h * (p : ℝ) = 3 := div_mul_cancel₀ 3 hpR.ne'
  have hprofile := shortGapProfile_of_signs hh hcancel (shortGapProfileU_contDiff p)
    (shortGapProfileU_pos hp₀) (J := J) rfl (shortGapJ_deriv_pos hp₀ (by norm_num)) hD hH
  have he : shortGapF h =ᶠ[𝓝 d] fun t ↦ shortGapProfileT p h t - J t := by
    filter_upwards [eventually_gt_nhds hd, hJloc] with t ht hj
    unfold shortGapF shortGapProfileT
    rw [show Real.exp (3 * t / 2) * (1 - Real.exp (-((3 + h) * t))) / upperTailGap h t =
      h * ∑ l ∈ Finset.range (p + 1), Real.exp ((h * l - 3 / 2) * t) from
        shortGap_geometric_eq hp₀ ht, hj, show -((3 / 2 + h) * t) = -(3 / 2 + h) * t by ring]
  have hs := hprofile d ⟨hd.le, hdmax⟩
  have hf' : deriv (shortGapF h) d ≤ 0 := (he.deriv_eq.trans_lt hs.2).le
  have hf'' : 1 / 200 < deriv (deriv (shortGapF h)) d :=
    hs.1.trans_eq he.deriv.deriv_eq.symm
  have hfd : (α u - β v) * deriv (shortGapF h) d ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hβ.trans hα)) hf'
  have hJ' : 0 ≤ deriv (shortGapJ h) d := by
    rw [hJloc.deriv_eq]
    exact (shortGapJ_deriv_pos hp₀ hd.le).le
  have hJ'' : deriv (shortGapJ h) d / 2 ≤ deriv (deriv (shortGapJ h)) d := by
    rw [hJloc.deriv_eq, hJloc.deriv.deriv_eq]
    exact shortGapJ_deriv_half_le_second hp₀ hd.le
  have hZ' : 0 ≤ deriv Z v :=
    (middleGap_marginal_bounds hh hhp (show 2 ≤ v by linarith)).2.2.1
  have hcor := shortGap_correction_lt_from_ten_thirds (h := h)
    (jd := deriv J d) hh hhp hu huv hdmax (shortGapJ_deriv_le hp hd.le)
    (shortGapJ_deriv_le_from_one hp) hαu hαv
  have hcrit : deriv Z v * deriv (shortGapJ h) d ≤
      (c h * upperTailGap h v * Real.exp (-((u + v) / 2))) * (1 / 2 - α u) * (1 / 2 - α v) := by
    rw [hJloc.deriv_eq]
    exact hcor.le
  have hm := logKernel_gap_mixed_of_profile_margin_of_slopes (ε := (1 / 200 : ℝ)) hp hu₀ huv
    hα hβ hαβ (shortGapF_pos hp₀ hd).le (by linarith only [hf'', hfd, hg]) hJ' hJ'' hZ' hcrit
  exact hm.trans_le (neg_nonpos.mpr
    (mul_nonneg (mul_nonneg (div_nonneg (gap_pos hp₀ hu₀).le (Real.sqrt_nonneg _))
      (one_div_nonneg.mpr (Real.sqrt_nonneg _))) (by norm_num)))

/--
info: 'RefinedBMV.PositiveCenter.CompactGap.logKernel_shortGap_mixed_from_ten_thirds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms logKernel_shortGap_mixed_from_ten_thirds

end RefinedBMV.PositiveCenter.CompactGap
