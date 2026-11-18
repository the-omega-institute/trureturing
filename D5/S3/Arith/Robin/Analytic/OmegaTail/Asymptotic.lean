/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/Asymptotic
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/Asymptotic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Matching lower bounds and the two-sided exponential rate of the large distinct-prime tail. -/

import D5.S3.Arith.Robin.Analytic.OmegaTail.Counting
import D5.S3.Arith.Robin.Analytic.OmegaTail.Saddle
import D5.S3.Arith.Robin.Analytic.OmegaTail.Truncation
import D5.S3.Arith.Robin.Analytic.OmegaTail.Binning

/-! admission_basis: open-problem-resolution (preregistration #31303). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Set MeasureTheory Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaTail.Asymptotic
open D5.S3.Arith.Robin.Analytic.OmegaTailUpper

private lemma parameter_lower {s epsilon : ℝ} (hs : saddle < s) (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop, H s - epsilon ≤ log (tailCount 0 x : ℝ) / scale x := by
  have hs1 : 1 < s := saddle_characterization.1.1.trans hs
  have hm : m s < 0 := m_neg_of_saddle_lt hs
  let e : ℝ := min (-m s / 4) (epsilon / 4)
  have he : 0 < e := lt_min (by linarith) (by positivity)
  obtain ⟨A, B, g, hA, hAB, hg, h01, hmass, hmoment, hentropy⟩ :=
    Truncation.compact_profile hs1 he
  have hmoment' : |(∫ u in Ioc A B, g u * log u) - m s| < e := by
    simpa only [m, cot_eq_cos_div_sin, mul_div_assoc] using hmoment
  have hentropy' : H s - e < ∫ u in Ioc A B, binEntropy (g u) := by
    simpa only [H, cot_eq_cos_div_sin, mul_div_assoc] using hentropy
  obtain ⟨n, hn, a, b, r, hbins, hdisj, hsum, hE, hJ⟩ :=
    Binning.compact_bins hA hAB hg h01 (show 0 < -m s / 4 by linarith)
  have hslack : 0 + ∑ j, r j * log (b j) < 0 := by
    rw [hmass] at hJ
    have hJe := (abs_lt.mp hmoment').2
    have he_le : e ≤ -m s / 4 := min_le_left _ _
    linarith
  have hsum' : ∑ j, r j = 1 := hsum.trans hmass
  have hlow := Counting.finite_box_lower (⟨0, hn⟩ : Fin n) a b r 0
    (fun j => (hbins j).1) (fun j => (hbins j).2.1) hdisj
    (fun j => (hbins j).2.2.1) (fun j => (hbins j).2.2.2) hsum' hslack
    (show 0 < epsilon / 2 by positivity)
  filter_upwards [hlow] with x hx
  have he_le : e ≤ epsilon / 4 := min_le_right _ _
  linarith

/-- The matching lower exponent, in the eventual form equivalent to the liminf bound. -/
private theorem lower_bound {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop, C0 - epsilon ≤ log (tailCount 0 x : ℝ) / scale x := by
  have hc := H_continuousAt saddle_characterization.1.1
  obtain ⟨delta, hdelta, hnear⟩ := Metric.continuousAt_iff.mp hc
    (epsilon / 4) (by positivity)
  let s : ℝ := saddle + delta / 2
  have hs : saddle < s := by dsimp [s]; linarith
  have hsd : dist s saddle < delta := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hs)]
    dsimp [s]
    linarith
  have hH := hnear hsd
  rw [Real.dist_eq, ← saddle_characterization.2.2.2.2.2] at hH
  have hlow := parameter_lower hs (show 0 < epsilon / 2 by positivity)
  filter_upwards [hlow] with x hx
  have hclose := (abs_lt.mp hH).1
  linarith

/-- The exact exponential counting rate for integers with more than
log(x)/log(log(x)) distinct prime factors. -/
theorem result :
    Tendsto (fun x : ℝ => log (tailCount 0 x : ℝ) / scale x) atTop (𝓝 C0) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hs1 := saddle_characterization.1.1
  have hrate := saddle_characterization.2.2.2.2.1
  filter_upwards [lower_bound (show 0 < epsilon / 2 by positivity),
    lower_bound (by norm_num : (0 : ℝ) < 1 / 2),
    upper_bound 0 (by norm_num) hs1 (show 0 < epsilon / 2 by positivity),
    eventually_gt_atTop (exp 1)] with x hlo hpositive hup hx
  have hy : 0 < scale x := scale_pos hx
  have hn : 0 < (tailCount 0 x : ℝ) := by
    by_contra h
    have hz : (tailCount 0 x : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
    rw [hz, log_zero, zero_div] at hpositive
    linarith [constant_gt_one]
  have hlog := log_le_log hn hup
  rw [log_exp, ← hrate] at hlog
  have hhi : log (tailCount 0 x : ℝ) / scale x ≤ C0 + epsilon / 2 :=
    (div_le_iff₀ hy).mpr hlog
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end D5.S3.Arith.Robin.Analytic.OmegaTail.Asymptotic
