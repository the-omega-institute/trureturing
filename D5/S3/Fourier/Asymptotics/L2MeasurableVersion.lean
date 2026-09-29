/- GID: D5/S3/Fourier/Asymptotics/L2MeasurableVersion
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/L2MeasurableVersion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A Lipschitz L2 curve has a jointly measurable fixed-time modification. -/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Analysis.SpecificLimits.Normed

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace D5.S3.Fourier.Asymptotics.L2MeasurableVersion

/-- A dyadic representative limit gives joint measurability and equality almost
surely at each fixed time, for an arbitrary measure. -/
theorem result {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : ℝ → Lp ℝ 2 P) {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∃ X : ℝ → Ω → ℝ, Measurable (Function.uncurry X) ∧
      ∀ t, X t =ᵐ[P] (fun z => f t z) := by
  classical
  let grid : ℕ → ℝ → ℝ := fun n t => (⌊(2 : ℝ) ^ n * t⌋ : ℝ) / (2 : ℝ) ^ n
  let Xn : ℕ → ℝ × Ω → ℝ := fun n p => f (grid n p.1) p.2
  have hgrid (n : ℕ) (t : ℝ) : ‖grid n t - t‖ ≤ (1 / 2 : ℝ) ^ n := by
    have hp : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
    have hle : grid n t ≤ t := by
      dsimp only [grid]
      apply (div_le_iff₀ hp).mpr
      simpa only [mul_comm] using Int.floor_le ((2 : ℝ) ^ n * t)
    have hlo : t - 1 / (2 : ℝ) ^ n ≤ grid n t := by
      dsimp only [grid]
      apply (le_div_iff₀ hp).mpr
      rw [sub_mul, one_div_mul_cancel hp.ne']
      have H := (Int.sub_one_lt_floor ((2 : ℝ) ^ n * t)).le
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hle), one_div_pow]
    linarith
  have hmeas (n : ℕ) : Measurable (Xn n) := by
    have H : Measurable (fun p : ℤ × Ω => f ((p.1 : ℝ) / (2 : ℝ) ^ n) p.2) :=
      measurable_from_prod_countable_right
        (fun k => (Lp.stronglyMeasurable (f ((k : ℝ) / (2 : ℝ) ^ n))).measurable)
    exact H.comp (((measurable_const.mul measurable_fst).floor).prodMk measurable_snd)
  let X : ℝ → Ω → ℝ := fun t z => limUnder atTop (fun n => Xn n (t,z))
  refine ⟨X, (StronglyMeasurable.limUnder (fun n => (hmeas n).stronglyMeasurable)).measurable, ?_⟩
  intro t
  have hsum : Summable (fun n => ‖f (grid n t) - f t‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1)).mul_left (K : ℝ))
    intro n
    have H : ‖f (grid n t) - f t‖ ≤ (K : ℝ) * ‖grid n t - t‖ := by
      simpa only [dist_eq_norm] using hf.dist_le_mul (grid n t) t
    exact H.trans (mul_le_mul_of_nonneg_left (hgrid n t) K.coe_nonneg)
  have herror : ∑' n, eLpNorm (fun z => Xn n (t,z) - f t z) 2 P ≠ ∞ := by
    have H := tsum_enorm_ne_top_iff_summable_norm.mpr hsum
    convert H using 1
    congr 1
    funext n
    rw [Lp.enorm_def]
    exact (eLpNorm_congr_ae (Lp.coeFn_sub (f (grid n t)) (f t))).symm
  have hconv := summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (fun n => ((Lp.aestronglyMeasurable (f (grid n t))).sub (Lp.aestronglyMeasurable (f t))))
    herror
  filter_upwards [hconv] with z hz
  have H : Tendsto (fun n => Xn n (t,z) - f t z) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hz.tendsto_atTop_zero
  have H' : Tendsto (fun n => Xn n (t,z)) atTop (𝓝 (f t z)) :=
    (tendsto_sub_nhds_zero_iff).mp H
  exact H'.limUnder_eq


#print axioms result

end D5.S3.Fourier.Asymptotics.L2MeasurableVersion
