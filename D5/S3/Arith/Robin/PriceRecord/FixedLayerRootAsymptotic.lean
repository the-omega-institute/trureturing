/- GID: D5/S3/Arith/Robin/PriceRecord/FixedLayerRootAsymptotic
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/FixedLayerRootAsymptotic
   mirror-E: none(waiver:elementary-asymptotic-analysis)
   anchors: []
   utility: none
   digest: The actual fixed-layer cutoff has limiting logarithmic offset log j. -/
import D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
import D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! UNCOMPILED_UNACCEPTED. Consumes the completed cutoff and slope SOURCES,
not an admitted/native supplier. The relative gain is proved, not inferred from
the factor-two root bounds. The natural index j is fixed before every limit. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic
open Real Filter Finset
open scoped Topology
open D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask

private theorem normalized_powerSum_tendsto {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun u : ℝ => powerSum j u / u ^ j) atTop (𝓝 1) := by
  have hpow : Tendsto (fun u : ℝ => u ^ j) atTop atTop :=
    tendsto_pow_atTop (by omega : j ≠ 0)
  have hi : Tendsto (fun u : ℝ => 1 / u ^ j) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpow
  have hu : Tendsto (fun u : ℝ => 1 / u) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hh := ((tendsto_const_nhds (x := (1 : ℝ))).sub hi).div
    (tendsto_const_nhds.sub hu) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  simp only [sub_zero, div_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
  have hg := powerSum_geometric j u
  have up : u ^ j ≠ 0 := (pow_pos (by linarith : 0 < u) j).ne'
  have hd : 1 - 1 / u ≠ 0 := by
    have := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hu
    norm_num only [one_div_one] at this
    simpa only [one_div] using (sub_pos.mpr this).ne'
  change (1 - 1 / u ^ j) / (1 - 1 / u) = powerSum j u / u ^ j
  apply (div_eq_div_iff hd up).mpr
  field_simp [show u ≠ 0 by linarith]
  nlinarith only [hg]

private theorem relative_gain_tendsto {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun u : ℝ => gain j u * u ^ j) atTop (𝓝 1) := by
  have hi : Tendsto (fun u : ℝ => 1 / u ^ j) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega : j ≠ 0))
  have hl := ((tendsto_const_nhds (x := (1 : ℝ))).div
    ((normalized_powerSum_tendsto hj).add hi) (by norm_num : (1 : ℝ) + 0 ≠ 0))
  simp only [add_zero, div_one] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with u hu
    have hu0 : 0 < u := by linarith
    have hs := powerSum_pos hu0 hj
    have hp := pow_pos hu0 j
    have hlog := one_sub_inv_le_log_of_pos (show 0 < 1 + 1 / powerSum j u by positivity)
    have hlow : 1 / (powerSum j u + 1) ≤ gain j u := by
      have he : 1 - (1 + 1 / powerSum j u)⁻¹ = 1 / (powerSum j u + 1) := by
        field_simp [hs.ne', (by positivity : powerSum j u + 1 ≠ 0)] <;> ring
      simpa only [he, gain] using hlog
    have hh := mul_le_mul_of_nonneg_right hlow hp.le
    change 1 / (powerSum j u / u ^ j + 1 / u ^ j) ≤ _
    rw [← add_div, one_div_div]
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hh
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with u hu
    have hp := pow_pos (by linarith : 0 < u) j
    have hh := mul_le_mul_of_nonneg_right (gain_le_inv_pow (by linarith : 0 < u) hj) hp.le
    simpa only [one_div_mul_cancel hp.ne'] using hh

/- Relative marginal at each fixed multiplicative point. This is the actual
real beta, so it also identifies the moving cutoff rather than a proxy root. -/
private theorem scaled_beta_tendsto {j : ℕ} (hj : 1 ≤ j) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => beta j (c * t) / referencePrice (t ^ j))
      atTop (𝓝 ((j : ℝ) / c ^ j)) := by
  have hcT : Tendsto (fun t : ℝ => c * t) atTop atTop :=
    tendsto_id.const_mul_atTop hc
  have hgain := (relative_gain_tendsto hj).comp hcT
  have hz : Tendsto (fun t : ℝ => log c / log t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_atTop
  have hratio : Tendsto (fun t : ℝ => log t / log (c * t)) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds.add hz).inv₀ (by norm_num : (1 : ℝ) + 0 ≠ 0)
    simp only [add_zero, inv_one] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ), hcT.eventually_gt_atTop 1] with t ht hct
    rw [log_mul hc.ne' (by linarith : t ≠ 0)]
    have hd : log c + log t ≠ 0 := by
      rw [← log_mul hc.ne' (by linarith : t ≠ 0)]
      exact (log_pos hct).ne'
    field_simp [(log_pos ht).ne', hd] <;> ring <;> field_simp [hd] <;> ring
  have h := hgain.mul (hratio.const_mul ((j : ℝ) / c ^ j))
  simp only [mul_one, one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ), hcT.eventually_gt_atTop 1] with t ht hct
  dsimp only [Function.comp_def]
  unfold beta referencePrice
  rw [log_pow, mul_pow]
  field_simp [hc.ne', (by linarith : t ≠ 0), (log_pos ht).ne', (log_pos hct).ne']
  <;> ring

/-- Exact fixed-j logarithmic offset of the supplied actual beta cutoff.
The statement is for all real X tending to infinity, not just natural powers. -/
theorem fixed_layer_root_offset_tendsto {j : ℕ} (hj : 2 ≤ j) :
    Tendsto (fun X : ℝ => (j : ℝ) * log (cutoff j (referencePrice X)) - log X)
      atTop (𝓝 (log (j : ℝ))) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hj1 : 1 ≤ j := by omega
  have htlim : Tendsto (fun t : ℝ =>
      (j : ℝ) * log (cutoff j (referencePrice (t ^ j))) - log (t ^ j))
      atTop (𝓝 (log (j : ℝ))) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let a := exp ((log (j : ℝ) - ε / 2) / j)
    let b := exp ((log (j : ℝ) + ε / 2) / j)
    have ha : 0 < a := exp_pos _
    have hb : 0 < b := exp_pos _
    have hap : a ^ j = (j : ℝ) * exp (-ε / 2) := by
      dsimp [a]
      rw [← exp_nat_mul]
      have he : (j : ℝ) * ((log (j : ℝ) - ε / 2) / j) = log (j : ℝ) + -ε / 2 := by
        field_simp [hj0.ne'] <;> ring
      rw [he, exp_add, exp_log hj0]
    have hbp : b ^ j = (j : ℝ) * exp (ε / 2) := by
      dsimp [b]
      rw [← exp_nat_mul]
      have he : (j : ℝ) * ((log (j : ℝ) + ε / 2) / j) = log (j : ℝ) + ε / 2 := by
        field_simp [hj0.ne'] <;> ring
      rw [he, exp_add, exp_log hj0]
    have hla : 1 < (j : ℝ) / a ^ j := by
      rw [hap]
      apply (lt_div_iff₀ (mul_pos hj0 (exp_pos _))).mpr
      have he : exp (-ε / 2) < 1 := by rw [exp_lt_one_iff]; linarith
      nlinarith
    have hlb : (j : ℝ) / b ^ j < 1 := by
      rw [hbp]
      apply (div_lt_iff₀ (mul_pos hj0 (exp_pos _))).mpr
      have he : 1 < exp (ε / 2) := by rw [one_lt_exp_iff]; linarith
      nlinarith
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      (tendsto_id.const_mul_atTop ha).eventually_ge_atTop 2,
      (tendsto_id.const_mul_atTop hb).eventually_ge_atTop 2,
      (scaled_beta_tendsto hj1 ha).eventually (eventually_gt_nhds hla),
      (scaled_beta_tendsto hj1 hb).eventually (eventually_lt_nhds hlb)]
      with t ht hat hbt hla hlb
    simp only [id_eq] at hat hbt
    have hX : 1 < t ^ j := one_lt_pow₀ ht (by omega : j ≠ 0)
    have hLambda : 0 < referencePrice (t ^ j) := by
      dsimp [referencePrice]
      exact one_div_pos.mpr (mul_pos (by linarith) (log_pos hX))
    have hlow : a * t < cutoff j (referencePrice (t ^ j)) :=
      (cutoff_occupancy hj hLambda hat).mp (by
        simpa only [one_mul, id_eq] using (lt_div_iff₀ hLambda).mp hla)
    have hhigh : cutoff j (referencePrice (t ^ j)) ≤ b * t := by
      by_contra! hn
      have hh := (cutoff_occupancy hj hLambda hbt).mpr hn
      have hu := (div_lt_iff₀ hLambda).mp hlb
      simp only [one_mul, id_eq] at hh hu
      exact (hu.trans hh).false
    have hloglo := log_lt_log (mul_pos ha (by linarith : 0 < t)) hlow
    have hloghi := log_le_log ((mul_pos ha (by linarith : 0 < t)).trans hlow) hhigh
    have hloga : (j : ℝ) * log (a * t) - log (t ^ j) = log (j : ℝ) - ε / 2 := by
      rw [log_mul ha.ne' (by linarith : t ≠ 0), log_pow]
      dsimp [a]
      rw [log_exp]
      field_simp [hj0.ne'] <;> ring
    have hlogb : (j : ℝ) * log (b * t) - log (t ^ j) = log (j : ℝ) + ε / 2 := by
      rw [log_mul hb.ne' (by linarith : t ≠ 0), log_pow]
      dsimp [b]
      rw [log_exp]
      field_simp [hj0.ne'] <;> ring
    have hloglo' := mul_lt_mul_of_pos_left hloglo hj0
    have hloghi' := mul_le_mul_of_nonneg_left hloghi hj0.le
    rw [dist_eq]
    apply abs_lt.mpr
    constructor <;> linarith only [hloglo', hloghi', hloga, hlogb, hε]
  have hroot := tendsto_rpow_atTop (inv_pos.mpr hj0)
  have h := htlim.comp hroot
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  simp only [Function.comp_def, rpow_inv_natCast_pow hX.le (by omega : j ≠ 0)]

#print axioms fixed_layer_root_offset_tendsto
end D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic
