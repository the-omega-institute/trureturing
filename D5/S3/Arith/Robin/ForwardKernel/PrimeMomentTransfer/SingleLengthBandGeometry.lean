/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthBandGeometry
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthBandGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Floors of polynomial bands preserve single-length ranges and logarithmic bounds. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.RealLengthRescaling
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SingleLengthMSDefs
import D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FourthMomentAsymptotic

/-! Integer cutoffs and lengths preserve the range of the single-length moment theorem. -/

open Set Filter
open scoped Topology

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

/-- A strict exponent margin absorbs flooring the base of a nonnegative real power. -/
theorem floor_power_upper (β q : ℝ) (hβq : β < q) (hq : 0 ≤ q) :
    ∀ᶠ Y : ℝ in atTop, Y ^ β ≤ (⌊Y⌋₊ : ℝ) ^ q := by
  have hs := (tendsto_rpow_neg_atTop (sub_pos.mpr hβq)).eventually_le_const
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-q))
  filter_upwards [hs, eventually_ge_atTop (1 : ℝ)] with Y hs hY
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  calc
    Y ^ β = Y ^ q * Y ^ (-(q - β)) := by
      rw [← Real.rpow_add hY0]; congr 1; ring
    _ ≤ Y ^ q * (2 : ℝ) ^ (-q) := by gcongr
    _ = (Y / 2) ^ q := by
      rw [Real.div_rpow hY0.le (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      rfl
    _ ≤ (⌊Y⌋₊ : ℝ) ^ q :=
      Real.rpow_le_rpow (by positivity) (Nat.div_two_lt_floor hY).le hq

/-- Both natural floors satisfy the uniform range for the single-length moment theorem. -/
theorem band_geometry (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 4) :
    ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ, Y ^ α ≤ v → v ≤ Y ^ β →
      let N := ⌊Y⌋₊
      let K := ⌊v⌋₊
      2 ≤ N ∧ 1 ≤ K ∧ (Y / 2 ≤ (N : ℝ)) ∧ (v / 2 ≤ (K : ℝ)) ∧
        Y ^ (α / 2) ≤ (K : ℝ) ∧ (K : ℝ) ≤ Y ^ β ∧
        polynomialLengthFamily β 2 N K ∧ Real.log (N : ℝ) ≤ (K : ℝ) ∧
        (K : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
  have hβ1 : β < 1 := hβ.trans (by norm_num)
  have hβ0 : 0 ≤ β := (hα.trans hαβ).le
  have hlog := (isLittleO_log_rpow_atTop (half_pos hα)).tendsto_div_nhds_zero
  filter_upwards [floor_range α β hα hαβ hβ1,
    range_geometry α β 1 hα hβ1 zero_lt_one, floor_power_upper β (1 / 4) hβ (by norm_num),
    hlog.eventually_le_const zero_lt_one, eventually_ge_atTop (2 : ℝ)]
    with Y hfloor hgeom hquarter hlog hY v hvα hvβ
  obtain ⟨hK, hKpow, hKhi, _, _⟩ := hfloor v hvα hvβ
  obtain ⟨hv2, _, _⟩ := hgeom.2.2 v hvα hvβ
  have hY0 : 0 < Y := by positivity
  have hN : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by simpa using hY)
  have hN0 : 0 < (⌊Y⌋₊ : ℝ) := by exact_mod_cast (zero_lt_two.trans_le hN)
  have hNhalf : Y / 2 ≤ (⌊Y⌋₊ : ℝ) := (Nat.div_two_lt_floor (by linarith : 1 ≤ Y)).le
  have hY2N : Y ≤ 2 * (⌊Y⌋₊ : ℝ) := by linarith only [hNhalf]
  have htwo : (2 : ℝ) ^ β ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hβ1.le
  have hfamily : polynomialLengthFamily β 2 ⌊Y⌋₊ ⌊v⌋₊ := by
    change (⌊v⌋₊ : ℝ) ≤ 2 * (⌊Y⌋₊ : ℝ) ^ β
    calc
      _ ≤ Y ^ β := hKhi
      _ ≤ (2 * (⌊Y⌋₊ : ℝ)) ^ β := Real.rpow_le_rpow hY0.le hY2N hβ0
      _ = (2 : ℝ) ^ β * (⌊Y⌋₊ : ℝ) ^ β :=
        Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
      _ ≤ 2 * (⌊Y⌋₊ : ℝ) ^ β := by gcongr
  have hlogpow : Real.log Y ≤ Y ^ (α / 2) :=
    (div_le_one (Real.rpow_pos_of_pos hY0 _)).mp hlog
  have hlogN : Real.log (⌊Y⌋₊ : ℝ) ≤ (⌊v⌋₊ : ℝ) :=
    (Real.log_le_log hN0 (Nat.floor_le hY0.le)).trans (hlogpow.trans hKpow)
  exact ⟨hN, hK, hNhalf, (Nat.div_two_lt_floor (by linarith : 1 ≤ v)).le,
    hKpow, hKhi, hfamily, hlogN, hKhi.trans hquarter⟩

/-- The logarithmic normalizer is positive and uniformly comparable to the cutoff logarithm. -/
theorem band_log (β Y v : ℝ) (hβ : β < 1) (hY : 1 < Y) (hv : 1 ≤ v)
    (hvβ : v ≤ Y ^ β) :
    0 < Real.log (Y / v) ∧
      (1 - β) * Real.log Y ≤ Real.log (Y / v) ∧ Real.log (Y / v) ≤ Real.log Y := by
  have hY0 : 0 < Y := zero_lt_one.trans hY
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hlower := FourthTransfer.FourthMomentAsymptotic.band_log_lower hY0 hv0 hvβ
  have hpos : 0 < (1 - β) * Real.log Y := mul_pos (sub_pos.mpr hβ) (Real.log_pos hY)
  refine ⟨hpos.trans_le hlower, hlower, ?_⟩
  rw [Real.log_div hY0.ne' hv0.ne']
  exact sub_le_self _ (Real.log_nonneg hv)

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
