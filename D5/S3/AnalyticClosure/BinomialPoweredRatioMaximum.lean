/- GID: D5/S3/AnalyticClosure/BinomialPoweredRatioMaximum
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/BinomialPoweredRatioMaximum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian asymptotic of the actual powered binomial ratio maximum. -/

import D5.S3.AnalyticClosure.BinomialPoweredRatioLocalization
import D5.S3.AnalyticClosure.BinomialUniformMaximum
import D5.S3.AnalyticClosure.BinomialPowerNormalization

open Filter Real Finset
open scoped Topology
open D5.S3.AnalyticClosure.BinomialLocalGaussian
open D5.S3.AnalyticClosure.BinomialMaximumLocalization
open D5.S3.AnalyticClosure.BinomialPoweredRatioLocalization

namespace D5.S3.AnalyticClosure.BinomialPoweredRatioMaximum

/-- The finite maximum includes both endpoints and permits ties. -/
noncomputable def maximumValue (a : ℝ) (l m : ℕ) : ℝ := by
  classical
  exact ((range (m + 1)).image (poweredRatio a l m)).max'
    ((show (range (m + 1)).Nonempty from ⟨0, by simp⟩).image _)

/-- The powered-sum maximum with the exact constant of equation (1.4) in
Byun--Poznanovic, arXiv:2604.14639v1, Conjecture 1.1(d).
All subtractions in real exponents are in `ℝ`, including when `l = 1`.
No exact-peak, uniqueness, or unimodality assumption is used. -/
theorem maximum_asymptotic (a : ℝ) (ha : 0 < a) (l : ℕ) (hl : 0 < l) :
    Tendsto (fun m : ℕ => maximumValue a l m /
      (sqrt (l : ℝ) / sqrt (2 * π * m) *
        (sqrt (1 + 2 * a) * (1 + a) * a ^ (((l : ℝ) - 2) / 2) /
          ((1 + a) ^ l - 1)) *
        ((1 + 2 * a) / (1 + a)) ^ (((m : ℝ) + 1 / 2) * (l : ℝ))))
      atTop (𝓝 1) := by
  classical
  let q := a / (1 + 2 * a)
  let p := a / (1 + a)
  let B := (1 + 2 * a) / (1 + a)
  let L := (1 - ((1 + a)⁻¹) ^ l)⁻¹
  let t := (1 - (l : ℝ)) / 2
  let Z (x : ℝ) := (2 * π * x * p * (1 - p)) ^ t / sqrt l
  let S (j : ℕ) := ∑ i ∈ range (j + 1), binomialMass p j i ^ l
  let H (m : ℕ) := sqrt (2 * π * m * q * (1 - q)) ^ l
  let K (m : ℕ) := H m * Z ((m : ℝ) * q) / B ^ (m * l)
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by dsimp [q]; apply (div_lt_one (by positivity)).2; linarith
  have hp : 0 < p := by dsimp [p]; positivity
  have hp1 : p < 1 := by dsimp [p]; apply (div_lt_one (by positivity)).2; linarith
  have hb : 0 < 1 + a := by positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hsqrtl : 0 < sqrt (l : ℝ) := sqrt_pos.mpr hlR
  have hZ (x : ℝ) (hx : 0 < x) : 0 < Z x := by dsimp [Z]; positivity
  have hK (m : ℕ) : 0 ≤ K m := by dsimp [K, H, Z]; positivity
  have hS (j : ℕ) : 0 < S j := by
    apply sum_pos'
    · intro i _; unfold binomialMass; positivity
    · refine ⟨0, by simp, ?_⟩
      simp only [binomialMass, Nat.choose_zero_right, Nat.cast_one, pow_zero,
        mul_one, one_mul, Nat.sub_zero]
      positivity
  have hden (j : ℕ) : S j =
      (∑ i ∈ range (j + 1), ((j.choose i : ℝ) * a ^ i) ^ l) / (1 + a) ^ (j * l) := by
    rw [sum_div]
    apply sum_congr rfl
    intro i hi
    have hij : i ≤ j := Nat.le_of_lt_succ (mem_range.mp hi)
    have hcomp : 1 - p = 1 / (1 + a) := by dsimp [p]; field_simp; ring
    have hmass : binomialMass p j i = (j.choose i : ℝ) * a ^ i / (1 + a) ^ j := by
      rw [binomialMass, hcomp]
      dsimp [p]
      rw [div_pow, div_pow, one_pow]
      have hadd : (1 + a) ^ j = (1 + a) ^ i * (1 + a) ^ (j - i) := by
        rw [← pow_add, Nat.add_sub_of_le hij]
      rw [hadd]
      field_simp
    change binomialMass p j i ^ l = _
    rw [hmass, div_pow, ← pow_mul]
  have hidentity (m j : ℕ) : poweredRatio a l m j = prefixValue a l m j / S j := by
    rw [hden]
    dsimp [poweredRatio, prefixValue]
    have hn : (1 + a) ^ (j * l) ≠ 0 := (pow_pos hb _).ne'
    field_simp
  have hm : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpath (s : ℕ → ℕ)
      (hs : Tendsto (fun m : ℕ => (s m : ℝ) / m) atTop (𝓝 q)) :
      Tendsto (fun m : ℕ => S (s m) / Z ((m : ℝ) * q)) atTop (𝓝 1) := by
    have hsreal : Tendsto (fun m : ℕ => (s m : ℝ)) atTop atTop := by
      apply (hm.atTop_mul_pos hq hs).congr'
      filter_upwards [eventually_gt_atTop 0] with m hm0
      have hn : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
      exact mul_div_cancel₀ (s m : ℝ) hn
    have hsnat : Tendsto s atTop atTop := tendsto_natCast_atTop_iff.mp hsreal
    have hn := (BinomialPowerNormalization.binomial_power_normalization p hp hp1 l hl).comp hsnat
    change Tendsto (fun m : ℕ => S (s m) / Z (s m)) atTop (𝓝 1) at hn
    have hz : Tendsto (fun m : ℕ => Z (s m) / Z ((m : ℝ) * q)) atTop (𝓝 1) := by
      have ht := (hs.div_const q).rpow_const (p := t) (Or.inl (div_self hq.ne' ▸ one_ne_zero))
      rw [div_self hq.ne', one_rpow] at ht
      apply ht.congr'
      filter_upwards [eventually_gt_atTop 0] with m hm0
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
      have hc : 0 < 2 * π * ((m : ℝ) * q) * p * (1 - p) := by positivity
      have hbase : ((s m : ℝ) / m) / q =
          (2 * π * (s m : ℝ) * p * (1 - p)) /
            (2 * π * ((m : ℝ) * q) * p * (1 - p)) := by
        field_simp [(sub_pos.mpr hp1).ne']
        <;> ring
      rw [hbase, div_rpow (by positivity) hc.le]
      dsimp [Z]
      field_simp
    have ht := hn.mul hz
    rw [mul_one] at ht
    apply ht.congr'
    filter_upwards [hsnat.eventually (eventually_gt_atTop 0)] with m hsm
    have hzs := (hZ (s m) (by exact_mod_cast hsm)).ne'
    field_simp
  obtain ⟨r, hrange, hrmax⟩ : ∃ r : ℕ → ℕ,
      (∀ m, r m ∈ range (m + 1)) ∧
      (∀ m j, j ∈ range (m + 1) → poweredRatio a l m j ≤ poweredRatio a l m (r m)) := by
    have hex (m : ℕ) := exists_max_image (range (m + 1)) (poweredRatio a l m)
      (show (range (m + 1)).Nonempty from ⟨0, by simp⟩)
    choose r hr hmax using hex
    exact ⟨r, hr, hmax⟩
  have hr (m : ℕ) : r m ≤ m := Nat.le_of_lt_succ (mem_range.mp (hrange m))
  have hmax (m j : ℕ) (hj : j ≤ m) := hrmax m j (mem_range.mpr (Nat.lt_succ_of_le hj))
  have hM (m : ℕ) : maximumValue a l m = poweredRatio a l m (r m) := by
    apply le_antisymm
    · apply max'_le
      intro y hy
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hy
      exact hrmax m j hj
    · apply le_max'
      exact mem_image.mpr ⟨r m, hrange m, rfl⟩
  have hslope := actual_maximizer_slope a ha l hl r hr hmax
  change Tendsto (fun m : ℕ => (r m : ℝ) / m) atTop (𝓝 q) at hslope
  have hdr := hpath r hslope
  let f (m : ℕ) := ⌊(m : ℝ) * q⌋₊
  have hf (m : ℕ) : f m ≤ m :=
    Nat.floor_le_of_le (by nlinarith [Nat.cast_nonneg (α := ℝ) m])
  have hfslope : Tendsto (fun m : ℕ => (f m : ℝ) / m) atTop (𝓝 q) := by
    have herr (m : ℕ) : |(f m : ℝ) - m * q| ≤ 1 :=
      Nat.abs_floor_sub_le (by positivity)
    have hd : Tendsto (fun m : ℕ => ((f m : ℝ) - m * q) / m) atTop (𝓝 0) := by
      apply squeeze_zero_norm' (Eventually.of_forall fun m => ?_)
        (tendsto_const_nhds.div_atTop hm : Tendsto (fun m : ℕ => (1 : ℝ) / m) atTop (𝓝 0))
      rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
      exact div_le_div_of_nonneg_right (herr m) (Nat.cast_nonneg m)
    have ht := hd.add_const q
    rw [zero_add] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop 0] with m hm0
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
    field_simp
    ring
  have hdf := hpath f hfslope
  have hlo : Tendsto (fun m : ℕ => poweredRatio a l m (f m) * K m) atTop (𝓝 L) := by
    have ht := (floor_comparison a ha l hl).div hdf one_ne_zero
    rw [div_one] at ht
    change Tendsto (fun m : ℕ =>
      (prefixValue a l m (f m) / B ^ (m * l) * H m) /
        (S (f m) / Z ((m : ℝ) * q))) atTop (𝓝 L) at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop 0] with m hm0
    rw [hidentity]
    have hz := (hZ ((m : ℝ) * q) (by positivity)).ne'
    dsimp only [K]
    field_simp
  let E (m : ℕ) := (∑ i ∈ range (r m + 1), ((m.choose i : ℝ) * a ^ i) ^ l) /
    ((m.choose (r m) : ℝ) * a ^ r m) ^ l
  let X (m : ℕ) := binomialMass q m (r m) * sqrt (2 * π * m * q * (1 - q))
  have hE : Tendsto E atTop (𝓝 L) := by
    have hqa : q < a / (1 + a) := by
      dsimp [q]; exact div_lt_div_of_pos_left ha (by positivity) (by linarith)
    have ht := BinomialMovingEndpoint.moving_endpoint_sum a q ha hq hqa l hl r hslope
    have hid : q / (a * (1 - q)) = (1 + a)⁻¹ := by
      have hcomp : 1 - q = (1 + a) / (1 + 2 * a) := by
        dsimp [q]; field_simp; ring
      rw [hcomp, inv_eq_one_div]
      dsimp [q]
      field_simp
    rwa [hid] at ht
  have hcap : Tendsto (fun m => max 1 (X m)) atTop (𝓝 1) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (BinomialUniformMaximum.uniform_upper q hq hq1 (ε / 2) (by positivity))
    refine ⟨N, fun m hmN => ?_⟩
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_max_left _ _))]
    have hbnd := hN m hmN (r m) (hr m)
    have hx : max 1 (X m) ≤ 1 + ε / 2 := max_le (by linarith) hbnd
    linarith
  have hu : Tendsto (fun m : ℕ => E m * (max 1 (X m)) ^ l /
      (S (r m) / Z ((m : ℝ) * q))) atTop (𝓝 L) := by
    convert (hE.mul (hcap.pow l)).div hdr one_ne_zero using 1
    · ext m
      rfl
    · simp
  have hbound : ∀ᶠ m : ℕ in atTop, maximumValue a l m * K m ≤
      E m * (max 1 (X m)) ^ l / (S (r m) / Z ((m : ℝ) * q)) := by
    filter_upwards [eventually_gt_atTop 0] with m hm0
    have hz := hZ ((m : ℝ) * q) (by positivity)
    have hw : (0 : ℝ) < (m.choose (r m) : ℝ) * a ^ r m :=
      mul_pos (by exact_mod_cast Nat.choose_pos (hr m)) (pow_pos ha _)
    have htilt : binomialMass q m (r m) =
        ((m.choose (r m) : ℝ) * a ^ r m) / ((1 + a) ^ r m * B ^ m) := by
      have hcomp : 1 - q = (1 + a) / (1 + 2 * a) := by dsimp [q]; field_simp; ring
      rw [binomialMass, hcomp]
      dsimp [q, B]
      rw [div_pow, div_pow, div_pow]
      have hbp : (1 + a) ^ m = (1 + a) ^ r m * (1 + a) ^ (m - r m) := by
        rw [← pow_add, Nat.add_sub_of_le (hr m)]
      have hcp : (1 + 2 * a) ^ m =
          (1 + 2 * a) ^ r m * (1 + 2 * a) ^ (m - r m) := by
        rw [← pow_add, Nat.add_sub_of_le (hr m)]
      field_simp
      rw [hbp, hcp]
      ring
    have hid : maximumValue a l m * K m = E m * X m ^ l /
        (S (r m) / Z ((m : ℝ) * q)) := by
      rw [hM, hidentity]
      dsimp [E, X, K, H, prefixValue]
      rw [htilt]
      simp only [mul_pow, div_pow, ← pow_mul]
      have hchoose : (m.choose (r m) : ℝ) ≠ 0 :=
        (by exact_mod_cast Nat.choose_pos (hr m) : (0 : ℝ) < m.choose (r m)).ne'
      field_simp
    rw [hid]
    apply div_le_div_of_nonneg_right _ (div_pos (hS _) hz).le
    apply mul_le_mul_of_nonneg_left _ (show 0 ≤ E m by dsimp [E]; positivity)
    apply pow_le_pow_left₀ _ (le_max_right _ _) l
    dsimp [X, binomialMass]
    positivity
  have hlim : Tendsto (fun m => maximumValue a l m * K m) atTop (𝓝 L) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hu
    · exact Eventually.of_forall fun m =>
        mul_le_mul_of_nonneg_right (by rw [hM]; exact hmax m _ (hf m)) (hK m)
    · exact hbound
  let A (m : ℕ) := sqrt (l : ℝ) / sqrt (2 * π * m) *
    (sqrt (1 + 2 * a) * (1 + a) * a ^ (((l : ℝ) - 2) / 2) /
      ((1 + a) ^ l - 1)) * B ^ (((m : ℝ) + 1 / 2) * (l : ℝ))
  have hbpow : 1 < (1 + a) ^ l := one_lt_pow₀ (by linarith) hl.ne'
  have hdenpos : 0 < (1 + a) ^ l - 1 := sub_pos.mpr hbpow
  have hLform : L = (1 + a) ^ l / ((1 + a) ^ l - 1) := by
    dsimp [L]
    rw [inv_pow]
    field_simp
    <;> ring
  have hLpos : 0 < L := by rw [hLform]; positivity
  have hApos (m : ℕ) (hm0 : 0 < m) : 0 < A m := by dsimp [A]; positivity
  have hAK (m : ℕ) (hm0 : 0 < m) : A m * K m = L := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
    have hkpos : 0 < K m := by dsimp [K, H, Z]; positivity
    have hqcomp : 1 - q = (1 + a) / (1 + 2 * a) := by
      dsimp [q]; field_simp; ring
    have hpcomp : 1 - p = 1 / (1 + a) := by dsimp [p]; field_simp; ring
    apply log_injOn_pos (mul_pos (hApos m hm0) hkpos) hLpos
    rw [log_mul (hApos m hm0).ne' hkpos.ne', hLform]
    dsimp [A, K, H, Z]
    rw [hqcomp, hpcomp]
    dsimp [q, p, B, t]
    simp (disch := positivity) only [log_mul, log_div, log_pow, log_sqrt,
      log_rpow, log_one, Nat.cast_mul]
    ring
  have ht := hlim.div_const L
  rw [div_self hLpos.ne'] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with m hm0
  change maximumValue a l m * K m / L = maximumValue a l m / A m
  rw [← hAK m hm0]
  have hkpos : 0 < K m := by dsimp [K, H, Z]; positivity
  field_simp

end D5.S3.AnalyticClosure.BinomialPoweredRatioMaximum
