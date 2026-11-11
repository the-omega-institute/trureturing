/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthRates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Single-length moment errors vanish uniformly on polynomial length bands. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SingleLengthBandGeometry
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SingleLengthMainTerms

/-! Uniform error estimates for cumulative single-length prime moments. -/

open Set Filter
open scoped Topology

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

/-- The relative sampling error includes the terminal fractional cell. -/
def cumulativeSamplingRate (k : ℕ) (Y v : ℝ) : ℝ :=
  Real.sqrt (Real.log Y / v) + (Real.log Y / v) ^ ((k : ℝ) / 2) +
    (v * Real.log Y) ^ ((k : ℝ) / 2) / Y

/-- The relative sampling envelope vanishes uniformly over a polynomial band. -/
theorem sampling_uniform (k : ℕ) (α β η : ℝ) (hk : k = 2 ∨ k = 4)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 4) (hη : 0 < η) :
    ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ, Y ^ α ≤ v → v ≤ Y ^ β →
      cumulativeSamplingRate k Y v ≤ η := by
  let t := min (η / 3) 1
  have ht : 0 < t := lt_min (by positivity) zero_lt_one
  filter_upwards [sqrt_rate α t hα ht,
    cell_rate β (η / 3) k (hα.trans hαβ).le (by linarith)
      (by rcases hk with rfl | rfl <;> norm_num) (by positivity),
    eventually_ge_atTop (1 : ℝ)] with Y hs he hY v hvα hvβ
  have hv : 1 ≤ v := (Real.one_le_rpow hY hα.le).trans hvα
  have hx0 : 0 ≤ Real.log Y / v := div_nonneg (Real.log_nonneg hY) (by positivity)
  have hs1 : Real.sqrt (Real.log Y / v) ≤ 1 := (hs v hvα).trans (min_le_right _ _)
  have hx1 : Real.log Y / v ≤ 1 := Real.sqrt_le_one.mp hs1
  have hx : Real.log Y / v ≤ t :=
    (Real.le_sqrt_self_iff.mpr hx1).trans (hs v hvα)
  have hp : (Real.log Y / v) ^ ((k : ℝ) / 2) ≤ t := by
    rcases hk with rfl | rfl
    · simpa only [Nat.cast_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0),
        Real.rpow_one] using hx
    · norm_num only [Nat.cast_ofNat, show (4 : ℝ) / 2 = 2 by norm_num,
        Real.rpow_two]
      have hsq : (Real.log Y / v) ^ 2 ≤ Real.log Y / v := by
        simpa only [sq] using mul_le_of_le_one_right hx0 hx1
      exact hsq.trans hx
  have htη : t ≤ η / 3 := min_le_left _ _
  have hsη := (hs v hvα).trans htη
  have hpη := hp.trans htη
  have heη := he v hv hvβ
  unfold cumulativeSamplingRate
  linarith only [hsη, hpη, heη]

/-- The first Montgomery–Soundararajan error vanishes uniformly on the length band. -/
private theorem ms_first_error_uniform (k : ℕ) (α β η : ℝ) (hk : k = 2 ∨ k = 4)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 4) (hη : 0 < η) :
    ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ, Y ^ α ≤ v → v ≤ Y ^ β →
      let N : ℝ := ⌊Y⌋₊
      let K : ℝ := ⌊v⌋₊
      N * Real.log N ^ (k / 2) * K ^ (k / 2) *
        (K / Real.log N) ^ (-1 / (8 * (k : ℝ))) ≤
          η * Y * v ^ (k / 2) * Real.log (Y / v) ^ (k / 2) := by
  have hk0 : 0 < (k : ℝ) := by rcases hk with rfl | rfl <;> norm_num
  have hβ1 : β < 1 := hβ.trans (by norm_num)
  have hc : 0 < (1 - β) ^ (k / 2) := pow_pos (sub_pos.mpr hβ1) _
  have hq : 0 < 1 / (8 * (k : ℝ)) := by positivity
  have hlim0 := (isLittleO_log_rpow_atTop (half_pos hα)).tendsto_div_nhds_zero
  have hlim := (hlim0.rpow_const_nhds_zero hq).eventually_le_const (mul_pos hη hc)
  filter_upwards [hlim, band_geometry α β hα hαβ hβ,
    eventually_ge_atTop (2 : ℝ)] with Y hsmall hgeom hY v hvα hvβ
  dsimp only
  obtain ⟨hN, hK, _, _, hKlo, _, _, _, _⟩ := hgeom v hvα hvβ
  have hY0 : 0 < Y := by positivity
  have hv1 : 1 ≤ v := (Real.one_le_rpow (by linarith : 1 ≤ Y) hα.le).trans hvα
  have hv0 : 0 < v := zero_lt_one.trans_le hv1
  have hK0 : 0 < (⌊v⌋₊ : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hK)
  have hN1 : (1 : ℝ) < (⌊Y⌋₊ : ℝ) := by exact_mod_cast hN
  have hLN : 0 < Real.log (⌊Y⌋₊ : ℝ) := Real.log_pos hN1
  have hLY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hlogN := Real.log_le_log (by positivity : 0 < (⌊Y⌋₊ : ℝ))
    (Nat.floor_le hY0.le)
  have hratio : Real.log (⌊Y⌋₊ : ℝ) / (⌊v⌋₊ : ℝ) ≤
      Real.log Y / Y ^ (α / 2) := by
    exact (div_le_div_of_nonneg_right hlogN hK0.le).trans
      (div_le_div_of_nonneg_left hLY (Real.rpow_pos_of_pos hY0 _) hKlo)
  have hr : ((⌊v⌋₊ : ℝ) / Real.log (⌊Y⌋₊ : ℝ)) ^
      (-1 / (8 * (k : ℝ))) ≤ η * (1 - β) ^ (k / 2) := by
    rw [neg_div, Real.rpow_neg_eq_inv_rpow, inv_div]
    exact (Real.rpow_le_rpow (by positivity) hratio hq.le).trans hsmall
  have hbase : (⌊Y⌋₊ : ℝ) * Real.log (⌊Y⌋₊ : ℝ) ^ (k / 2) *
      (⌊v⌋₊ : ℝ) ^ (k / 2) ≤ Y * Real.log Y ^ (k / 2) * v ^ (k / 2) := by
    exact mul_le_mul
      (mul_le_mul (Nat.floor_le hY0.le) (pow_le_pow_left₀ hLN.le hlogN _)
        (by positivity) hY0.le)
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hv0.le) _)
      (by positivity) (by positivity)
  have hlower := (band_log β Y v hβ1 (by linarith) hv1 hvβ).2.1
  calc
    _ ≤ (Y * Real.log Y ^ (k / 2) * v ^ (k / 2)) *
        (η * (1 - β) ^ (k / 2)) :=
      mul_le_mul hbase hr (by positivity) (by positivity)
    _ = η * Y * v ^ (k / 2) * ((1 - β) * Real.log Y) ^ (k / 2) := by
      rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hlower _) (by positivity)

/-- The correlation part of the single-length moment error is uniformly negligible. -/
private theorem ms_correlation_error_uniform (k : ℕ) (α β ε η : ℝ)
    (hk : k = 2 ∨ k = 4) (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 4)
    (hε : 0 < ε) (hεβ : ε < 1 / 2 - 2 * β) (hη : 0 < η) :
    ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ, Y ^ α ≤ v → v ≤ Y ^ β →
      (⌊v⌋₊ : ℝ) ^ k * (⌊Y⌋₊ : ℝ) ^ (1 / 2 + ε) ≤
        η * Y * v ^ (k / 2) * Real.log (Y / v) ^ (k / 2) := by
  have hβ1 : β < 1 := hβ.trans (by norm_num)
  have hc : 0 < (1 - β) ^ (k / 2) := pow_pos (sub_pos.mpr hβ1) _
  filter_upwards [arithmetic_rate_four β ε (η * (1 - β) ^ (k / 2)) hε hεβ
      (mul_pos hη hc), sqrt_rate α 1 hα zero_lt_one,
    eventually_ge_atTop (2 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with Y harith hs hY hL1 v hvα hvβ
  have hY0 : 0 < Y := by positivity
  have hv1 : 1 ≤ v := (Real.one_le_rpow (by linarith : 1 ≤ Y) hα.le).trans hvα
  have hv0 : 0 < v := zero_lt_one.trans_le hv1
  have hL : 0 < Real.log Y := zero_lt_one.trans_le hL1
  have hLv : Real.log Y ≤ v := (div_le_one hv0).mp (Real.sqrt_le_one.mp (hs v hvα))
  have hx1 : 1 ≤ v / Real.log Y := (one_le_div hL).mpr hLv
  have hfour : Y ^ (-1 / 2 + ε) * (v / Real.log Y) ^ 2 ≤
      η * (1 - β) ^ (k / 2) := by
    calc
      _ = Y ^ (-1 / 2 + ε) * v ^ 2 * (Real.log Y) ^ (-2 : ℝ) := by
        rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hL.le,
          Real.rpow_two]
        simp only [div_eq_mul_inv, mul_pow, inv_pow, mul_assoc]
      _ ≤ _ := harith v hv0.le hvβ
  have hp : Y ^ (-1 / 2 + ε) * (v / Real.log Y) ^ (k / 2) ≤
      η * (1 - β) ^ (k / 2) := by
    rcases hk with rfl | rfl
    · norm_num only [Nat.reduceDiv, pow_one] at *
      have hx : v / Real.log Y ≤ (v / Real.log Y) ^ 2 := by
        simpa only [sq] using le_mul_of_one_le_right
          (by positivity : 0 ≤ v / Real.log Y) hx1
      exact (mul_le_mul_of_nonneg_left hx (by positivity)).trans hfour
    · exact hfour
  have hYexp : Y ^ (1 / 2 + ε) = Y ^ (-1 / 2 + ε) * Y := by
    conv_lhs => rw [show (1 / 2 + ε : ℝ) = (-1 / 2 + ε) + 1 by ring,
      Real.rpow_add hY0, Real.rpow_one]
  have hid : v ^ k * Y ^ (1 / 2 + ε) =
      (Y ^ (-1 / 2 + ε) * (v / Real.log Y) ^ (k / 2)) *
        (Y * v ^ (k / 2) * Real.log Y ^ (k / 2)) := by
    rw [hYexp]
    rcases hk with rfl | rfl <;> norm_num only [Nat.reduceDiv, pow_one]
    all_goals field_simp [hL.ne']
  have hlower := (band_log β Y v hβ1 (by linarith) hv1 hvβ).2.1
  calc
    _ ≤ v ^ k * Y ^ (1 / 2 + ε) := mul_le_mul
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hv0.le) _)
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hY0.le) (by linarith))
      (by positivity) (by positivity)
    _ = _ := hid
    _ ≤ (η * (1 - β) ^ (k / 2)) * (Y * v ^ (k / 2) * Real.log Y ^ (k / 2)) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = η * Y * v ^ (k / 2) * ((1 - β) * Real.log Y) ^ (k / 2) := by
      rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hlower _) (by positivity)

/-- Both explicit Montgomery–Soundararajan errors are uniformly negligible. -/
theorem ms_error_uniform (k : ℕ) (α β ε η : ℝ) (hk : k = 2 ∨ k = 4)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 4)
    (hε : 0 < ε) (hεβ : ε < 1 / 2 - 2 * β) (hη : 0 < η) :
    ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ, Y ^ α ≤ v → v ≤ Y ^ β →
      montgomerySoundararajanError k ε (⌊Y⌋₊ : ℝ) (⌊v⌋₊ : ℝ) ≤
        η * Y * v ^ (k / 2) * Real.log (Y / v) ^ (k / 2) := by
  filter_upwards [ms_first_error_uniform k α β (η / 2) hk hα hαβ hβ (half_pos hη),
    ms_correlation_error_uniform k α β ε (η / 2) hk hα hαβ hβ hε hεβ (half_pos hη)]
    with Y hfirst hcorr v hvα hvβ
  have h₁ := hfirst v hvα hvβ
  have h₂ := hcorr v hvα hvβ
  dsimp only at h₁
  unfold montgomerySoundararajanError
  linarith only [h₁, h₂]

/-- Rounding both the cutoff and the length changes the main term by a uniform little-o error. -/
theorem main_errors_uniform (k : ℕ) (α β η : ℝ) (hk : k = 2 ∨ k = 4)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 4) (hη : 0 < η) :
    ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ, Y ^ α ≤ v → v ≤ Y ^ β →
      |montgomerySoundararajanMainTerm k (⌊Y⌋₊ : ℝ) (⌊v⌋₊ : ℝ) - montgomerySoundararajanMainTerm k Y v| ≤
        η * Y * v ^ (k / 2) * Real.log (Y / v) ^ (k / 2) := by
  obtain ⟨A, hA, hcut⟩ := cutoff_main_term k hk
  have hlength : ∃ B : ℝ, 0 < B ∧ ∀ Y v : ℝ, 2 ≤ Y → 1 ≤ v → v ≤ Y →
      |montgomerySoundararajanMainTerm k Y (⌊v⌋₊ : ℝ) - montgomerySoundararajanMainTerm k Y v| ≤
        B * Y * v ^ (k / 2 - 1) * Real.log Y ^ (k / 2) := by
    rcases hk with rfl | rfl
    · simpa only [Nat.reduceDiv, Nat.reduceSub, pow_zero, pow_one, mul_one] using
        length_main_second
    · simpa only [Nat.reduceDiv, Nat.reduceSub, pow_one] using length_main_fourth
  obtain ⟨B, hB, hlen⟩ := hlength
  have hβ1 : β < 1 := hβ.trans (by norm_num)
  let δ := η * (1 - β) ^ (k / 2) / (A + B)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδid : (A + B) * δ = η * (1 - β) ^ (k / 2) := by
    dsimp only [δ]
    field_simp
  filter_upwards [range_geometry α β 1 hα hβ1 zero_lt_one,
    sqrt_rate α 1 hα zero_lt_one, inverse_log_rate δ hδ,
    eventually_ge_atTop (2 : ℝ)] with Y hgeom hs hinv hY v hvα hvβ
  obtain ⟨hv2, hvY, _⟩ := hgeom.2.2 v hvα hvβ
  have hv1 : 1 ≤ v := by linarith
  have hv0 : 0 < v := by positivity
  have hY0 : 0 < Y := by positivity
  have hL : 0 < Real.log Y := zero_lt_one.trans_le hgeom.2.1
  have hLv : Real.log Y ≤ v := (div_le_one hv0).mp (Real.sqrt_le_one.mp (hs v hvα))
  have hYinv : 1 / Y ≤ δ :=
    (div_le_div_of_nonneg_left zero_le_one hL (Real.log_le_self hY0.le)).trans hinv
  have hvinv : 1 / v ≤ δ :=
    (div_le_div_of_nonneg_left zero_le_one hL hLv).trans hinv
  have hcoef : A / Y + B / v ≤ η * (1 - β) ^ (k / 2) := by
    calc
      _ = A * (1 / Y) + B * (1 / v) := by ring
      _ ≤ A * δ + B * δ := add_le_add
        (mul_le_mul_of_nonneg_left hYinv hA.le) (mul_le_mul_of_nonneg_left hvinv hB.le)
      _ = (A + B) * δ := by ring
      _ = _ := hδid
  have hK : 1 ≤ ⌊v⌋₊ := Nat.le_floor (by simpa using hv1)
  have hKv := Nat.floor_le hv0.le
  have hround := hcut Y ⌊v⌋₊ hY hK (hKv.trans hvY)
  have hmain : |montgomerySoundararajanMainTerm k (⌊Y⌋₊ : ℝ) (⌊v⌋₊ : ℝ) - montgomerySoundararajanMainTerm k Y v| ≤
      A * v ^ (k / 2) * Real.log Y ^ (k / 2) +
        B * Y * v ^ (k / 2 - 1) * Real.log Y ^ (k / 2) := by
    calc
      _ ≤ |montgomerySoundararajanMainTerm k (⌊Y⌋₊ : ℝ) (⌊v⌋₊ : ℝ) - montgomerySoundararajanMainTerm k Y (⌊v⌋₊ : ℝ)| +
          |montgomerySoundararajanMainTerm k Y (⌊v⌋₊ : ℝ) - montgomerySoundararajanMainTerm k Y v| := abs_sub_le _ _ _
      _ ≤ A * (⌊v⌋₊ : ℝ) ^ (k / 2) * Real.log Y ^ (k / 2) +
          B * Y * v ^ (k / 2 - 1) * Real.log Y ^ (k / 2) :=
        add_le_add (by simpa only [abs_sub_comm] using hround) (hlen Y v hY hv1 hvY)
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hKv _) hA.le)
        (pow_nonneg hL.le _)) le_rfl
  have hid : A * v ^ (k / 2) * Real.log Y ^ (k / 2) +
      B * Y * v ^ (k / 2 - 1) * Real.log Y ^ (k / 2) =
        (A / Y + B / v) * (Y * v ^ (k / 2) * Real.log Y ^ (k / 2)) := by
    rcases hk with rfl | rfl <;> norm_num only [Nat.reduceDiv, Nat.reduceSub, pow_zero,
      pow_one, mul_one]
    all_goals field_simp [hY0.ne', hv0.ne']
  have hlower := (band_log β Y v hβ1 (by linarith) hv1 hvβ).2.1
  calc
    _ ≤ _ := hmain
    _ = _ := hid
    _ ≤ (η * (1 - β) ^ (k / 2)) * (Y * v ^ (k / 2) * Real.log Y ^ (k / 2)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = η * Y * v ^ (k / 2) * ((1 - β) * Real.log Y) ^ (k / 2) := by
      rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hlower _) (by positivity)

/-- The second main term has the normalized leading term one uniformly on the band. -/
theorem second_main_uniform (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ : β < 1)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ, Y ^ α ≤ v → v ≤ Y ^ β →
      |montgomerySoundararajanMainTerm 2 Y v / (Y * v * Real.log (Y / v)) - 1| ≤ η := by
  let C : ℝ := |montgomerySoundararajanConstant - 1| + |montgomerySoundararajanConstant| + 2
  have hC : 0 < C := by dsimp only [C]; positivity
  let δ := η * (1 - β) / C
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  filter_upwards [inverse_log_rate δ hδ, eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with Y hinv hY hlog1 v hvα hvβ
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by positivity
  obtain ⟨hv1, hvY⟩ := FourthTransfer.FourthMomentAsymptotic.band_lengths
    hY1 hα hαβ hβ hvα hvβ
  have hv0 : 0 < v := zero_lt_one.trans_le hv1
  obtain ⟨hL, hlower, _⟩ := band_log β Y v hβ (by linarith) hv1 hvβ
  have hlog : 0 < Real.log Y := zero_lt_one.trans_le hlog1
  have hlv : 0 ≤ Real.log v := Real.log_nonneg hv1
  have hlvY : Real.log v ≤ Y :=
    (Real.log_le_log hv0 hvY).trans (Real.log_le_self hY0.le)
  have hrem : |(montgomerySoundararajanConstant - 1) * Y + 1 + Real.log v - montgomerySoundararajanConstant| ≤ C * Y := by
    calc
      _ ≤ |(montgomerySoundararajanConstant - 1) * Y + 1 + Real.log v| + |montgomerySoundararajanConstant| := abs_sub _ _
      _ ≤ (|(montgomerySoundararajanConstant - 1) * Y + 1| + |Real.log v|) + |montgomerySoundararajanConstant| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ ((|(montgomerySoundararajanConstant - 1) * Y| + |(1 : ℝ)|) + |Real.log v|) + |montgomerySoundararajanConstant| :=
        add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
      _ = |montgomerySoundararajanConstant - 1| * Y + 1 + Real.log v + |montgomerySoundararajanConstant| := by
        rw [abs_mul, abs_of_pos hY0, abs_one, abs_of_nonneg hlv]
      _ ≤ C * Y := by
        have hscale := mul_le_mul_of_nonneg_left hY1 (abs_nonneg montgomerySoundararajanConstant)
        dsimp only [C]
        linarith only [hscale, hY1, hlvY]
  have hCsmall : C ≤ η * Real.log (Y / v) := by
    have hs := mul_le_mul_of_nonneg_left ((div_le_iff₀ hlog).mp hinv) hC.le
    have hid : C * (δ * Real.log Y) = η * ((1 - β) * Real.log Y) := by
      dsimp only [δ]
      field_simp
    rw [mul_one, hid] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left hlower hη.le)
  have hid : montgomerySoundararajanMainTerm 2 Y v / (Y * v * Real.log (Y / v)) - 1 =
      ((montgomerySoundararajanConstant - 1) * Y + 1 + Real.log v - montgomerySoundararajanConstant) / (Y * Real.log (Y / v)) := by
    rw [second_main_exact Y v hY1 hv0]
    field_simp [hY0.ne', hv0.ne', hL.ne']
    ring
  rw [hid, abs_div, abs_of_pos (mul_pos hY0 hL)]
  calc
    _ ≤ C * Y / (Y * Real.log (Y / v)) :=
      div_le_div_of_nonneg_right hrem (by positivity)
    _ = C / Real.log (Y / v) := by field_simp
    _ ≤ η := (div_le_iff₀ hL).mpr hCsmall

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
