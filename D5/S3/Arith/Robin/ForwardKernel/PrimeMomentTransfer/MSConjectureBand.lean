/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureBand
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureBand
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The second and fourth Montgomery–Soundararajan conjectural moments control every polynomial band. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SingleLengthBandGeometry
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SingleLengthMainTerms

/-! Montgomery–Soundararajan, Primes in short intervals (2004), Conjecture 1,
restricted to moments two and four, is a hypothesis. The band consequences are derived here. -/

open Set Filter
open scoped Topology
namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

/-- Conjecture 1, with a uniform relative error on its stated integer-length range. -/
def MSConjectureTwoFour : Prop :=
  ∀ k : ℕ, (k = 2 ∨ k = 4) → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η →
    ∀ᶠ N : ℕ in atTop, ∀ H : ℕ,
      Real.log (N : ℝ) ^ (1 + ε) ≤ (H : ℝ) →
      (H : ℝ) ≤ (N : ℝ) ^ (1 - ε) →
      |discretePrimeMoment k N H - (if k = 2 then 1 else 3) * (N : ℝ) *
          ((H : ℝ) * Real.log ((N : ℝ) / (H : ℝ))) ^ (k / 2)| ≤
        η * (N : ℝ) * ((H : ℝ) * Real.log ((N : ℝ) / (H : ℝ))) ^ (k / 2)

/-- A fixed positive margin inside the unit exponent band puts both floors in the conjectural range. -/
theorem conjecture_band_geometry (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hβ : β < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ,
      Y ^ α ≤ v → v ≤ Y ^ β →
      2 ≤ ⌊Y⌋₊ ∧ 1 ≤ ⌊v⌋₊ ∧
      Real.log (⌊Y⌋₊ : ℝ) ^ (1 + ε) ≤ (⌊v⌋₊ : ℝ) ∧
      (⌊v⌋₊ : ℝ) ≤ (⌊Y⌋₊ : ℝ) ^ (1 - ε) ∧
      (⌊v⌋₊ : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by
  let ε := (1 - β) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hβ0 : 0 < β := hα.trans hαβ
  have hq : 0 ≤ 1 - ε := by dsimp [ε]; linarith
  have hβq : β < 1 - ε := by dsimp [ε]; linarith
  have hlog := (isLittleO_log_rpow_rpow_atTop (1 + ε) (half_pos hα)).tendsto_div_nhds_zero
  refine ⟨ε, hε, ?_⟩
  filter_upwards [floor_range α β hα hαβ hβ, floor_power_upper β (1 - ε) hβq hq,
    hlog.eventually_le_const zero_lt_one, eventually_ge_atTop (2 : ℝ)]
    with Y hfloor hupper hlog hY v hvα hvβ
  obtain ⟨hK, hKlo, hKhi, _, _⟩ := hfloor v hvα hvβ
  have hY0 : 0 < Y := by positivity
  have hN : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by simpa using hY)
  have hN1 : (1 : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast (by omega : 1 ≤ ⌊Y⌋₊)
  have hloglo : Real.log (⌊Y⌋₊ : ℝ) ^ (1 + ε) ≤ (⌊v⌋₊ : ℝ) := by
    calc
      _ ≤ Real.log Y ^ (1 + ε) := Real.rpow_le_rpow
        (Real.log_nonneg hN1)
        (Real.log_le_log (by positivity) (Nat.floor_le hY0.le)) (by linarith)
      _ ≤ Y ^ (α / 2) := (div_le_one (Real.rpow_pos_of_pos hY0 _)).mp hlog
      _ ≤ _ := hKlo
  have hupper' := hKhi.trans hupper
  refine ⟨hN, hK, hloglo, hupper', ?_⟩
  exact hupper'.trans (by simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hN1 (show 1 - ε ≤ 1 by linarith))

private theorem floored_second_main_error (Y v : ℝ) (hY : 2 ≤ Y)
    (hL : 1 ≤ Real.log Y) (hv : 1 ≤ v) (hvY : v ≤ Y)
    (hKN : (⌊v⌋₊ : ℝ) ≤ (⌊Y⌋₊ : ℝ)) :
    |(⌊Y⌋₊ : ℝ) * (⌊v⌋₊ : ℝ) * Real.log ((⌊Y⌋₊ : ℝ) / (⌊v⌋₊ : ℝ)) -
      Y * v * Real.log (Y / v)| ≤ 4 * Y * Real.log Y := by
  let N : ℝ := ⌊Y⌋₊
  let H : ℝ := ⌊v⌋₊
  have hY0 : 0 < Y := by positivity
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hH1 : 1 ≤ H := by
    change (1 : ℝ) ≤ (⌊v⌋₊ : ℝ)
    exact_mod_cast (Nat.le_floor (by simpa using hv) : 1 ≤ ⌊v⌋₊)
  have hH0 : 0 < H := zero_lt_one.trans_le hH1
  have hN1 : 1 ≤ N := hH1.trans hKN
  have hN0 : 0 < N := zero_lt_one.trans_le hN1
  have hNY : N ≤ Y := Nat.floor_le hY0.le
  have hHv : H ≤ v := Nat.floor_le hv0.le
  have hHN : H ≤ N := hKN
  have hNYdiff : |N - Y| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hNY)]
    linarith [Nat.lt_floor_add_one Y]
  have hHvdiff : |H - v| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hHv)]
    linarith [Nat.lt_floor_add_one v]
  have hlogN := floor_log_difference Y (by linarith : 1 ≤ Y)
  have hlogH := floor_log_difference v hv
  have hln : |Real.log (N / H)| ≤ Real.log Y := by
    rw [abs_of_nonneg (Real.log_nonneg ((one_le_div hH0).mpr hHN))]
    exact (Real.log_le_log (div_pos hN0 hH0) (div_le_self hN0.le hH1)).trans
      (Real.log_le_log hN0 hNY)
  have hly : |Real.log (Y / v)| ≤ Real.log Y := by
    rw [abs_of_nonneg (Real.log_nonneg ((one_le_div hv0).mpr hvY))]
    exact Real.log_le_log (div_pos hY0 hv0) (div_le_self hY0.le hv)
  have ht₁ : |(N - Y) * H * Real.log (N / H)| ≤ Y * Real.log Y := by
    calc
      _ = |N - Y| * H * |Real.log (N / H)| := by rw [abs_mul, abs_mul, abs_of_pos hH0]
      _ ≤ 1 * v * Real.log Y := by gcongr
      _ ≤ Y * Real.log Y := by gcongr; linarith
  have ht₂ : |Y * (H - v) * Real.log (Y / v)| ≤ Y * Real.log Y := by
    rw [abs_mul, abs_mul, abs_of_pos hY0]
    simpa only [mul_one] using mul_le_mul (mul_le_mul_of_nonneg_left hHvdiff hY0.le) hly
      (abs_nonneg _) (by positivity)
  have ht₃ : |Y * H * (Real.log N - Real.log Y)| ≤ Y := by
    rw [abs_mul, abs_of_pos (mul_pos hY0 hH0), abs_sub_comm]
    calc
      _ ≤ Y * H * (1 / N) := mul_le_mul_of_nonneg_left hlogN (by positivity)
      _ ≤ Y * N * (1 / N) := by gcongr
      _ = Y := by field_simp
  have ht₄ : |Y * H * (Real.log v - Real.log H)| ≤ Y := by
    rw [abs_mul, abs_of_pos (mul_pos hY0 hH0)]
    calc
      _ ≤ Y * H * (1 / H) := mul_le_mul_of_nonneg_left hlogH (by positivity)
      _ = Y := by field_simp
  have heq : N * H * Real.log (N / H) - Y * v * Real.log (Y / v) =
      (N - Y) * H * Real.log (N / H) + Y * (H - v) * Real.log (Y / v) +
      Y * H * (Real.log N - Real.log Y) + Y * H * (Real.log v - Real.log H) := by
    rw [Real.log_div hN0.ne' hH0.ne', Real.log_div hY0.ne' hv0.ne']
    ring
  change |N * H * Real.log (N / H) - Y * v * Real.log (Y / v)| ≤ _
  rw [heq]
  calc
    _ ≤ |(N - Y) * H * Real.log (N / H)| + |Y * (H - v) * Real.log (Y / v)| +
        |Y * H * (Real.log N - Real.log Y)| + |Y * H * (Real.log v - Real.log H)| := by
      have h₁ := abs_add_le
        ((N - Y) * H * Real.log (N / H) + Y * (H - v) * Real.log (Y / v) +
          Y * H * (Real.log N - Real.log Y))
        (Y * H * (Real.log v - Real.log H))
      have h₂ := abs_add_le
        ((N - Y) * H * Real.log (N / H) + Y * (H - v) * Real.log (Y / v))
        (Y * H * (Real.log N - Real.log Y))
      have h₃ := abs_add_le ((N - Y) * H * Real.log (N / H))
        (Y * (H - v) * Real.log (Y / v))
      linarith only [h₁, h₂, h₃]
    _ ≤ 2 * Y * Real.log Y + 2 * Y := by linarith only [ht₁, ht₂, ht₃, ht₄]
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hL hY0.le]

/-- Conjecture 1 supplies the cumulative discrete variance uniformly on every strict polynomial band. -/
theorem conjecture_discrete_second_uniform (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hβ : β < 1) (hMS : MSConjectureTwoFour) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ, Y ^ α ≤ v → v ≤ Y ^ β →
      |discretePrimeMoment 2 ⌊Y⌋₊ ⌊v⌋₊ - Y * v * Real.log (Y / v)| ≤
        η * Y * v * Real.log (Y / v) := by
  obtain ⟨ε, hε, hgeom⟩ := conjecture_band_geometry α β hα hαβ hβ
  let ζ := η * (1 - β) / 2
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hdisc := hMS 2 (Or.inl rfl) ε hε ζ hζ
  filter_upwards [hgeom, (tendsto_nat_floor_atTop (α := ℝ)).eventually hdisc,
    (tendsto_rpow_atTop hα).eventually_ge_atTop (8 / (η * (1 - β))),
    eventually_ge_atTop (2 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with Y hgeom hd hlarge hY hlog v hvα hvβ
  obtain ⟨hN, hH, hlo, hhi, hHN⟩ := hgeom v hvα hvβ
  have hY0 : 0 < Y := by positivity
  have hv1 : 1 ≤ v := (Real.one_le_rpow (by linarith : 1 ≤ Y) hα.le).trans hvα
  have hv0 : 0 < v := zero_lt_one.trans_le hv1
  have hvY : v ≤ Y := hvβ.trans (by simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Y) hβ.le)
  have hH0 : (0 : ℝ) < (⌊v⌋₊ : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hH)
  have hN0 : (0 : ℝ) < (⌊Y⌋₊ : ℝ) := by exact_mod_cast (zero_lt_two.trans_le hN)
  have hHNlog : 0 ≤ Real.log ((⌊Y⌋₊ : ℝ) / (⌊v⌋₊ : ℝ)) :=
    Real.log_nonneg ((one_le_div hH0).mpr hHN)
  have hlogupper : Real.log ((⌊Y⌋₊ : ℝ) / (⌊v⌋₊ : ℝ)) ≤ Real.log Y := by
    apply Real.log_le_log (div_pos hN0 hH0)
    exact (div_le_self hN0.le (by exact_mod_cast hH)).trans (Nat.floor_le hY0.le)
  have hd' := hd ⌊v⌋₊ hlo hhi
  norm_num only [ite_true, Nat.reduceDiv, pow_one, one_mul] at hd'
  have hbase : (⌊Y⌋₊ : ℝ) * ((⌊v⌋₊ : ℝ) *
      Real.log ((⌊Y⌋₊ : ℝ) / (⌊v⌋₊ : ℝ))) ≤ Y * v * Real.log Y := by
    calc
      _ ≤ Y * (v * Real.log Y) := mul_le_mul (Nat.floor_le hY0.le)
        (mul_le_mul (Nat.floor_le hv0.le) hlogupper hHNlog hv0.le)
        (by positivity) hY0.le
      _ = _ := by ring
  have hlow := (band_log β Y v hβ (by linarith) hv1 hvβ).2.1
  have hdsmall : |discretePrimeMoment 2 ⌊Y⌋₊ ⌊v⌋₊ -
      (⌊Y⌋₊ : ℝ) * (⌊v⌋₊ : ℝ) * Real.log ((⌊Y⌋₊ : ℝ) / (⌊v⌋₊ : ℝ))| ≤
      (η / 2) * Y * v * Real.log (Y / v) := by
    have hd'' : |discretePrimeMoment 2 ⌊Y⌋₊ ⌊v⌋₊ -
        (⌊Y⌋₊ : ℝ) * (⌊v⌋₊ : ℝ) * Real.log ((⌊Y⌋₊ : ℝ) / (⌊v⌋₊ : ℝ))| ≤
        ζ * ((⌊Y⌋₊ : ℝ) * ((⌊v⌋₊ : ℝ) *
          Real.log ((⌊Y⌋₊ : ℝ) / (⌊v⌋₊ : ℝ)))) := by
      simpa only [mul_assoc] using hd'
    have hh := hd''.trans (mul_le_mul_of_nonneg_left hbase hζ.le)
    have hh' : ζ * (Y * v * Real.log Y) = (η / 2) * Y * v * ((1 - β) * Real.log Y) := by dsimp [ζ]; ring
    calc
      _ ≤ ζ * (Y * v * Real.log Y) := by simpa only [mul_assoc] using hh
      _ = (η / 2) * Y * v * ((1 - β) * Real.log Y) := hh'
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
  have hlarge' : 8 ≤ η * (1 - β) * v := by
    simpa only [mul_comm] using
      (div_le_iff₀ (mul_pos hη (sub_pos.mpr hβ))).mp (hlarge.trans hvα)
  have hm := floored_second_main_error Y v hY hlog hv1 hvY hHN
  have hmsmall : 4 * Y * Real.log Y ≤ (η / 2) * Y * v * Real.log (Y / v) := by
    calc
      _ ≤ (η / 2) * Y * v * ((1 - β) * Real.log Y) := by
        have hs := mul_le_mul_of_nonneg_right hlarge' (show 0 ≤ Y * Real.log Y by positivity)
        nlinarith only [hs]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
  exact (abs_sub_le (discretePrimeMoment 2 ⌊Y⌋₊ ⌊v⌋₊)
    ((⌊Y⌋₊ : ℝ) * (⌊v⌋₊ : ℝ) * Real.log ((⌊Y⌋₊ : ℝ) / (⌊v⌋₊ : ℝ)))
    (Y * v * Real.log (Y / v))).trans (by linarith only [hdsmall, hm.trans hmsmall])

/-- The conjectural fourth moment has a uniform upper bound on every strict polynomial band. -/
theorem conjecture_discrete_fourth_upper (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hβ : β < 1) (hMS : MSConjectureTwoFour) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ,
      Y ^ α ≤ v → v ≤ Y ^ β →
      discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ ≤ A * Y * v ^ 2 * Real.log Y ^ 2 := by
  obtain ⟨ε, hε, hgeom⟩ := conjecture_band_geometry α β hα hαβ hβ
  have hdisc := hMS 4 (Or.inr rfl) ε hε 1 zero_lt_one
  refine ⟨4, by norm_num, ?_⟩
  filter_upwards [hgeom, (tendsto_nat_floor_atTop (α := ℝ)).eventually hdisc,
    eventually_ge_atTop (2 : ℝ)] with Y hgeom hd hY v hvα hvβ
  obtain ⟨hN, hH, hlo, hhi, hHN⟩ := hgeom v hvα hvβ
  have hY0 : 0 < Y := by positivity
  have hv0 : 0 < v := (Real.rpow_pos_of_pos hY0 _).trans_le hvα
  have hH0 : (0 : ℝ) < (⌊v⌋₊ : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hH)
  have hN0 : (0 : ℝ) < (⌊Y⌋₊ : ℝ) := by exact_mod_cast (zero_lt_two.trans_le hN)
  have hlog0 : 0 ≤ Real.log ((⌊Y⌋₊ : ℝ) / (⌊v⌋₊ : ℝ)) :=
    Real.log_nonneg ((one_le_div hH0).mpr hHN)
  have hlogle : Real.log ((⌊Y⌋₊ : ℝ) / (⌊v⌋₊ : ℝ)) ≤ Real.log Y := by
    apply Real.log_le_log (div_pos hN0 hH0)
    exact (div_le_self hN0.le (by exact_mod_cast hH)).trans (Nat.floor_le hY0.le)
  have hbase : (⌊Y⌋₊ : ℝ) * ((⌊v⌋₊ : ℝ) *
      Real.log ((⌊Y⌋₊ : ℝ) / (⌊v⌋₊ : ℝ))) ^ 2 ≤ Y * (v * Real.log Y) ^ 2 :=
    mul_le_mul (Nat.floor_le hY0.le)
      (pow_le_pow_left₀ (by positivity)
        (mul_le_mul (Nat.floor_le hv0.le) hlogle hlog0 hv0.le) 2)
      (by positivity) hY0.le
  have hh := (abs_le.mp (hd ⌊v⌋₊ hlo hhi)).2
  norm_num only [show ¬(4 : ℕ) = 2 by decide, ite_false, Nat.reduceDiv, one_mul] at hh
  have hmain : discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ ≤ 4 *
      ((⌊Y⌋₊ : ℝ) * ((⌊v⌋₊ : ℝ) * Real.log ((⌊Y⌋₊ : ℝ) / (⌊v⌋₊ : ℝ))) ^ 2) := by
    linarith only [hh]
  calc
    _ ≤ 4 * (Y * (v * Real.log Y) ^ 2) := hmain.trans (mul_le_mul_of_nonneg_left hbase (by norm_num))
    _ = _ := by ring

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
