/- GID: D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentAsymptotic
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentAsymptotic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform cumulative fourth-moment asymptotics imply band and local energy bounds. -/

import D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FourthMomentTransferDefs
import D5.S3.Arith.Robin.ForwardKernel.FourthMomentBandDefs
import D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer

/-! Cumulative fourth moments control the exponent band and every comparable subinterval. -/

namespace D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FourthMomentAsymptotic

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs FourthMomentBandDefs FourthMomentTransferDefs
open VarianceTransfer

noncomputable section
set_option autoImplicit false

/-- The cumulative fourth-moment formula holds uniformly over the full exponent band. -/
def FourthMomentAsymptoticFor (E : ℝ → ℝ) (α β B : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ,
    Y ^ α ≤ v → v ≤ Y ^ β →
    |(∫ x in (1 : ℝ)..Y, |increment E v x| ^ 4) -
      3 * v ^ 2 * (∫ y in (1 : ℝ)..Y, (Real.log (y / v) + B) ^ 2)| ≤
        η * Y * v ^ 2 * Real.log (Y / v) ^ 2

private lemma band_lengths {α β Y v : ℝ} (hY : 1 ≤ Y)
    (hα : 0 < α) (_hαβ : α < β) (hβ : β < 1)
    (hvα : Y ^ α ≤ v) (hvβ : v ≤ Y ^ β) : 1 ≤ v ∧ v ≤ Y := by
  exact ⟨(Real.one_le_rpow hY hα.le).trans hvα,
    hvβ.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hY hβ.le)⟩

private lemma band_log_lower {β Y v : ℝ} (hY : 0 < Y) (hv : 0 < v)
    (hvβ : v ≤ Y ^ β) : (1 - β) * Real.log Y ≤ Real.log (Y / v) := by
  rw [Real.log_div hY.ne' hv.ne']
  have h := Real.log_le_log hv hvβ
  rw [Real.log_rpow hY] at h
  linarith

private lemma log_ratio_abs_le {Y v y : ℝ} (_hY : 1 ≤ Y)
    (hv : 1 ≤ v) (hvY : v ≤ Y) (hy : y ∈ Icc (1 : ℝ) Y) :
    |Real.log (y / v)| ≤ Real.log Y := by
  have hv0 : 0 < v := by linarith
  have hy0 : 0 < y := by linarith [hy.1]
  rw [Real.log_div hy0.ne' hv0.ne', abs_le]
  have hly := Real.log_nonneg hy.1
  have hlv := Real.log_nonneg hv
  have hlyY := Real.log_le_log hy0 hy.2
  have hlvY := Real.log_le_log hv0 hvY
  constructor <;> linarith

private lemma log_square_integrable {a b v B : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hv : 0 < v) :
    IntervalIntegrable (fun y => (Real.log (y / v) + B) ^ 2) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (ContinuousOn.add ?_ continuousOn_const).pow
  apply Real.continuousOn_log.comp (continuousOn_id.div_const v)
  intro y hy
  exact ne_of_gt (div_pos (ha.trans_le ((uIcc_of_le hab ▸ hy).1)) hv)

private lemma log_square_integral_le {a b v B T : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hv : 0 < v) (hT : 0 ≤ T)
    (hbound : ∀ y ∈ Icc a b, |Real.log (y / v) + B| ≤ T) :
    (∫ y in a..b, (Real.log (y / v) + B) ^ 2) ≤ (b - a) * T ^ 2 := by
  calc
    _ ≤ ∫ _y in a..b, T ^ 2 := by
      apply intervalIntegral.integral_mono_on hab (log_square_integrable ha hab hv)
        intervalIntegrable_const
      intro y hy
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hT).mpr (hbound y hy)
    _ = _ := by simp

/-- The uniform cumulative formula supplies a fourth-moment upper bound on the band. -/
theorem asymptotic_implies_band
    (E : ℝ → ℝ) (α β B : ℝ) (_hE : LocallyBoundedMeasurable E)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1)
    (hF : FourthMomentAsymptoticFor E α β B) :
    ∃ C : ℝ, FourthMomentBandBoundFor E α β C := by
  let K : ℝ := (1 + |B|) / (1 - β)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨3 * K ^ 2 + 1, by positivity, ?_⟩
  filter_upwards [hF 1 zero_lt_one, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
    with Y hF hY hlog
  intro v hvα hvβ
  obtain ⟨hv1, hvY⟩ := band_lengths hY hα hαβ hβ hvα hvβ
  have hv0 : 0 < v := by linarith
  have hY0 : 0 < Y := by linarith
  have hL := band_log_lower hY0 hv0 hvβ
  have hlogv : 0 ≤ Real.log (Y / v) := Real.log_nonneg ((one_le_div hv0).2 hvY)
  have hmain : (∫ y in (1 : ℝ)..Y, (Real.log (y / v) + B) ^ 2) ≤
      Y * (K * Real.log (Y / v)) ^ 2 := by
    apply (log_square_integral_le zero_lt_one hY hv0 (mul_nonneg hK hlogv) ?_).trans
    · exact mul_le_mul_of_nonneg_right (by linarith : Y - 1 ≤ Y) (sq_nonneg _)
    · intro y hy
      calc
        _ ≤ |Real.log (y / v)| + |B| := abs_add_le _ _
        _ ≤ Real.log Y + |B| := add_le_add (log_ratio_abs_le hY hv1 hvY hy) le_rfl
        _ ≤ (1 + |B|) * Real.log Y := by nlinarith [abs_nonneg B]
        _ ≤ K * Real.log (Y / v) := by
          dsimp [K]
          rw [div_mul_eq_mul_div]
          apply (le_div_iff₀ (sub_pos.mpr hβ)).2
          nlinarith [mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 1 + |B|)]
  have herror := (abs_le.mp (hF v hvα hvβ)).2
  have hm := mul_le_mul_of_nonneg_left hmain (by positivity : 0 ≤ 3 * v ^ 2)
  nlinarith only [herror, hm]

private lemma local_energy_eventually
    {E : ℝ → ℝ} {α β B₀ : ℝ} (hE : LocallyBoundedMeasurable E)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1)
    (hF : FourthMomentAsymptoticFor E α β B₀) :
    ∀ η : ℝ, 0 < η → ∀ᶠ X : ℝ in atTop,
      localFourthEnergyWindow E α β 13 X η := by
  intro η hη
  let δ : ℝ := 13 * η / 32
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (hF δ (by dsimp [δ]; positivity))
  filter_upwards [eventually_ge_atTop (2 * Y₀), eventually_ge_atTop (4 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (20 * |B₀|))]
    with X hXY hX hlarge
  intro A B hA hAB hB v hvα hvβ
  have hX0 : 0 < X := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := hA0.trans_le hAB
  have hβ0 : 0 ≤ β := (hα.trans hαβ).le
  have band (Y : ℝ) (hY : Y ∈ Icc (X / 2) (4 * X)) :
      Y ^ α ≤ v ∧ v ≤ Y ^ β := by
    constructor
    · exact (Real.rpow_le_rpow (by linarith [hY.1]) hY.2 hα.le).trans hvα
    · exact hvβ.trans (Real.rpow_le_rpow (by linarith) hY.1 hβ0)
  have hAmem : A ∈ Icc (X / 2) (4 * X) := ⟨hA, hAB.trans hB⟩
  have hBmem : B ∈ Icc (X / 2) (4 * X) := ⟨hA.trans hAB, hB⟩
  obtain ⟨hv1, hvA⟩ := band_lengths hA1 hα hαβ hβ (band A hAmem).1 (band A hAmem).2
  have hv0 : 0 < v := by linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlog4X : Real.log (4 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 4) hX]
  have logs (y : ℝ) (hy : y ∈ Icc A (4 * X)) :
      0 ≤ Real.log (y / v) ∧ Real.log (y / v) ≤ 2 * Real.log X := by
    have hy0 : 0 < y := hA0.trans_le hy.1
    exact ⟨Real.log_nonneg ((one_le_div hv0).2 (hvA.trans hy.1)),
      (Real.log_le_log (div_pos hy0 hv0)
        ((div_le_self hy0.le hv1).trans hy.2)).trans hlog4X⟩
  have hm : 3 * v ^ 2 * (∫ y in A..B, (Real.log (y / v) + B₀) ^ 2) ≤
      13 * v ^ 2 * Real.log X ^ 2 * (B - A) := by
    have hi := log_square_integral_le hA0 hAB hv0
      (show 0 ≤ 2 * Real.log X + |B₀| by positivity) (by
        intro y hy
        have hl := logs y ⟨hy.1, hy.2.trans hB⟩
        exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hl.1]; linarith [hl.2]))
    have hs : 3 * (2 * Real.log X + |B₀|) ^ 2 ≤ 13 * Real.log X ^ 2 := by
      have hh : (2 * Real.log X + |B₀|) ^ 2 ≤ ((41 / 20 : ℝ) * Real.log X) ^ 2 := by
        apply (sq_le_sq₀ (by positivity) (by positivity)).2
        linarith
      nlinarith [sq_nonneg (Real.log X)]
    calc
      _ ≤ 3 * v ^ 2 * ((B - A) * (2 * Real.log X + |B₀|) ^ 2) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = v ^ 2 * (B - A) * (3 * (2 * Real.log X + |B₀|) ^ 2) := by ring
      _ ≤ v ^ 2 * (B - A) * (13 * Real.log X ^ 2) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  have err (Y : ℝ) (hY : Y ∈ Icc A (4 * X)) :
      |(∫ x in (1 : ℝ)..Y, |increment E v x| ^ 4) -
        3 * v ^ 2 * (∫ y in (1 : ℝ)..Y, (Real.log (y / v) + B₀) ^ 2)| ≤
          16 * δ * X * v ^ 2 * Real.log X ^ 2 := by
    have hYY : Y ∈ Icc (X / 2) (4 * X) := ⟨hA.trans hY.1, hY.2⟩
    have he := hY₀ Y (by linarith [hY.1]) v (band Y hYY).1 (band Y hYY).2
    have hl := logs Y hY
    have hs : Real.log (Y / v) ^ 2 ≤ 4 * Real.log X ^ 2 := by
      nlinarith only [hl.1, hl.2,
        sq_nonneg (2 * Real.log X - Real.log (Y / v))]
    apply he.trans
    calc
      _ ≤ δ * (4 * X) * v ^ 2 * (4 * Real.log X ^ 2) := by
        gcongr
        · exact hY.2
      _ = _ := by ring
  have hi (Y : ℝ) : IntervalIntegrable (fun y => |increment E v y| ^ 4) volume 1 Y := by
    simpa only [Even.pow_abs (by decide : Even (4 : ℕ))] using
      (increment_pow_integrableOn (μ := volume) hE isCompact_uIcc
        (u := fun _ : ℝ => v) (x := fun y : ℝ => y)
        continuous_const continuous_id 4).intervalIntegrable
  have hlogi (Y : ℝ) (hY : A ≤ Y) := log_square_integrable zero_lt_one
    (hA1.trans hY) hv0 (B := B₀)
  have hid := intervalIntegral.integral_interval_sub_left (hi B) (hi A)
  have hmid := intervalIntegral.integral_interval_sub_left (hlogi B hAB) (hlogi A le_rfl)
  have hEA := (abs_le.mp (err A ⟨le_rfl, hAmem.2⟩)).1
  have hEB := (abs_le.mp (err B ⟨hAB, hB⟩)).2
  dsimp [δ] at hEA hEB
  nlinarith only [hid, hmid, hEA, hEB, hm]

/-- The same cumulative formula gives local fourth energy with constant thirteen. -/
theorem asymptotic_implies_local
    (E : ℝ → ℝ) (α β B : ℝ) (hE : LocallyBoundedMeasurable E)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1)
    (hF : FourthMomentAsymptoticFor E α β B) :
    LocalFourthEnergyFor E α β 13 := by
  classical
  let S (X : ℝ) : Set ℝ := {η | 0 ≤ η ∧ localFourthEnergyWindow E α β 13 X η}
  let r (X : ℝ) : ℝ := max 0 (sInf (S X))
  let ε (X : ℝ) : ℝ := r X + 1 / max 1 X
  have hr (X : ℝ) : 0 ≤ r X := le_max_left _ _
  have hε (X : ℝ) : 0 ≤ ε X := by dsimp [ε]; positivity
  have hb (X : ℝ) : BddBelow (S X) := ⟨0, fun _ h => h.1⟩
  have hlocal := local_energy_eventually hE hα hαβ hβ hF
  have hrt : Tendsto r atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    filter_upwards [hlocal (η / 2) (by positivity)] with X hX
    have hi : sInf (S X) ≤ η / 2 := csInf_le (hb X) ⟨by positivity, hX⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hr X)]
    exact (max_le (by positivity) hi).trans_lt (by linarith)
  have hinv : Tendsto (fun X : ℝ => 1 / max 1 X) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_atTop_mono (fun X : ℝ => le_max_right 1 X) tendsto_id)
  have hεt : Tendsto ε atTop (𝓝 0) := by
    simpa only [add_zero] using hrt.add hinv
  refine ⟨by norm_num, ε, hε, hεt, ?_⟩
  filter_upwards [hlocal 1 zero_lt_one, eventually_ge_atTop (4 : ℝ)] with X hX hX4
  have hne : (S X).Nonempty := ⟨1, zero_le_one, hX⟩
  have hpos : 0 < 1 / max 1 X := by positivity
  have hlt : sInf (S X) < ε X := by
    exact lt_of_le_of_lt (le_max_right _ _) (lt_add_of_pos_right _ hpos)
  obtain ⟨η, hη, hηε⟩ := exists_lt_of_csInf_lt hne hlt
  intro A B hA hAB hB v hvα hvβ
  have hi := hη.2 A B hA hAB hB v hvα hvβ
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 13 * v ^ 2 * Real.log X ^ 2)
  have hh := mul_le_mul_of_nonneg_right hηε.le (show 0 ≤ X by linarith)
  linarith

end
end D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FourthMomentAsymptotic
