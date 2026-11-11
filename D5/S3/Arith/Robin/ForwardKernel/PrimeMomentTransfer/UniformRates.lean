/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform transfer error rates decay over polynomial length bands. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Uniform logarithmic and arithmetic error bounds for polynomial length bands. -/

open Set Filter
open scoped Topology

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

theorem transfer_epsilon_exists (β : ℝ) (hβ : β < 1 / 4) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 - 2 * β := by
  refine ⟨(1 / 2 - 2 * β) / 2, ?_, ?_⟩ <;> linarith

theorem sqrt_rate (α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ) :
    ∀ᶠ N : ℝ in atTop, ∀ H : ℝ, N ^ α ≤ H →
      Real.sqrt (Real.log N / H) ≤ δ := by
  have hlim : Tendsto (fun N : ℝ => Real.sqrt (Real.log N / N ^ α))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      (isLittleO_log_rpow_atTop hα).tendsto_div_nhds_zero.sqrt
  filter_upwards [hlim.eventually_le_const hδ, eventually_ge_atTop (1 : ℝ)]
    with N hsmall hN H hH
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  exact (Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (Real.log_nonneg hN)
    (Real.rpow_pos_of_pos hNpos α) hH)).trans hsmall

theorem arithmetic_rate_three (β ε δ : ℝ) (hβ : 0 < β) (_hε : 0 < ε)
    (hεβ : ε < 1 / 2 - (3 / 2) * β) (hδ : 0 < δ) :
    ∀ᶠ N : ℝ in atTop, ∀ H : ℝ, 1 ≤ H → H ≤ N ^ β →
      N ^ (-1 / 2 + ε) * H ^ (3 / 2 : ℝ) * (Real.log N) ^ (-3 / 2 : ℝ) ≤ δ := by
  have hdecay : 0 < 1 / 2 - ε - β * (3 / 2) := by linarith
  have hsmall := (tendsto_rpow_neg_atTop hdecay).eventually_le_const hδ
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with N hsmall hN hlog H hH hHβ
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hHpow : H ^ (3 / 2 : ℝ) ≤ (N ^ β) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hHβ (by norm_num)
  have hlogpow : (Real.log N) ^ (-3 / 2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hlog (by norm_num)
  calc
    N ^ (-1 / 2 + ε) * H ^ (3 / 2 : ℝ) * (Real.log N) ^ (-3 / 2 : ℝ)
        ≤ N ^ (-1 / 2 + ε) * H ^ (3 / 2 : ℝ) :=
      mul_le_of_le_one_right (by positivity) hlogpow
    _ ≤ N ^ (-1 / 2 + ε) * (N ^ β) ^ (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hHpow (Real.rpow_nonneg hNpos.le _)
    _ = N ^ (-(1 / 2 - ε - β * (3 / 2))) := by
      rw [← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
      congr 1
      ring
    _ ≤ δ := hsmall

theorem arithmetic_rate_four (β ε δ : ℝ) (_hε : 0 < ε)
    (hεβ : ε < 1 / 2 - 2 * β) (hδ : 0 < δ) :
    ∀ᶠ N : ℝ in atTop, ∀ H : ℝ, 0 ≤ H → H ≤ N ^ β →
      N ^ (-1 / 2 + ε) * H ^ 2 * (Real.log N) ^ (-2 : ℝ) ≤ δ := by
  have hdecay : 0 < 1 / 2 - ε - β * 2 := by linarith
  have hsmall := (tendsto_rpow_neg_atTop hdecay).eventually_le_const hδ
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with N hsmall hN hlog H hH hHβ
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hHpow : H ^ 2 ≤ (N ^ β) ^ 2 := pow_le_pow_left₀ hH hHβ 2
  have hlogpow : (Real.log N) ^ (-2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hlog (by norm_num)
  calc
    N ^ (-1 / 2 + ε) * H ^ 2 * (Real.log N) ^ (-2 : ℝ)
        ≤ N ^ (-1 / 2 + ε) * H ^ 2 :=
      mul_le_of_le_one_right (by positivity) hlogpow
    _ ≤ N ^ (-1 / 2 + ε) * (N ^ β) ^ 2 :=
      mul_le_mul_of_nonneg_left hHpow (Real.rpow_nonneg hNpos.le _)
    _ = N ^ (-(1 / 2 - ε - β * 2)) := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
      congr 1
      norm_num
      ring
    _ ≤ δ := hsmall

theorem inverse_log_rate (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℝ in atTop, 1 / Real.log N ≤ δ := by
  simpa only [one_div, Pi.inv_apply] using
    Real.tendsto_log_atTop.inv_tendsto_atTop.eventually_le_const hδ

theorem antitone_modulus_rate (η : ℝ → ℝ) (α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ)
    (hanti : AntitoneOn η (Ici 2)) (hlim : Tendsto η atTop (𝓝 0)) :
    ∀ᶠ N : ℝ in atTop, ∀ H : ℝ, N ^ α ≤ H →
      η H ≤ η (N ^ α) ∧ η H ≤ δ := by
  have hpow := tendsto_rpow_atTop hα
  filter_upwards [hpow.eventually_ge_atTop 2, (hlim.comp hpow).eventually_le_const hδ]
    with N hN hsmall H hH
  have hηH : η H ≤ η (N ^ α) := hanti hN (hN.trans hH) hH
  exact ⟨hηH, hηH.trans hsmall⟩

theorem cell_rate (β δ : ℝ) (k : ℕ) (_hβ0 : 0 ≤ β) (hβ : β < 1 / 2)
    (hk : k ≤ 4) (hδ : 0 < δ) :
    ∀ᶠ N : ℝ in atTop, ∀ H : ℝ, 1 ≤ H → H ≤ N ^ β →
      (H * Real.log N) ^ ((k : ℝ) / 2) / N ≤ δ := by
  have hdecay : 0 < 1 - β * 2 := by linarith
  have hlim : Tendsto (fun N : ℝ => (Real.log N) ^ 2 / N ^ (1 - β * 2))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hdecay).tendsto_div_nhds_zero
  filter_upwards [hlim.eventually_le_const hδ, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with N hsmall hN hlog H hH hHβ
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hHL : 1 ≤ H * Real.log N := one_le_mul_of_one_le_of_one_le hH hlog
  have hk' : (k : ℝ) / 2 ≤ 2 := by
    have hkR : (k : ℝ) ≤ 4 := by exact_mod_cast hk
    linarith
  have hpow : (H * Real.log N) ^ ((k : ℝ) / 2) ≤ (H * Real.log N) ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hHL hk'
  have hmul : H * Real.log N ≤ N ^ β * Real.log N :=
    mul_le_mul_of_nonneg_right hHβ (by linarith)
  calc
    (H * Real.log N) ^ ((k : ℝ) / 2) / N ≤ (H * Real.log N) ^ 2 / N :=
      div_le_div_of_nonneg_right hpow hNpos.le
    _ ≤ (N ^ β * Real.log N) ^ 2 / N :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hmul 2) hNpos.le
    _ = (Real.log N) ^ 2 / N ^ (1 - β * 2) := by
      rw [mul_pow, ← Real.rpow_natCast (N ^ β) 2, ← Real.rpow_mul hNpos.le,
        Real.rpow_sub hNpos, Real.rpow_one]
      norm_num
      field_simp
    _ ≤ δ := hsmall

theorem range_geometry (α β M : ℝ) (hα : 0 < α) (hβ : β < 1) (hM : 0 < M) :
    ∀ᶠ N : ℝ in atTop, 2 ≤ N ∧ 1 ≤ Real.log N ∧
      ∀ H : ℝ, N ^ α ≤ H → H ≤ N ^ β → 2 ≤ H ∧ H ≤ N ∧ M * H ≤ N := by
  have hlim : Tendsto (fun N : ℝ => M * N ^ (-(1 - β))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (sub_pos.mpr hβ)).const_mul M
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (tendsto_rpow_atTop hα).eventually_ge_atTop 2,
    hlim.eventually_le_const zero_lt_one] with N hN hlog hlow hsmall
  have hNpos : 0 < N := by linarith
  have hMN : M * N ^ β ≤ N := by
    rw [neg_sub, Real.rpow_sub hNpos, Real.rpow_one, ← mul_div_assoc] at hsmall
    exact (div_le_one hNpos).mp hsmall
  refine ⟨hN, hlog, ?_⟩
  intro H hHlo hHhi
  have hpow : N ^ β ≤ N := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ N) hβ.le
  exact ⟨hlow.trans hHlo, hHhi.trans hpow,
    (mul_le_mul_of_nonneg_left hHhi hM.le).trans hMN⟩

end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
