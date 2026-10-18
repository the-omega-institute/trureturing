/- GID: D5/S3/Entropy/RenyiCombining/CachinShannonBranch
   generality: G
   mirror-B: D5/B/S3/Entropy/RenyiCombining/CachinShannonBranch
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shannon elasticity certificate for binary entropy combining. -/

import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert

/-! Strict Shannon elasticity and its multiplicative slope comparison. -/

open Set Filter
open scoped Topology

namespace D5.S3.Entropy.RenyiCombining.CachinShannonBranch

noncomputable def E (t : ℝ) : ℝ := t / ((1 - t ^ 2) * Real.artanh t)

theorem artanh_hasDerivAt {t : ℝ} (ht : t ∈ Ioo (-1) 1) :
    HasDerivAt Real.artanh (1 / (1 - t ^ 2)) t := by
  have hp : 1 + t ≠ 0 := by linarith [ht.1]
  have hm : 1 - t ≠ 0 := by linarith [ht.2]
  have hq : (1 + t) / (1 - t) ≠ 0 := div_ne_zero hp hm
  have hsq : 1 - t ^ 2 ≠ 0 := by
    rw [show 1 - t ^ 2 = (1 - t) * (1 + t) by ring]
    exact mul_ne_zero hm hp
  have hd := ((((hasDerivAt_const t 1).add (hasDerivAt_id t)).div
    ((hasDerivAt_const t 1).sub (hasDerivAt_id t)) hm).log hq).const_mul (1 / 2 : ℝ)
  have he : (fun s : ℝ => 1 / 2 * Real.log ((1 + s) / (1 - s))) =ᶠ[𝓝 t]
      Real.artanh := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact (Real.artanh_eq_half_log ⟨hs.1.le, hs.2.le⟩).symm
  convert hd.congr_of_eventuallyEq he.symm using 1
  dsimp
  field_simp [hp, hm, hsq]
  <;> ring

theorem self_le_artanh {t : ℝ} (ht : t ∈ Ioo 0 1) : t ≤ Real.artanh t := by
  have hd : ∀ s ∈ Icc (0 : ℝ) t,
      HasDerivAt (fun x => Real.artanh x - x) (1 / (1 - s ^ 2) - 1) s := by
    intro s hs
    exact (artanh_hasDerivAt ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩).sub
      (hasDerivAt_id s)
  have hm : MonotoneOn (fun x => Real.artanh x - x) (Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    intro s hs
    have hst := interior_subset hs
    rw [(hd s hst).deriv]
    have hpos : 0 < 1 - s ^ 2 := by nlinarith [hst.1, hst.2, ht.2]
    have : (1 : ℝ) ≤ 1 / (1 - s ^ 2) := (le_div_iff₀ hpos).2 (by nlinarith [sq_nonneg s])
    linarith
  have h := hm ⟨le_rfl, ht.1.le⟩ ⟨ht.1.le, le_rfl⟩ ht.1.le
  simpa using h

theorem E_hasDerivAt {t : ℝ} (ht : t ∈ Ioo 0 1) :
    HasDerivAt E (((1 + t ^ 2) * Real.artanh t - t) /
      ((1 - t ^ 2) * Real.artanh t) ^ 2) t := by
  have hp : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have ha := Real.artanh_pos ht
  have hd := (hasDerivAt_id t).div
    (((hasDerivAt_const t 1).sub (hasDerivAt_pow 2 t)).mul
      (artanh_hasDerivAt ⟨by linarith [ht.1], ht.2⟩)) (mul_pos hp ha).ne'
  convert hd using 1
  · rfl
  · dsimp
    field_simp
    <;> ring

theorem E_strictMonoOn : StrictMonoOn E (Ioo 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    (fun t ht => (E_hasDerivAt ht).continuousAt.continuousWithinAt)
  intro t ht
  have ht' := interior_subset ht
  rw [(E_hasDerivAt ht').deriv]
  apply div_pos
  · have ha := Real.artanh_pos ht'
    have hab := self_le_artanh ht'
    have hsq : 0 < t ^ 2 * Real.artanh t := mul_pos (sq_pos_of_pos ht'.1) ha
    nlinarith
  · exact sq_pos_of_pos (mul_pos (by nlinarith [ht'.1, ht'.2]) (Real.artanh_pos ht'))

theorem slope_ratio_strictAntiOn {v : ℝ} (hv : v ∈ Ioo 0 1) :
    StrictAntiOn (fun t => v * Real.artanh (v * t) / Real.artanh t) (Ioo 0 1) := by
  have hvt : ∀ t ∈ Ioo (0 : ℝ) 1, v * t ∈ Ioo (0 : ℝ) 1 := by
    intro t ht
    exact ⟨mul_pos hv.1 ht.1, by nlinarith [ht.2, mul_pos (sub_pos.mpr hv.2) ht.1]⟩
  have hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun s => v * Real.artanh (v * s) / Real.artanh s)
      (v * Real.artanh (v * t) / (t * Real.artanh t) * (E (v * t) - E t)) t := by
    intro t ht
    have h₁ := artanh_hasDerivAt (show v * t ∈ Ioo (-1 : ℝ) 1 from
      ⟨by linarith [(hvt t ht).1], (hvt t ht).2⟩)
    have h₂ := artanh_hasDerivAt (show t ∈ Ioo (-1 : ℝ) 1 from
      ⟨by linarith [ht.1], ht.2⟩)
    convert ((h₁.comp t ((hasDerivAt_id t).const_mul v)).const_mul v).div h₂
      (Real.artanh_pos ht).ne' using 1
    · rfl
    · dsimp [E]
      field_simp [hv.1.ne', ht.1.ne', (Real.artanh_pos ht).ne',
        (Real.artanh_pos (hvt t ht)).ne']
      <;> ring
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  intro t ht
  have ht' := interior_subset ht
  rw [(hd t ht').deriv]
  exact mul_neg_of_pos_of_neg
    (div_pos (mul_pos hv.1 (Real.artanh_pos (hvt t ht')))
      (mul_pos ht'.1 (Real.artanh_pos ht')))
    (sub_neg.mpr (E_strictMonoOn (hvt t ht') ht' (by nlinarith [hv.2, ht'.1])))

theorem binEntropy_bias_hasDerivAt {t : ℝ} (ht : t ∈ Ioo 0 1) :
    HasDerivAt (fun s : ℝ => Real.binEntropy ((1 - s) / 2)) (-Real.artanh t) t := by
  have hp : (1 - t) / 2 ≠ 0 := by linarith [ht.2]
  have hq : (1 - t) / 2 ≠ 1 := by linarith [ht.1]
  have h₁ : 1 + t ≠ 0 := by linarith [ht.1]
  have h₂ : 1 - t ≠ 0 := by linarith [ht.2]
  have hd := (Real.hasDerivAt_binEntropy hp hq).comp t
    (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).div_const 2)
  convert hd using 1
  · rfl
  · rw [show 1 - (1 - t) / 2 = (1 + t) / 2 by ring,
    Real.artanh_eq_half_log ⟨by linarith [ht.1], ht.2.le⟩,
    Real.log_div h₁ h₂, Real.log_div h₁ (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_div h₂ (by norm_num : (2 : ℝ) ≠ 0)]
    ring

end D5.S3.Entropy.RenyiCombining.CachinShannonBranch
