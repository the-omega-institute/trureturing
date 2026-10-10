/- GID: D5/S3/Quantum/Petz/DittmannLemmaFourComplete
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict swap inequality and the four literal statements of Dittmann Lemma 4. -/

import D5.S3.Quantum.Petz.SwapRepresentation
import D5.S3.Quantum.Petz.DensityPositivity
import D5.S3.Quantum.Petz.DittmannLemmaFour

namespace D5.S3.Quantum.Petz.DittmannLemmaFourComplete

open Set MeasureTheory
open D5.S3.Quantum.Petz.KernelSmoothness
open D5.S3.Quantum.Petz.StieltjesDensity
open D5.S3.Quantum.Petz.DensityPositivity
open D5.S3.Quantum.Petz.SwapRepresentation
open D5.S3.Quantum.Petz.DittmannLemmaFour

/-- Dittmann (64) is strict for ordered positive nodes; `hs1` differentiates the first slot. -/
theorem dittmann64 {x y lam : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hlam : 0 < lam) (hxy : x < y) :
    0 < hs1 x y lam - hs1 y x lam := by
  obtain ⟨hi, he⟩ := hs1_sub_swap_integral hx hy hlam
  rw [he]
  apply mul_pos (sub_pos.mpr hxy)
  have hp : ∀ s : ℝ, 0 < s →
      0 < (x+y+2*s)/((x+s)^2*(y+s)^2)*rho (x+y+s) lam s := by
    intro s hs
    exact mul_pos (div_pos (by positivity) (by positivity))
      (rho_pos (by positivity) hlam hs)
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs; exact (hp s hs).le)
    hi).mpr
  have hsub : Ioo (1 : ℝ) 2 ⊆
      Function.support (fun s => (x+y+2*s)/((x+s)^2*(y+s)^2)*rho (x+y+s) lam s) ∩
        Ioi 0 := by
    intro s hs
    have hs0 : 0 < s := lt_trans zero_lt_one hs.1
    exact ⟨(hp s hs0).ne', hs0⟩
  exact (show 0 < volume (Ioo (1 : ℝ) 2) by norm_num).trans_le (measure_mono hsub)

/-- Literal (64), retaining the unused positive auxiliary parameter `mu`. -/
theorem claim64 : ∀ x y lam mu : ℝ, 0 < x → 0 < y → 0 < lam → 0 < mu → x < y →
    0 ≤ hs1 x y lam - hs1 y x lam := by
  intro x y lam mu hx hy hlam hmu hxy
  exact (dittmann64 hx hy hlam hxy).le

/-- Dittmann Lemma 4, with the original functions and all four literal quantifier lists. -/
theorem lemma4 :
    (∀ x y lam mu : ℝ, 0 < x → 0 < y → 0 < lam → 0 < mu → x < y →
      0 ≤ 2 * hs1 x x y - hs1 y x x - 2 * hs1 y x y + hs1 x y y) ∧
    (∀ x y lam mu : ℝ, 0 < x → 0 < y → 0 < lam → 0 < mu → x < y →
      0 ≤ hs1 x x lam - hs1 y y lam) ∧
    (∀ x y lam mu : ℝ, 0 < x → 0 < y → 0 < lam → 0 < mu → x < y →
      0 ≤ hs1 x y lam - hs1 y x lam) ∧
    (∀ x y lam mu : ℝ, 0 < x → 0 < y → 0 < lam → 0 < mu → x < y →
      0 ≤ hs1 x lam mu - hs1 y lam mu) :=
  ⟨claim62, claim63, claim64, claim65⟩

end D5.S3.Quantum.Petz.DittmannLemmaFourComplete
