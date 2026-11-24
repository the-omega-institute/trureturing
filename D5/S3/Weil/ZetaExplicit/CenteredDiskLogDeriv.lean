/- GID: D5/S3/Weil/ZetaExplicit/CenteredDiskLogDeriv
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaExplicit/CenteredDiskLogDeriv
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Centering the logarithmic derivative gives a remainder linear in the evaluation radius. -/

import D5.S3.Weil.ZetaExplicit.Landau
import Mathlib.Analysis.Complex.Schwarz

noncomputable section

namespace Zeta23.WeilEF

open Metric Set

/-- The difference of the two logarithmic derivatives, after subtracting the corresponding
finite zero sums, has an error bounded by `179180000 * ‖z‖ * Real.log B`. -/
theorem logDeriv_partial_fraction_unit_centered {f : ℂ → ℂ} {B : ℝ}
    (hfa : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1)) (hf0 : f 0 = 1)
    (hB2 : 2 ≤ B) (hfB : ∀ w : ℂ, ‖w‖ ≤ 24 / 25 → ‖f w‖ ≤ B) :
    ∃ Z : Finset ℂ, (↑Z : Set ℂ) = SetOfZeros (22 / 25) f ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 / 4 → f z ≠ 0 →
        ‖(logDeriv f z - logDeriv f 0) -
          ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)) -
            ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (0 - ρ))‖ ≤
          179180000 * ‖z‖ * Real.log B := by
  have hf0ne : f 0 ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hr : (22 / 25 : ℝ) < 1 := by norm_num
  have hfin := finite_SetOfZeros hfa hf0ne
  have hfinr := finiteSetOfZeros_mono hr hfin
  refine ⟨hfinr.toFinset, hfinr.coe_toFinset, ?_⟩
  let h := logDeriv (Cf (22 / 25) f)
  have hCfa := CfAnalytic (by norm_num : (22 / 25 : ℝ) < 9 / 10)
    (by norm_num) hfa hf0ne
  have hdiff : DifferentiableOn ℂ h (ball 0 (1 / 2)) := by
    intro w hw
    have hwn := mem_ball_zero_iff.mp hw
    have ha := hCfa w (mem_closedBall_zero_iff.mpr (by linarith))
    have hne := Cf_ne_zero hfa hf0ne hr hfin (z := w) (by linarith)
    exact (ha.deriv.div ha hne).differentiableAt.differentiableWithinAt
  have hbound : ∀ w : ℂ, ‖w‖ ≤ 83 / 100 → ‖h w‖ ≤ 44795000 * Real.log B :=
    fun _ hw => norm_logDeriv_Cf_le hfa hf0 hfin hB2 hfB hw
  have hmaps : MapsTo h (ball 0 (1 / 2)) (closedBall (h 0) (2 * (44795000 * Real.log B))) := by
    intro w hw
    have hwn := mem_ball_zero_iff.mp hw
    rw [mem_closedBall, dist_eq_norm]
    calc
      ‖h w - h 0‖ ≤ ‖h w‖ + ‖h 0‖ := norm_sub_le _ _
      _ ≤ 2 * (44795000 * Real.log B) := by
        simpa only [two_mul] using add_le_add (hbound w (by linarith)) (hbound 0 (by norm_num))
  intro z hz hfz
  have hzball : z ∈ ball (0 : ℂ) (1 / 2) := mem_ball_zero_iff.mpr (by linarith)
  have hSchwarz := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiff hmaps hzball
  rw [dist_eq_norm, dist_zero_right] at hSchwarz
  have hsplitz := logDeriv_split hfa hf0ne hr hfin (z := z) (by linarith) hfz
  have hsplit0 := logDeriv_split hfa hf0ne hr hfin (z := 0) (by norm_num) hf0ne
  calc
    _ = ‖h z - h 0‖ := by
      congr 1
      rw [hsplitz, hsplit0]
      dsimp only [h, hfinr]
      abel
    _ ≤ (2 * (44795000 * Real.log B)) / (1 / 2) * ‖z‖ := hSchwarz
    _ = 179180000 * ‖z‖ * Real.log B := by ring

end Zeta23.WeilEF
