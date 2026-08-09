/- GID: D5/S3/Divergence/DpiDefect
   generality: G
   mirror-B: D5/B/S3/Divergence/DpiDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Deduce nonnegativity of the finite classical data-processing defect. -/

import D5.S3.Divergence.ClassicalDPI
import D5.S3.Divergence.GrandmotherTheorem

namespace D5.S3.Divergence.DpiDefect

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.GrandmotherTheorem

/-- The loss of finite classical KL divergence under a strictly positive channel is nonnegative. -/
theorem dpi_defect_nonneg {X Y : Type*}
    [Fintype X] [Nonempty X] [Fintype Y]
    (p q : X → ℝ) (W : X → Y → ℝ)
    (hp : (∀ x, 0 < p x) ∧ ∑ x, p x = 1)
    (hq : (∀ x, 0 < q x) ∧ ∑ x, q x = 1)
    (hW : (∀ x y, 0 < W x y) ∧ ∀ x, ∑ y, W x y = 1) :
    klDivergence p q -
        klDivergence (channelOutput W p) (channelOutput W q) ≥ 0 := by
  classical
  have hOutputPos (r : X → ℝ) (hr : ∀ x, 0 < r x) (y : Y) :
      0 < channelOutput W r y := by
    rw [channelOutput]
    exact Finset.sum_pos' (fun x _ => (mul_pos (hr x) (hW.1 x y)).le)
      ⟨Classical.choice inferInstance, Finset.mem_univ _,
        mul_pos (hr _) (hW.1 _ y)⟩
  have hPosteriorMass (r : X → ℝ) (hr : ∀ x, 0 < r x) (y : Y) :
      (∀ x, 0 ≤ posterior W r y x) ∧ ∑ x, posterior W r y x = 1 := by
    refine ⟨fun x => (div_pos (mul_pos (hr x) (hW.1 x y)) (hOutputPos r hr y)).le, ?_⟩
    simp only [posterior, ← Finset.sum_div]
    exact div_self (ne_of_gt (hOutputPos r hr y))
  have hPosteriorNonneg (y : Y) :
      0 ≤ klDivergence (posterior W p y) (posterior W q y) := by
    apply kl_divergence_nonneg _ _ (hPosteriorMass p hp.1 y) (hPosteriorMass q hq.1 y)
    intro x hzero
    exact (ne_of_gt (div_pos (mul_pos (hq.1 x) (hW.1 x y)) (hOutputPos q hq.1 y)) hzero).elim
  rw [classical_dpi_identity p q W hp hq hW]
  exact sub_nonneg.mpr (le_add_of_nonneg_right (Finset.sum_nonneg fun y _ =>
    mul_nonneg (hOutputPos p hp.1 y).le (hPosteriorNonneg y)))

end D5.S3.Divergence.DpiDefect
