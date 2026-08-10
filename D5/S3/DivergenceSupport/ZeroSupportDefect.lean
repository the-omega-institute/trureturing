/- GID: D5/S3/DivergenceSupport/ZeroSupportDefect
   generality: G
   mirror-B: D5/B/S3/DivergenceSupport/ZeroSupportDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Deduce nonnegativity of the finite classical DPI defect on general support. -/

/- Library-search audit trail (2026-08-10):
   * Repository search terms: `dpi_defect_nonneg`, `classical_dpi_identity_zero_support`,
     `zero_output_weighted_posterior_kl`, and `kl_divergence_nonneg`.
   * `ZeroSupportDPI.classical_dpi_identity_zero_support` is the exact general-support chain
     identity, and `GrandmotherTheorem.kl_divergence_nonneg` is the existing finite Gibbs
     inequality under discrete absolute continuity. This file composes those frozen results.
   * Pinned mathlib search found the measure-valued nonnegativity results in
     `Mathlib.InformationTheory.KullbackLeibler.Basic`, but no bridge to the repository's
     real-valued finite sum beyond the already frozen `kl_divergence_nonneg`.
-/

import D5.S3.DivergenceSupport.ZeroSupportDPI
import D5.S3.Divergence.GrandmotherTheorem

namespace D5.S3.DivergenceSupport.ZeroSupportDefect

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.GrandmotherTheorem
open D5.S3.DivergenceSupport.ZeroSupportDPI

/-- The loss of finite classical KL divergence under a nonnegative row-stochastic channel is
nonnegative for normalized masses satisfying discrete absolute continuity `p << q`. -/
theorem dpi_defect_nonneg_zero_support {X Y : Type*}
    [Fintype X] [Fintype Y]
    (p q : X -> Real) (W : X -> Y -> Real)
    (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1)
    (hq : (∀ x, 0 ≤ q x) ∧ ∑ x, q x = 1)
    (hac : ∀ x, q x = 0 → p x = 0)
    (hW : (∀ x y, 0 ≤ W x y) ∧ ∀ x, ∑ y, W x y = 1) :
    klDivergence p q -
        klDivergence (channelOutput W p) (channelOutput W q) ≥ 0 := by
  classical
  have hOutputPNonneg (y : Y) : 0 ≤ channelOutput W p y := by
    rw [channelOutput]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hp.1 x) (hW.1 x y)
  have hOutputQNonneg (y : Y) : 0 ≤ channelOutput W q y := by
    rw [channelOutput]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hq.1 x) (hW.1 x y)
  have hOutputAC (y : Y) (hy : channelOutput W q y = 0) :
      channelOutput W p y = 0 :=
    channel_output_absolute_continuity p q W hq.1 hac hW.1 y hy
  have hTermNonneg (y : Y) :
      0 ≤ channelOutput W p y *
        klDivergence (posterior W p y) (posterior W q y) := by
    by_cases hOutputPZero : channelOutput W p y = 0
    · rw [zero_output_weighted_posterior_kl p q W y hOutputPZero]
    have hOutputPPos : 0 < channelOutput W p y :=
      lt_of_le_of_ne (hOutputPNonneg y) (Ne.symm hOutputPZero)
    have hOutputQNe : channelOutput W q y ≠ 0 := by
      intro hOutputQZero
      exact hOutputPZero (hOutputAC y hOutputQZero)
    have hOutputQPos : 0 < channelOutput W q y :=
      lt_of_le_of_ne (hOutputQNonneg y) (Ne.symm hOutputQNe)
    have hPosteriorMass (r : X -> Real) (hr : ∀ x, 0 ≤ r x)
        (hOutputPos : 0 < channelOutput W r y) :
        (∀ x, 0 ≤ posterior W r y x) ∧ ∑ x, posterior W r y x = 1 := by
      refine ⟨fun x => div_nonneg (mul_nonneg (hr x) (hW.1 x y)) hOutputPos.le, ?_⟩
      simp only [posterior, ← Finset.sum_div]
      exact div_self (ne_of_gt hOutputPos)
    have hPosteriorAC :
        ∀ x, posterior W q y x = 0 → posterior W p y x = 0 := by
      intro x hPosteriorQZero
      have hJointQZero : q x * W x y = 0 :=
        (div_eq_zero_iff.mp (by
          simpa only [posterior] using hPosteriorQZero)).resolve_right hOutputQNe
      rcases mul_eq_zero.mp hJointQZero with hqx | hWxy
      · simp [posterior, hac x hqx]
      · simp [posterior, hWxy]
    apply mul_nonneg hOutputPPos.le
    exact kl_divergence_nonneg
      (posterior W p y) (posterior W q y)
      (hPosteriorMass p hp.1 hOutputPPos)
      (hPosteriorMass q hq.1 hOutputQPos)
      hPosteriorAC
  rw [classical_dpi_identity_zero_support p q W hp hq hac hW]
  have hPosteriorSumNonneg :
      0 ≤ ∑ y, channelOutput W p y *
        klDivergence (posterior W p y) (posterior W q y) :=
    Finset.sum_nonneg fun y _ => hTermNonneg y
  linarith

end D5.S3.DivergenceSupport.ZeroSupportDefect
