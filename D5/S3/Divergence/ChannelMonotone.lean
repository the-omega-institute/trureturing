/- GID: D5/S3/Divergence/ChannelMonotone
   generality: G
   mirror-B: D5/B/S3/Divergence/ChannelMonotone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove finite-channel monotonicity for classical KL divergence. -/

/- Library-search audit trail (2026-08-09):
   * Local pinned-mathlib grep terms: `dataProcessing`, `data_processing`,
     `klDiv.*(map|comp|mono|le)`, `map.*klDiv`, `PMF.*kl`, `toReal_klDiv`,
     `relativeEntropy`, and `Kullback.*Leibler`.
   * `Mathlib.InformationTheory.KullbackLeibler.ChainRule` provides the measure-valued
     identities `InformationTheory.klDiv_compProd_eq_add` and
     `InformationTheory.klDiv_compProd_left`; its divergence takes values in `ℝ≥0∞`.
   * `Mathlib.InformationTheory.KullbackLeibler.Basic` provides `toReal_klDiv` integral
     identities, but no pinned theorem was found that identifies those integrals with the
     repository's real-valued finite sum or states the requested finite-channel inequality.
   * The proof below therefore composes the repository's finite-sum data-processing identity
     with its finite-sum Gibbs inequality, without rebuilding either result.
-/

import D5.S3.Divergence.ClassicalDPI
import D5.S3.Divergence.GrandmotherTheorem

namespace D5.S3.Divergence.ChannelMonotone

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.GrandmotherTheorem

/-- Applying a strictly positive finite channel cannot increase classical KL divergence. -/
theorem kl_divergence_channel_le
    {X Y : Type*} [Fintype X] [Nonempty X] [Fintype Y]
    (p q : X → ℝ) (W : X → Y → ℝ)
    (hp : (∀ x, 0 < p x) ∧ ∑ x, p x = 1)
    (hq : (∀ x, 0 < q x) ∧ ∑ x, q x = 1)
    (hW : (∀ x y, 0 < W x y) ∧ ∀ x, ∑ y, W x y = 1) :
    klDivergence (channelOutput W p) (channelOutput W q) ≤ klDivergence p q := by
  classical
  rw [classical_dpi_identity p q W hp hq hW]
  have hOutputPPos (y : Y) : 0 < channelOutput W p y := by
    rw [channelOutput]
    refine Finset.sum_pos' (fun x _ => (mul_pos (hp.1 x) (hW.1 x y)).le) ?_
    let x : X := Classical.choice inferInstance
    exact ⟨x, Finset.mem_univ x, mul_pos (hp.1 x) (hW.1 x y)⟩
  have hOutputQPos (y : Y) : 0 < channelOutput W q y := by
    rw [channelOutput]
    refine Finset.sum_pos' (fun x _ => (mul_pos (hq.1 x) (hW.1 x y)).le) ?_
    let x : X := Classical.choice inferInstance
    exact ⟨x, Finset.mem_univ x, mul_pos (hq.1 x) (hW.1 x y)⟩
  have hPosteriorPPos (y : Y) (x : X) : 0 < posterior W p y x := by
    exact div_pos (mul_pos (hp.1 x) (hW.1 x y)) (hOutputPPos y)
  have hPosteriorQPos (y : Y) (x : X) : 0 < posterior W q y x := by
    exact div_pos (mul_pos (hq.1 x) (hW.1 x y)) (hOutputQPos y)
  have hPosteriorSumP (y : Y) : ∑ x, posterior W p y x = 1 := by
    simp only [posterior]
    rw [← Finset.sum_div, ← channelOutput]
    exact div_self (ne_of_gt (hOutputPPos y))
  have hPosteriorSumQ (y : Y) : ∑ x, posterior W q y x = 1 := by
    simp only [posterior]
    rw [← Finset.sum_div, ← channelOutput]
    exact div_self (ne_of_gt (hOutputQPos y))
  apply le_add_of_nonneg_right
  refine Finset.sum_nonneg ?_
  intro y _
  apply mul_nonneg (hOutputPPos y).le
  apply kl_divergence_nonneg
  · exact ⟨fun x => (hPosteriorPPos y x).le, hPosteriorSumP y⟩
  · exact ⟨fun x => (hPosteriorQPos y x).le, hPosteriorSumQ y⟩
  · intro x hqx
    exact (ne_of_gt (hPosteriorQPos y x) hqx).elim

end D5.S3.Divergence.ChannelMonotone
