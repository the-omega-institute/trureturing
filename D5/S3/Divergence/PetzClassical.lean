/- GID: D5/S3/Divergence/PetzClassical
   generality: G
   mirror-B: D5/B/S3/Divergence/PetzClassical
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize zero classical DPI defect by equality of posteriors on output support. -/

/- Library-search audit trail (2026-08-08):
   * Local pinned-mathlib grep terms: `sum_eq_zero_iff_of_nonneg`,
     `Fintype.sum_eq_zero_iff_of_nonneg`, `mul_eq_zero`, and `Finset.sum_div`.
   * `Finset.sum_eq_zero_iff_of_nonneg` is the exact finite-sum criterion needed to pass from
     a zero weighted posterior-divergence sum to pointwise zero summands; it is reused directly.
   * The divergence, channel output, posterior, DPI identity, KL nonnegativity theorem, and Gibbs
     equality theorem are imported from the three repository sources below. This file neither
     redefines those objects nor repeats their proofs.
   * The strict `hp`, `hq`, and `hW` hypotheses of `ClassicalDPI` make every output mass and every
     posterior coordinate positive. They therefore supply normalization and absolute continuity
     for each invocation of the existing KL theorems.
-/

import D5.S3.Divergence.ClassicalDPI
import D5.S3.Divergence.GrandmotherTheorem
import D5.S3.Divergence.GibbsEquality

namespace D5.S3.Divergence.PetzClassical

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.GrandmotherTheorem
open D5.S3.Divergence.GibbsEquality

/-- The classical DPI defect vanishes exactly when the input posteriors agree at every output
letter in the support of the output distribution induced by `p`. -/
theorem dpi_defect_zero_iff_posteriors_eq {X Y : Type*}
    [Fintype X] [Nonempty X] [Fintype Y]
    (p q : X → ℝ) (W : X → Y → ℝ)
    (hp : (∀ x, 0 < p x) ∧ ∑ x, p x = 1)
    (hq : (∀ x, 0 < q x) ∧ ∑ x, q x = 1)
    (hW : (∀ x y, 0 < W x y) ∧ ∀ x, ∑ y, W x y = 1) :
    klDivergence p q -
        klDivergence (channelOutput W p) (channelOutput W q) = 0 ↔
      ∀ y, 0 < channelOutput W p y →
        posterior W p y = posterior W q y := by
  classical
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
  have hPosteriorPSum (y : Y) : ∑ x, posterior W p y x = 1 := by
    simp only [posterior, ← Finset.sum_div]
    exact div_self (ne_of_gt (hOutputPPos y))
  have hPosteriorQSum (y : Y) : ∑ x, posterior W q y x = 1 := by
    simp only [posterior, ← Finset.sum_div]
    exact div_self (ne_of_gt (hOutputQPos y))
  have hPosteriorP (y : Y) :
      (∀ x, 0 ≤ posterior W p y x) ∧ ∑ x, posterior W p y x = 1 :=
    ⟨fun x => (hPosteriorPPos y x).le, hPosteriorPSum y⟩
  have hPosteriorQ (y : Y) :
      (∀ x, 0 ≤ posterior W q y x) ∧ ∑ x, posterior W q y x = 1 :=
    ⟨fun x => (hPosteriorQPos y x).le, hPosteriorQSum y⟩
  have hPosteriorAC (y : Y) :
      ∀ x, posterior W q y x = 0 → posterior W p y x = 0 := by
    intro x hzero
    exact (ne_of_gt (hPosteriorQPos y x) hzero).elim
  have hPosteriorDivergenceNonneg (y : Y) :
      0 ≤ klDivergence (posterior W p y) (posterior W q y) :=
    kl_divergence_nonneg
      (posterior W p y) (posterior W q y)
      (hPosteriorP y) (hPosteriorQ y) (hPosteriorAC y)
  have hTermNonneg (y : Y) :
      0 ≤ channelOutput W p y *
        klDivergence (posterior W p y) (posterior W q y) :=
    mul_nonneg (hOutputPPos y).le (hPosteriorDivergenceNonneg y)
  have hDefectIdentity :
      klDivergence p q -
          klDivergence (channelOutput W p) (channelOutput W q) =
        ∑ y, channelOutput W p y *
          klDivergence (posterior W p y) (posterior W q y) := by
    rw [classical_dpi_identity p q W hp hq hW]
    ring
  constructor
  · intro hzero
    have hsumZero :
        ∑ y, channelOutput W p y *
            klDivergence (posterior W p y) (posterior W q y) = 0 := by
      rw [← hDefectIdentity]
      exact hzero
    have hall : ∀ y ∈ Finset.univ,
        channelOutput W p y *
            klDivergence (posterior W p y) (posterior W q y) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hTermNonneg y).mp hsumZero
    intro y hy
    have hDivergenceZero :
        klDivergence (posterior W p y) (posterior W q y) = 0 :=
      (mul_eq_zero.mp (hall y (Finset.mem_univ y))).resolve_left (ne_of_gt hy)
    exact (kl_divergence_eq_zero_iff
      (posterior W p y) (posterior W q y)
      (hPosteriorP y) (hPosteriorQ y) (hPosteriorAC y)).mp hDivergenceZero
  · intro hposteriors
    rw [hDefectIdentity]
    apply Finset.sum_eq_zero
    intro y _
    have hDivergenceZero :
        klDivergence (posterior W p y) (posterior W q y) = 0 :=
      (kl_divergence_eq_zero_iff
        (posterior W p y) (posterior W q y)
        (hPosteriorP y) (hPosteriorQ y) (hPosteriorAC y)).mpr
          (hposteriors y (hOutputPPos y))
    rw [hDivergenceZero, mul_zero]

end D5.S3.Divergence.PetzClassical
