/- GID: D5/S3/DivergenceSupport/ZeroSupportDefectEquality
   generality: G
   mirror-B: D5/B/S3/DivergenceSupport/ZeroSupportDefectEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize vanishing of the finite classical DPI defect on general support. -/

/- Library-search and scope audit (2026-08-14):
   * Repository searches for `dpi_defect`, zero or vanishing defect terms, weighted posterior
     terms, and posterior equality found no zero-support criterion. The existing
     `PetzClassical.dpi_defect_zero_iff_posteriors_eq` assumes strict positivity of both masses
     and every channel entry, so it does not cover the support boundary treated here.
   * Pinned mathlib provides `Finset.sum_eq_zero_iff_of_nonneg`, whose conclusion makes every
     member summand zero. Its `Fintype` companion instead concludes that the summand function is
     the zero function; `Finset.sum_eq_zero` supplies only the converse construction. No pinned
     theorem specialized to this repository's weighted posterior sum was found.
   * The proofs consume the frozen zero-support chain identity, output absolute continuity,
     zero-output convention, Gibbs nonnegativity argument, and KL equality characterization.

   The results below characterize equality only through posterior coincidence on positive output
   mass. They establish neither a recovery map nor Petz sufficiency, and they do not assert that
   the condition can be checked from `p`, `q`, and `W` without computing the posteriors.
-/

import D5.S3.DivergenceSupport.ZeroSupportDefect
import D5.S3.Divergence.GibbsEquality

namespace D5.S3.DivergenceSupport.ZeroSupportDefectEquality

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.GrandmotherTheorem
open D5.S3.Divergence.GibbsEquality
open D5.S3.DivergenceSupport.ZeroSupportDPI

/-- The classical DPI defect vanishes exactly when every weighted posterior KL term vanishes. -/
theorem dpi_defect_eq_zero_iff_weighted_posterior_kl_zero {X Y : Type*}
    [Fintype X] [Fintype Y]
    (p q : X → ℝ) (W : X → Y → ℝ)
    (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1)
    (hq : (∀ x, 0 ≤ q x) ∧ ∑ x, q x = 1)
    (hac : ∀ x, q x = 0 → p x = 0)
    (hW : (∀ x y, 0 ≤ W x y) ∧ ∀ x, ∑ y, W x y = 1) :
    klDivergence p q -
        klDivergence (channelOutput W p) (channelOutput W q) = 0 ↔
      ∀ y, channelOutput W p y *
        klDivergence (posterior W p y) (posterior W q y) = 0 := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
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
    have hPosteriorMass (r : X → ℝ) (hr : ∀ x, 0 ≤ r x)
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
    exact mul_nonneg hOutputPPos.le (kl_divergence_nonneg
      (posterior W p y) (posterior W q y)
      (hPosteriorMass p hp.1 hOutputPPos)
      (hPosteriorMass q hq.1 hOutputQPos)
      hPosteriorAC)
  have hDefectIdentity :
      klDivergence p q -
          klDivergence (channelOutput W p) (channelOutput W q) =
        ∑ y, channelOutput W p y *
          klDivergence (posterior W p y) (posterior W q y) := by
    rw [classical_dpi_identity_zero_support p q W hp hq hac hW]
    ring
  rw [hDefectIdentity]
  simpa using
    (Finset.sum_eq_zero_iff_of_nonneg fun y (_ : y ∈ Finset.univ) => hTermNonneg y)

/-- The classical DPI defect vanishes exactly when each output has zero mass under `p` or its
two posterior mass functions agree. -/
theorem dpi_defect_eq_zero_iff_zero_output_or_posteriors_eq {X Y : Type*}
    [Fintype X] [Fintype Y]
    (p q : X → ℝ) (W : X → Y → ℝ)
    (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1)
    (hq : (∀ x, 0 ≤ q x) ∧ ∑ x, q x = 1)
    (hac : ∀ x, q x = 0 → p x = 0)
    (hW : (∀ x y, 0 ≤ W x y) ∧ ∀ x, ∑ y, W x y = 1) :
    klDivergence p q -
        klDivergence (channelOutput W p) (channelOutput W q) = 0 ↔
      ∀ y, channelOutput W p y = 0 ∨
        posterior W p y = posterior W q y := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
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
  have hTermZeroIff (y : Y) :
      channelOutput W p y *
          klDivergence (posterior W p y) (posterior W q y) = 0 ↔
        channelOutput W p y = 0 ∨
          posterior W p y = posterior W q y := by
    by_cases hOutputPZero : channelOutput W p y = 0
    · simp [hOutputPZero]
    have hOutputPPos : 0 < channelOutput W p y :=
      lt_of_le_of_ne (hOutputPNonneg y) (Ne.symm hOutputPZero)
    have hOutputQNe : channelOutput W q y ≠ 0 := by
      intro hOutputQZero
      exact hOutputPZero (hOutputAC y hOutputQZero)
    have hOutputQPos : 0 < channelOutput W q y :=
      lt_of_le_of_ne (hOutputQNonneg y) (Ne.symm hOutputQNe)
    have hPosteriorMass (r : X → ℝ) (hr : ∀ x, 0 ≤ r x)
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
    have hKlZeroIff :
        klDivergence (posterior W p y) (posterior W q y) = 0 ↔
          posterior W p y = posterior W q y :=
      kl_divergence_eq_zero_iff
        (posterior W p y) (posterior W q y)
        (hPosteriorMass p hp.1 hOutputPPos)
        (hPosteriorMass q hq.1 hOutputQPos)
        hPosteriorAC
    constructor
    · intro hTermZero
      refine Or.inr (hKlZeroIff.mp ?_)
      exact (mul_eq_zero.mp hTermZero).resolve_left hOutputPZero
    · rintro (hzero | hposteriors)
      · exact (hOutputPZero hzero).elim
      · rw [hKlZeroIff.mpr hposteriors, mul_zero]
  constructor
  · intro hDefectZero y
    exact (hTermZeroIff y).mp
      ((dpi_defect_eq_zero_iff_weighted_posterior_kl_zero
        p q W hp hq hac hW).mp hDefectZero y)
  · intro hPosteriors
    exact (dpi_defect_eq_zero_iff_weighted_posterior_kl_zero
      p q W hp hq hac hW).mpr fun y => (hTermZeroIff y).mpr (hPosteriors y)

#print axioms dpi_defect_eq_zero_iff_weighted_posterior_kl_zero
#print axioms dpi_defect_eq_zero_iff_zero_output_or_posteriors_eq

end D5.S3.DivergenceSupport.ZeroSupportDefectEquality
