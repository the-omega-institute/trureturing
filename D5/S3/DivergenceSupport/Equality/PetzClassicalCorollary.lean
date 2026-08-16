/- GID: D5/S3/DivergenceSupport/Equality/PetzClassicalCorollary
   generality: G
   mirror-B: D5/B/S3/DivergenceSupport/Equality/PetzClassicalCorollary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Combine posterior equality, Bayesian recovery, and permutation-channel equality. -/

/- Library-search audit (2026-08-16):
   * The repository already proves the zero-defect posterior criterion in
     `ZeroSupportDefectEquality` and the Bayesian reverse-recovery criterion in `PetzRecovery`.
     Those exact declarations are imported and applied below.
   * Pinned mathlib supplies `Equiv.sum_comp`, which is used to reindex the divergence sum under
     a permutation. No exact packaged result was found for this repository's defect definition.
   * Authenticated searches of admissible Lean repositories found no exact full corollary.
-/

import D5.S3.DivergenceSupport.Equality.PetzRecovery

namespace D5.S3.DivergenceSupport.Equality.PetzClassicalCorollary

open D5.S3.Divergence.ClassicalDPI
open D5.S3.DivergenceSupport.ZeroSupportDefectEquality
open D5.S3.DivergenceSupport.Equality.PetzRecovery

/-- The deterministic channel induced by a finite equivalence. -/
noncomputable def permutationChannel {X Y : Type*} (e : X ≃ Y) : X → Y → ℝ := by
  classical
  exact fun x y => if e x = y then 1 else 0

private theorem permutation_defect_eq_zero {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : X → ℝ) (e : X ≃ Y) :
    klDivergence p q -
        klDivergence (channelOutput (permutationChannel e) p)
          (channelOutput (permutationChannel e) q) = 0 := by
  classical
  have hOutput (r : X → ℝ) :
      channelOutput (permutationChannel e) r = fun y => r (e.symm y) := by
    funext y
    simp only [channelOutput, permutationChannel]
    rw [Fintype.sum_eq_single (e.symm y)]
    · simp
    · intro x hxy
      have hex : e x ≠ y := by
        intro h
        apply hxy
        exact e.injective (h.trans (e.apply_symm_apply y).symm)
      simp [hex]
  rw [hOutput p, hOutput q]
  unfold klDivergence
  have hReindex :
      (∑ y : Y, p (e.symm y) * Real.log (p (e.symm y) / q (e.symm y))) =
        ∑ x : X, p x * Real.log (p x / q x) :=
    e.symm.sum_comp fun x => p x * Real.log (p x / q x)
  rw [hReindex]
  ring

/-- Vanishing defect is equivalent both to posterior agreement and to Bayesian recovery, while
every permutation channel has vanishing defect. -/
theorem zero_defect_equivalences_and_permutation_channel {X Y : Type*}
    [Fintype X] [Fintype Y]
    (p q : X → ℝ) (W : X → Y → ℝ)
    (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1)
    (hq : (∀ x, 0 ≤ q x) ∧ ∑ x, q x = 1)
    (hac : ∀ x, q x = 0 → p x = 0)
    (hW : (∀ x y, 0 ≤ W x y) ∧ ∀ x, ∑ y, W x y = 1) :
    (klDivergence p q -
          klDivergence (channelOutput W p) (channelOutput W q) = 0 ↔
        ∀ y, channelOutput W p y = 0 ∨
          posterior W p y = posterior W q y) ∧
    (klDivergence p q -
          klDivergence (channelOutput W p) (channelOutput W q) = 0 ↔
        ∃ R : Y → X → ℝ,
          (∀ y x, R y x =
            if channelOutput W q y = 0 then q x else posterior W q y x) ∧
          (∀ y x, 0 ≤ R y x) ∧
          (∀ y, ∑ x, R y x = 1) ∧
          channelOutput R (channelOutput W p) = p ∧
          channelOutput R (channelOutput W q) = q) ∧
    ∀ e : X ≃ Y,
      klDivergence p q -
          klDivergence (channelOutput (permutationChannel e) p)
            (channelOutput (permutationChannel e) q) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact dpi_defect_eq_zero_iff_zero_output_or_posteriors_eq p q W hp hq hac hW
  · exact dpi_defect_eq_zero_iff_exists_bayes_recovery p q W hp hq hac hW
  · exact permutation_defect_eq_zero p q

#print axioms zero_defect_equivalences_and_permutation_channel

end D5.S3.DivergenceSupport.Equality.PetzClassicalCorollary
