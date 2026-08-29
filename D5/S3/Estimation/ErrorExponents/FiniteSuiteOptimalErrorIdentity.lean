/- GID: D5/S3/Estimation/ErrorExponents/FiniteSuiteOptimalErrorIdentity
   generality: G
   mirror-B: D5/B/S3/Estimation/ErrorExponents/FiniteSuiteOptimalErrorIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Optimal suite error is half one minus TV, including empty and equal-law cases. -/

/- Library-search audit trail (2026-08-25):
   * Repository searches for `finiteSuiteOptimalError` and the target total-variation identity
     found only private helpers in the two frozen finite-suite squeeze modules.
   * The public definitions `equalPriorError`, `finiteSuiteOptimalError`, and `windowLaw` are
     reused from the frozen finite-suite module; no duplicate definition is introduced here.
   * Pinned Mathlib search for a minimum testing-error/total-variation identity found no match.
   * The proof reuses the repository's public sharp and one-sided Le Cam finite-event theorems.
-/

import D5.S3.Estimation.ErrorExponents.FiniteSuiteErrorSqueeze

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.ErrorExponents.FiniteSuiteOptimalErrorIdentity

open D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy
open D5.S3.Estimation.ErrorExponents.FiniteSuiteErrorSqueeze
open D5.S3.Estimation.LeCam
open D5.S3.Estimation.LeCamTight
open D5.S3.TotalVariation.Pinsker

/-- Optimal equal-prior error is half of one minus total variation. Coordinate
nonnegativity is unnecessary; only normalization of the two product laws is used. -/
theorem finite_suite_optimal_error_eq
    {Index Outcome : Type*} [Fintype Index] [DecidableEq Index] [Fintype Outcome]
    (p q : Index → Outcome → ℝ)
    (hp : ∀ i, ∑ a, p i a = 1)
    (hq : ∀ i, ∑ a, q i a = 1) :
    finiteSuiteOptimalError p q =
      (1 - totalVariation (windowLaw p) (windowLaw q)) / 2 := by
  classical
  have hpw : ∑ u, windowLaw p u = 1 := windowLaw_sum_eq_one p hp
  have hqw : ∑ u, windowLaw q u = 1 := windowLaw_sum_eq_one q hq
  unfold finiteSuiteOptimalError
  apply le_antisymm
  · apply Finset.min'_le
    apply Finset.mem_image.mpr
    let optimalEvent : Finset (Index → Outcome) :=
      Finset.univ.filter (fun z => windowLaw p z ≤ windowLaw q z)
    refine ⟨optimalEvent, Finset.mem_univ _, ?_⟩
    unfold equalPriorError
    rw [le_cam_two_point_sum_tight (windowLaw p) (windowLaw q)
      (hpw.trans hqw.symm) hqw]
  · apply Finset.le_min'
    intro risk hRisk
    rcases Finset.mem_image.mp hRisk with ⟨acceptSecond, _, rfl⟩
    have hLower := le_cam_two_point_sum (windowLaw p) (windowLaw q)
      acceptSecond (hpw.trans hqw.symm) hqw
    unfold equalPriorError
    linarith
#print axioms finite_suite_optimal_error_eq

/-- The first normalization hypothesis cannot be dropped: a zero law against unit mass fails
the identity on the concrete one-index, one-outcome suite. -/
theorem p_normalization_is_necessary :
    finiteSuiteOptimalError
        (fun _ : Unit => fun _ : Unit => (0 : ℝ))
        (fun _ : Unit => fun _ : Unit => (1 : ℝ)) ≠
      (1 - totalVariation
        (windowLaw (fun _ : Unit => fun _ : Unit => (0 : ℝ)))
        (windowLaw (fun _ : Unit => fun _ : Unit => (1 : ℝ)))) / 2 := by
  let p : Unit → Unit → ℝ := fun _ _ => 0
  let q : Unit → Unit → ℝ := fun _ _ => 1
  change finiteSuiteOptimalError p q ≠
    (1 - totalVariation (windowLaw p) (windowLaw q)) / 2
  have hError : finiteSuiteOptimalError p q = 0 := by
    unfold finiteSuiteOptimalError
    apply le_antisymm
    · apply Finset.min'_le
      apply Finset.mem_image.mpr
      refine ⟨Finset.univ, Finset.mem_univ _, ?_⟩
      simp [equalPriorError, p, q, windowLaw]
    · apply Finset.le_min'
      intro risk hRisk
      rcases Finset.mem_image.mp hRisk with ⟨acceptSecond, _, rfl⟩
      simp [equalPriorError, p, q, windowLaw]
      positivity
  have hTV : totalVariation (windowLaw p) (windowLaw q) = 1 / 2 := by
    norm_num [totalVariation, windowLaw, p, q]
  rw [hError, hTV]
  norm_num
#print axioms p_normalization_is_necessary

/-- The second normalization hypothesis cannot be dropped: unit mass against a zero law fails
the identity on the concrete one-index, one-outcome suite. -/
theorem q_normalization_is_necessary :
    finiteSuiteOptimalError
        (fun _ : Unit => fun _ : Unit => (1 : ℝ))
        (fun _ : Unit => fun _ : Unit => (0 : ℝ)) ≠
      (1 - totalVariation
        (windowLaw (fun _ : Unit => fun _ : Unit => (1 : ℝ)))
        (windowLaw (fun _ : Unit => fun _ : Unit => (0 : ℝ)))) / 2 := by
  let p : Unit → Unit → ℝ := fun _ _ => 1
  let q : Unit → Unit → ℝ := fun _ _ => 0
  change finiteSuiteOptimalError p q ≠
    (1 - totalVariation (windowLaw p) (windowLaw q)) / 2
  have hError : finiteSuiteOptimalError p q = 0 := by
    unfold finiteSuiteOptimalError
    apply le_antisymm
    · apply Finset.min'_le
      apply Finset.mem_image.mpr
      refine ⟨∅, Finset.mem_univ _, ?_⟩
      simp [equalPriorError, p, q, windowLaw]
    · apply Finset.le_min'
      intro risk hRisk
      rcases Finset.mem_image.mp hRisk with ⟨acceptSecond, _, rfl⟩
      simp [equalPriorError, p, q, windowLaw]
      positivity
  have hTV : totalVariation (windowLaw p) (windowLaw q) = 1 / 2 := by
    norm_num [totalVariation, windowLaw, p, q]
  rw [hError, hTV]
  norm_num
#print axioms q_normalization_is_necessary

/-- An empty outcome type cannot carry a normalized law at a nonempty index. -/
theorem empty_outcome_normalization_is_impossible (p : Unit → Empty → ℝ) :
    ¬∀ i, ∑ a, p i a = 1 := by
  simp
#print axioms empty_outcome_normalization_is_impossible

/-- With no coordinates, both window laws are the same empty product and the identity holds,
even when the outcome type itself is empty. -/
theorem empty_index_optimal_error_eq
    {Outcome : Type*} [Fintype Outcome]
    (p q : Empty → Outcome → ℝ) :
    finiteSuiteOptimalError p q =
      (1 - totalVariation (windowLaw p) (windowLaw q)) / 2 := by
  apply finite_suite_optimal_error_eq p q
  · intro i
    exact i.elim
  · intro i
    exact i.elim
#print axioms empty_index_optimal_error_eq

/-- Equal normalized coordinate laws have zero window total variation and optimal error one half. -/
theorem equal_laws_optimal_error_eq
    {Index Outcome : Type*} [Fintype Index] [DecidableEq Index] [Fintype Outcome]
    (p : Index → Outcome → ℝ)
    (hp : ∀ i, ∑ a, p i a = 1) :
    finiteSuiteOptimalError p p = (1 : ℝ) / 2 ∧
      totalVariation (windowLaw p) (windowLaw p) = 0 := by
  have hTV : totalVariation (windowLaw p) (windowLaw p) = 0 := by
    simp [totalVariation]
  constructor
  · rw [finite_suite_optimal_error_eq p p hp hp, hTV]
    norm_num
  · exact hTV
#print axioms equal_laws_optimal_error_eq

end D5.S3.Estimation.ErrorExponents.FiniteSuiteOptimalErrorIdentity
