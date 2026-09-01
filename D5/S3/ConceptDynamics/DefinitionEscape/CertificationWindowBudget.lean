/- GID: D5/S3/ConceptDynamics/DefinitionEscape/CertificationWindowBudget
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/CertificationWindowBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite certification windows grow with budget and combine under summed budgets. -/

import D5.S3.ConceptDynamics.DefinitionEscape.FiniteCoverCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/- Library-search audit trail (2026-09-01):
   * Repository search found `budgetedEscapeRate`, `finiteSelectionCost`,
     `finiteSelectionSupplement`, and `countingEscapeAntitoneLaw` in
     `FiniteCoverCounting`. The model below reuses `finiteSelectionCost`; it
     studies budget growth of certified targets rather than escape-rate decay
     or observer-family refinement.
   * Pinned Mathlib search found
     `Finset.sum_le_sum_of_subset_of_nonneg`, the finite-sum order law needed
     when overlapping selections are combined. No separate cost carrier or
     external package is required. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.CertificationWindowBudget

open D5.S3.ConceptDynamics.DefinitionEscape.FiniteCoverCounting

/-- The targets covered by at least one candidate in a finite selection. -/
noncomputable def finiteSelectionCapture
    {I Target : Type*}
    (Gamma : Set I) (coverage : I → Set Target)
    (selection : Finset Gamma) : Set Target := by
  classical
  exact {point | ∃ item ∈ selection, point ∈ coverage item.1}

/-- A target set is in the certification window at `budget` when one finite
selection covers it and its canonical summed cost is within budget. Candidate
costs and budgets are nonnegative reals. -/
noncomputable def certificationWindow
    {I Target : Type*}
    (Gamma : Set I) (coverage : I → Set Target)
    (candidateCost : I → NNReal) (budget : NNReal) : Set (Set Target) :=
  {claim | ∃ selection : Finset Gamma,
    finiteSelectionCost Gamma (fun item ↦ (candidateCost item : Real)) selection ≤
        (budget : Real) ∧
      claim ⊆ finiteSelectionCapture Gamma coverage selection}

/-- Increasing the budget preserves every certification witness, so the
certification window is monotone without any model-side premise. -/
theorem certification_window_budget_monotone
    {I Target : Type*}
    (Gamma : Set I) (coverage : I → Set Target)
    (candidateCost : I → NNReal) :
    Monotone (certificationWindow Gamma coverage candidateCost) := by
  intro budget1 budget2 budgetOrder claim certified
  rcases certified with ⟨selection, costAtBudget1, captures⟩
  refine ⟨selection, ?_, captures⟩
  exact costAtBudget1.trans (by exact_mod_cast budgetOrder)

/-- Two certified target sets remain certified after union when their budgets
are added. Overlapping candidates are charged only once in the union. -/
theorem certification_window_union_closed
    {I Target : Type*}
    (Gamma : Set I) (coverage : I → Set Target)
    (candidateCost : I → NNReal)
    (claimA claimB : Set Target) (budgetA budgetB : NNReal)
    (claimACertified :
      claimA ∈ certificationWindow Gamma coverage candidateCost budgetA)
    (claimBCertified :
      claimB ∈ certificationWindow Gamma coverage candidateCost budgetB) :
    claimA ∪ claimB ∈
      certificationWindow Gamma coverage candidateCost (budgetA + budgetB) := by
  classical
  rcases claimACertified with ⟨selectionA, costA, capturesA⟩
  rcases claimBCertified with ⟨selectionB, costB, capturesB⟩
  refine ⟨selectionA ∪ selectionB, ?_, ?_⟩
  · have remainingCostLe :
        (∑ item ∈ selectionB \ selectionA, (candidateCost item.1 : Real)) ≤
          ∑ item ∈ selectionB, (candidateCost item.1 : Real) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun item _ _ ↦ (candidateCost item.1).coe_nonneg)
    have unionCostLe :
        finiteSelectionCost Gamma
            (fun item ↦ (candidateCost item : Real))
            (selectionA ∪ selectionB) ≤
          finiteSelectionCost Gamma
              (fun item ↦ (candidateCost item : Real)) selectionA +
            finiteSelectionCost Gamma
              (fun item ↦ (candidateCost item : Real)) selectionB := by
      unfold finiteSelectionCost
      calc
        (∑ item ∈ selectionA ∪ selectionB,
            (candidateCost item.1 : Real)) =
            (∑ item ∈ selectionA, (candidateCost item.1 : Real)) +
              ∑ item ∈ selectionB \ selectionA,
                (candidateCost item.1 : Real) := by
          rw [← Finset.sum_union Finset.disjoint_sdiff,
            Finset.union_sdiff_self_eq_union]
        _ ≤
            (∑ item ∈ selectionA, (candidateCost item.1 : Real)) +
              ∑ item ∈ selectionB,
                (candidateCost item.1 : Real) :=
          add_le_add_right remainingCostLe _
    refine unionCostLe.trans ?_
    simpa only [NNReal.coe_add] using add_le_add costA costB
  · rintro point (pointInA | pointInB)
    · rcases capturesA pointInA with ⟨item, itemInA, itemCovers⟩
      exact ⟨item, Finset.mem_union_left selectionB itemInA, itemCovers⟩
    · rcases capturesB pointInB with ⟨item, itemInB, itemCovers⟩
      exact ⟨item, Finset.mem_union_right selectionA itemInB, itemCovers⟩

#print axioms certification_window_budget_monotone
#print axioms certification_window_union_closed

end D5.S3.ConceptDynamics.DefinitionEscape.CertificationWindowBudget
