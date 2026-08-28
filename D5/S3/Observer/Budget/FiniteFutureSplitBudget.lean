/- GID: D5/S3/Observer/Budget/FiniteFutureSplitBudget
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/FiniteFutureSplitBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite future refinements obey pair and class-count split budgets. -/

import D5.S3.ConceptDynamics.Refinement.StrictRefinementBound
import Mathlib.Data.Nat.Choose.Basic

/- Library-search audit trail (2026-08-28):
   * The exact D5 class-budget theorem
     `strict_refinement_steps_le_card_sub_initial_image` supplies the second
     public clause on the canonical `Concept` and `StrictlyRefines` carriers.
   * Searches under `ConceptDynamics`, `Observer`, and `ObserverMemory` found no
     theorem combining that clause with the unordered-pair budget.
   * Pinned Mathlib supplies `Nat.choose_succ_succ` and
     `Nat.choose_one_right`; these evaluate the pair budget without introducing
     a parallel pair carrier. The exact `Sym2.natCard_subtype_not_isDiag` hit is
     equivalent supporting infrastructure but is not needed by this proof. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Budget.FiniteFutureSplitBudget

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Refinement.StrictRefinementBound

/-- A chain of strict finite-state observation refinements has no more steps
than there are unordered distinct state pairs, and no more than the deficit
between the state count and the initial observation-class count. -/
theorem finite_future_split_budget
    {X B : Type*} [Finite X] (steps : Nat)
    (readout : Fin (steps + 1) -> Concept X B)
    (strict : forall i : Fin steps,
      StrictlyRefines (readout i.castSucc) (readout i.succ)) :
    steps <= (Nat.card X).choose 2 /\
      steps <= Nat.card X - Nat.card (Set.range (readout 0)) := by
  have classBudget :=
    strict_refinement_steps_le_card_sub_initial_image steps readout strict
  refine ⟨?_, classBudget⟩
  cases isEmpty_or_nonempty X with
  | inl emptyX =>
      letI := Fintype.ofFinite X
      have stateCard : Nat.card X = 0 := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_eq_zero_iff.mpr emptyX
      have stepsZero : steps = 0 := by
        apply Nat.eq_zero_of_le_zero
        simpa only [stateCard, Nat.zero_sub] using classBudget
      simp [stepsZero]
  | inr nonemptyX =>
      letI : Nonempty X := nonemptyX
      letI : Nonempty (Set.range (readout 0)) :=
        (Set.range_nonempty (readout 0)).to_subtype
      have initialPositive : 1 <= Nat.card (Set.range (readout 0)) :=
        Nat.card_pos
      have deficitLePred :
          Nat.card X - Nat.card (Set.range (readout 0)) <= Nat.card X - 1 :=
        Nat.sub_le_sub_left initialPositive (Nat.card X)
      have predLeChooseTwo : forall n : Nat, n - 1 <= n.choose 2 := by
        intro n
        cases n with
        | zero => simp
        | succ n =>
            simp only [Nat.succ_sub_one, Nat.choose_succ_succ,
              Nat.choose_one_right]
            exact Nat.le_add_right n (n.choose 2)
      exact classBudget.trans (deficitLePred.trans (predLeChooseTwo _))

#print axioms finite_future_split_budget

end D5.S3.Observer.Budget.FiniteFutureSplitBudget
