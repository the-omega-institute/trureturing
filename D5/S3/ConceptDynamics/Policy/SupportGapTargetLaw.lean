/- GID: D5/S3/ConceptDynamics/Policy/SupportGapTargetLaw
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Policy/SupportGapTargetLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A target branch outside behavior support leaves its outcome law undetermined. -/

import Mathlib.Probability.ProbabilityMassFunction.Constructions

/- Library-search audit trail (2026-08-25):
   * Repository searches for policy support, off-policy laws, transition models,
     and counterfactual identifiability found nearby causal separation modules but
     no theorem constructing two transition mechanisms at a missing behavior branch.
   * Pinned Mathlib exact hits `PMF.map_const`, `PMF.mem_support_map_iff`, and
     `PMF.mem_support_iff` are applied directly below. They supply the constant-law
     pushforward and the positive target-branch support witness.
   * Exact full-statement searches across D5, accepted freezes, and pinned Mathlib
     were misses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Policy.SupportGapTargetLaw

/-- If a target-reachable history-action branch has zero behavior-policy mass,
two transition mechanisms can differ at that branch while agreeing at every
behavior-supported branch, and their target pushforward outcome laws differ. -/
theorem support_gap_target_law
    {History Action Outcome : Type*}
    (behavior : History -> PMF Action)
    (targetBranches : PMF (History × Action))
    (history : History) (action : Action)
    (firstOutcome secondOutcome : Outcome)
    (behaviorMissing : behavior history action = 0)
    (targetReachable : targetBranches (history, action) ≠ 0)
    (outcomesDistinct : firstOutcome ≠ secondOutcome) :
    ∃ firstModel secondModel : History -> Action -> Outcome,
      firstModel history action ≠ secondModel history action ∧
      (∀ nextHistory nextAction,
        behavior nextHistory nextAction ≠ 0 ->
          firstModel nextHistory nextAction = secondModel nextHistory nextAction) ∧
      targetBranches.map
          (fun branch => firstModel branch.1 branch.2) ≠
        targetBranches.map
          (fun branch => secondModel branch.1 branch.2) := by
  classical
  let firstModel : History -> Action -> Outcome :=
    fun _ _ => firstOutcome
  let secondModel : History -> Action -> Outcome :=
    fun nextHistory nextAction =>
      if (nextHistory, nextAction) = (history, action) then
        secondOutcome
      else
        firstOutcome
  refine ⟨firstModel, secondModel, ?_, ?_, ?_⟩
  · simpa [firstModel, secondModel] using outcomesDistinct
  · intro nextHistory nextAction behaviorSupported
    by_cases selected : (nextHistory, nextAction) = (history, action)
    · cases selected
      exact (behaviorSupported behaviorMissing).elim
    · change firstOutcome =
        if (nextHistory, nextAction) = (history, action) then
          secondOutcome
        else
          firstOutcome
      rw [if_neg selected]
  · intro targetLawsEqual
    have firstLaw :
        targetBranches.map
            (fun branch => firstModel branch.1 branch.2) =
          PMF.pure firstOutcome := by
      change targetBranches.map (Function.const (History × Action) firstOutcome) =
        PMF.pure firstOutcome
      exact PMF.map_const targetBranches firstOutcome
    have secondOutcomeSupported :
        secondOutcome ∈
          (targetBranches.map
            (fun branch => secondModel branch.1 branch.2)).support := by
      rw [PMF.mem_support_map_iff]
      refine ⟨(history, action), ?_, ?_⟩
      · exact targetReachable
      · simp [secondModel]
    have pureSupportsSecondOutcome :
        secondOutcome ∈ (PMF.pure firstOutcome).support := by
      rw [← firstLaw, targetLawsEqual]
      exact secondOutcomeSupported
    have reverseDistinct : secondOutcome ≠ firstOutcome := Ne.symm outcomesDistinct
    rw [PMF.mem_support_iff, PMF.pure_apply, if_neg reverseDistinct] at pureSupportsSecondOutcome
    exact (pureSupportsSecondOutcome rfl).elim

/-- The support-gap hypotheses have a checked one-history Boolean witness. -/
example :
    (PMF.pure false : PMF Bool) true = 0 ∧
      (PMF.pure (PUnit.unit, true) : PMF (PUnit × Bool))
        (PUnit.unit, true) ≠ 0 ∧
      false ≠ true := by
  simp [PMF.pure_apply]

/-- The history domain used by the witness is inhabited. -/
example : PUnit := PUnit.unit

#print axioms support_gap_target_law

end D5.S3.ConceptDynamics.Policy.SupportGapTargetLaw
