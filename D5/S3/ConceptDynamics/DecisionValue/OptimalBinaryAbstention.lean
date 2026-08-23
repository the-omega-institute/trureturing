/- GID: D5/S3/ConceptDynamics/DecisionValue/OptimalBinaryAbstention
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValue/OptimalBinaryAbstention
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Binary posterior loss selects the stated answer or abstention at each threshold. -/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/- Library-search audit trail (2026-08-23):
   * Repository searches for `decisionPayoff`, `optimalActions`, `abstain`,
     `Option Bool`, binary decision losses, and `_eq_` bridges found no exact
     posterior-loss construction or threshold theorem.
   * `DecisionWithoutFullPrediction.decisionPayoff` is a fixed counterexample
     payoff table, while `SafeAnswerCoverageMaximality.canonicalSafeAnswer` is a
     zero-error fiber construction; neither is the source object here.
   * The established `Option Bool` action carrier is reused directly. Pinned
     Mathlib has generic minimum and argmin interfaces but no exact theorem for
     these three posterior costs; Loogle's exact `abstain` query returned no hits. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DecisionValue.OptimalBinaryAbstention

/-- Expected loss for answering zero, abstaining, or answering one. -/
def binaryDecisionLoss (p lambda : Real) : Option Bool -> Real
  | some false => p
  | none => lambda
  | some true => 1 - p

/-- The loss-comparison selector, with ties assigned to answer zero first and
answer one second, as in the source statement. -/
noncomputable def preferredBinaryAction (p lambda : Real) : Option Bool :=
  if binaryDecisionLoss p lambda (some false) <=
        binaryDecisionLoss p lambda none /\
      binaryDecisionLoss p lambda (some false) <=
        binaryDecisionLoss p lambda (some true) then
    some false
  else if binaryDecisionLoss p lambda none <
        binaryDecisionLoss p lambda (some false) /\
      binaryDecisionLoss p lambda none <
        binaryDecisionLoss p lambda (some true) then
    none
  else
    some true

/-- For a binary posterior and abstention cost strictly between zero and one
half, direct comparison of the three source losses gives exactly the three
stated optimal-action regions, including both endpoint tie conventions. -/
theorem optimal_binary_answer_with_abstention
    (p lambda : Real) (hp : p ∈ Set.Icc (0 : Real) 1)
    (hlambda : lambda ∈ Set.Ioo (0 : Real) (1 / 2 : Real)) :
    (p <= lambda -> preferredBinaryAction p lambda = some false) /\
    ((lambda < p /\ p < 1 - lambda) ->
      preferredBinaryAction p lambda = none) /\
    (1 - lambda <= p -> preferredBinaryAction p lambda = some true) := by
  rcases hp with ⟨hp0, hp1⟩
  rcases hlambda with ⟨hlambda0, hlambdaHalf⟩
  constructor
  · intro hlow
    have hzero :
        binaryDecisionLoss p lambda (some false) <=
            binaryDecisionLoss p lambda none /\
          binaryDecisionLoss p lambda (some false) <=
            binaryDecisionLoss p lambda (some true) := by
      simp only [binaryDecisionLoss]
      constructor <;> linarith
    simp [preferredBinaryAction, hzero]
  constructor
  · rintro ⟨hlow, hhigh⟩
    have hnotZero :
        ¬ (binaryDecisionLoss p lambda (some false) <=
              binaryDecisionLoss p lambda none /\
            binaryDecisionLoss p lambda (some false) <=
              binaryDecisionLoss p lambda (some true)) := by
      simp only [binaryDecisionLoss]
      intro h
      linarith [h.1]
    have habstain :
        binaryDecisionLoss p lambda none <
            binaryDecisionLoss p lambda (some false) /\
          binaryDecisionLoss p lambda none <
            binaryDecisionLoss p lambda (some true) := by
      simp only [binaryDecisionLoss]
      constructor <;> linarith
    simp [preferredBinaryAction, hnotZero, habstain]
  · intro hhigh
    have hnotZero :
        ¬ (binaryDecisionLoss p lambda (some false) <=
              binaryDecisionLoss p lambda none /\
            binaryDecisionLoss p lambda (some false) <=
              binaryDecisionLoss p lambda (some true)) := by
      simp only [binaryDecisionLoss]
      intro h
      linarith [h.2]
    have hnotAbstain :
        ¬ (binaryDecisionLoss p lambda none <
              binaryDecisionLoss p lambda (some false) /\
            binaryDecisionLoss p lambda none <
              binaryDecisionLoss p lambda (some true)) := by
      simp only [binaryDecisionLoss]
      intro h
      linarith [h.2]
    simp [preferredBinaryAction, hnotZero, hnotAbstain]

#print axioms optimal_binary_answer_with_abstention

end D5.S3.ConceptDynamics.DecisionValue.OptimalBinaryAbstention
