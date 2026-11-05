import D5.S3.Combinatorics.CircularWords.ActualCycleMeanLowerBound

open D5.S3.Combinatorics.CircularWords.UniformCycleAttainment
open D5.S3.Combinatorics.CircularWords.ActualCycleMeanLowerBound
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound

variable {α : Type} [DecidableEq α]

set_option maxHeartbeats 4000000

noncomputable section
attribute [local instance] Classical.propDecidable
example {A : Finset α} (hA : 4 ≤ A.card)
    {L : Type} (policy : History A → Sum (Query A) L)
    (tr : Cycle α → History A) (lab : Cycle α → L)
    (runs : ∀ C ∈ carrier A, ∃ n, execute (read A) policy n [] C = some (tr C,lab C))
    (output : L → Cycle α) (correct : ∀ C ∈ carrier A, output (lab C) = C) :
    (2 : ℚ) + 2 / (A.card - 1 : ℚ) ≤
      ((∑ C ∈ carrier A, (tr C).length : Nat) : ℚ) / ((carrier A).card : ℚ) :=
  actual_history_lower_bound (α := α) (A := A) hA policy tr lab runs output correct

example {A : Finset α} (hA : 4 ≤ A.card)
    (x z y : Query A) (hxz : x.1 ≠ z.1) :
    ((∑ C ∈ carrier A,
      (runPassiveProtocol (read A) (attainingProtocol A x z y) C).length : Nat) : ℚ) /
      ((carrier A).card : ℚ) = 2 + 2 / (A.card - 1 : ℚ) :=
  actual_cycle_attaining_mean (α := α) (A := A) hA x z y hxz

#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.rooted_gap_second_law
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.slot_fiber_zero_card
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.pair_branch_exact
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.actual_cycle_attaining_mean
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.attainingProtocol_correct
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.attainingPolicy_execute
#print axioms D5.S3.Combinatorics.CircularWords.ActualCycleMeanLowerBound.actual_history_lower_bound
end
