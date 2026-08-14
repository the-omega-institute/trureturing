/- GID: D5/S0/Computability/DescriptionComplexity/LevinUpperBound
   generality: G
   mirror-B: D5/B/S0/Computability/DescriptionComplexity/LevinUpperBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite scaled-Kraft mass with a complexity ceiling bounds the candidate count. -/

import Mathlib

open scoped BigOperators

namespace D5.S0.Computability.DescriptionComplexity.LevinUpperBound

/-- The finite counting step behind the Levin upper bound.

The natural-number weight is a common power-of-two scaling of the prefix weights.
`weight_floor` records the budget bound on each shortest witness, while
`total_weight` records the conditional coding ceiling. -/
theorem levin_upper_bound
    {Candidate : Type*} (candidates : Finset Candidate)
    (Q K overhead : Nat) (weight : Candidate -> Nat)
    (weight_floor : forall candidate, candidate ∈ candidates -> 2 ^ K <= weight candidate)
    (total_weight : (∑ candidate ∈ candidates, weight candidate) <= 2 ^ (Q + overhead))
    (complexity_le_budget : K <= Q) :
    candidates.card <= 2 ^ (Q - K + overhead) := by
  have lower_mass :
      candidates.card * 2 ^ K <= ∑ candidate ∈ candidates, weight candidate := by
    calc
      candidates.card * 2 ^ K = ∑ _candidate ∈ candidates, 2 ^ K := by simp
      _ <= ∑ candidate ∈ candidates, weight candidate := by
        exact Finset.sum_le_sum (fun candidate hcandidate =>
          weight_floor candidate hcandidate)
  have scaled_bound : candidates.card * 2 ^ K <= 2 ^ (Q + overhead) :=
    lower_mass.trans total_weight
  have exponent_split : Q + overhead = K + (Q - K + overhead) := by
    omega
  have factored_bound :
      candidates.card * 2 ^ K <= 2 ^ K * 2 ^ (Q - K + overhead) := by
    simpa [exponent_split, pow_add, Nat.mul_comm] using scaled_bound
  have reordered_bound :
      2 ^ K * candidates.card <= 2 ^ K * 2 ^ (Q - K + overhead) := by
    simpa [Nat.mul_comm] using factored_bound
  exact Nat.le_of_mul_le_mul_left reordered_bound (by positivity)

/-- A one-candidate instance shows the scaled hypotheses are satisfiable. -/
example :
    let candidates : Finset Unit := {()}
    candidates.card <= 2 ^ (5 - 3 + 1) := by
  dsimp
  apply levin_upper_bound {()} 5 3 1 (fun _ => 2 ^ 3)
  · intro candidate hcandidate
    simp
  · simp
  · omega

end D5.S0.Computability.DescriptionComplexity.LevinUpperBound
