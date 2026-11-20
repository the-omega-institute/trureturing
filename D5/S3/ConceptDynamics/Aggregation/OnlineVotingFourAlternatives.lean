/- GID: D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives
   generality: W
   mirror-B: D5/B/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: refutes claim=claim result=result
   digest: Four labeled arrivals obstruct the deterministic square-root-of-thirteen guarantee. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Deterministic online voting with four alternatives

The model and threshold are from Ghasemi, Seddighin and Seddighin,
*Distortion in Online Voting*, [arXiv:2611.25709v1](https://arxiv.org/abs/2611.25709v1),
§§3 and 6. The finite certificate is the four-alternative construction in
[trureturing issue #32348](https://github.com/the-omega-institute/trureturing/issues/32348).
-/

set_option autoImplicit false

namespace OnlineVotingFourAlternatives

abbrev Alternative := Fin 4
abbrev Label (n : ℕ) := Fin n ⊕ Alternative
abbrev Profile (n : ℕ) := Fin n → Equiv.Perm Alternative
abbrev Arrival := Fin 4 ≃ Alternative

/-- The order of arrivals and each labeled voter's pairwise comparisons on the prefix. -/
structure Observation (n : ℕ) where
  arrived : List Alternative
  prefers : Fin n → Alternative → Alternative → Bool

def observe {n : ℕ} (arrival : Arrival) (profile : Profile n) (round : ℕ) : Observation n where
  arrived := (List.ofFn arrival).take round
  prefers v a b := decide
    ((arrival.symm a).val < round ∧ (arrival.symm b).val < round ∧ profile v a < profile v b)

/-- A deterministic rule receives all observations through the current round and its own
earlier decisions, in chronological order. True switches to the latest arrival. -/
abbrev Rule (n : ℕ) := List (Observation n) → List Bool → Bool

private def choose (switch : Bool) (incumbent latest : Alternative) : Alternative :=
  if switch then latest else incumbent

def finalWinner {n : ℕ} (rule : Rule n) (arrival : Arrival) (profile : Profile n) : Alternative :=
  let o := observe arrival profile
  let d₂ := rule [o 1, o 2] []
  let d₃ := rule [o 1, o 2, o 3] [d₂]
  let d₄ := rule [o 1, o 2, o 3, o 4] [d₂, d₃]
  choose d₄ (choose d₃ (choose d₂ (arrival 0) (arrival 1)) (arrival 2)) (arrival 3)

/-- Voters and alternatives lie in a single real-valued metric space. A full ballot
orders any ties once, and all observations inherit that order. -/
structure Election (n : ℕ) where
  Space : Type
  metric : MetricSpace Space
  location : Label n → Space
  arrival : Arrival
  profile : Profile n
  compatible : ∀ v a b, profile v a < profile v b →
    @dist Space metric.toDist (location (.inr a)) (location (.inl v)) ≤
      @dist Space metric.toDist (location (.inr b)) (location (.inl v))

noncomputable def socialCost {n : ℕ} (election : Election n) (a : Alternative) : ℝ :=
  ∑ v : Fin n, @dist election.Space election.metric.toDist
    (election.location (.inr a)) (election.location (.inl v))

/-- At the positive threshold, bounding the cost against every alternative is
equivalent to bounding it against the minimum over the full election. -/
def claim : Prop :=
  ∃ rule : Rule 12, ∀ election : Election 12, ∀ a : Alternative,
    socialCost election (finalWinner rule election.arrival election.profile) ≤
      Real.sqrt 13 * socialCost election a

end OnlineVotingFourAlternatives
