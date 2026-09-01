/- GID: D5/S3/ConceptDynamics/DecisionValue/BayesianBestResponseFixedPoint
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValue/BayesianBestResponseFixedPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite Bayesian best responses are nonempty and equilibria are fixed points. -/

import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * The target atom has no formalization receipt and remains in `residual-open`
     with empty `coverage_gids`. Repository searches for Bayesian and Nash
     equilibria, best-response correspondences, conditional argmax predicates,
     and expanded unilateral utility comparisons found no covering declaration.
   * The adjacent `CoordinationBestResponseNonuniqueness` module proves that two
     complete-information coordination profiles are locally stable. It has no
     signal, conditional expectation, positive-probability guard, set-valued
     response correspondence, or Bayesian fixed-point characterization.
   * Pinned Mathlib has no `NashEquilibrium` or `BestResponse` game-theory
     declaration. It supplies the exact finite maximizer theorem
     `Finite.exists_max`, the generic `IsGreatest` predicate, and
     `div_le_div_iff_of_pos_right`, all reused below. The `loogle` and
     `leansearch` executables were unavailable on PATH, and the other pinned
     Lean packages contain no game-theory match. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.DecisionValue.BayesianBestResponseFixedPoint

/-- The prior mass of a signal fiber. The prior uses nonnegative real weights;
normalization of the total mass is not needed for conditional argmaxes. -/
noncomputable def signalProbability {State Signal : Type*} [Fintype State]
    (prior : State -> NNReal) (signal : State -> Signal) (observed : Signal) : Real := by
  classical
  exact ∑ state with signal state = observed, (prior state : Real)

/-- The numerator of conditional expected utility on one signal fiber. -/
noncomputable def unnormalizedExpectedUtility
    {State OwnSignal OtherSignal Action : Type*} [Fintype State]
    (prior : State -> NNReal)
    (ownSignal : State -> OwnSignal) (otherSignal : State -> OtherSignal)
    (utility : State -> Action -> Action -> Real)
    (observed : OwnSignal) (ownAction : Action)
    (otherPolicy : OtherSignal -> Action) : Real := by
  classical
  exact ∑ state with ownSignal state = observed,
    (prior state : Real) *
      utility state ownAction (otherPolicy (otherSignal state))

/-- Finite conditional expected utility. Its denominator is guarded by positive
signal probability whenever it is used to define a best response. -/
noncomputable def conditionalExpectedUtility
    {State OwnSignal OtherSignal Action : Type*} [Fintype State]
    (prior : State -> NNReal)
    (ownSignal : State -> OwnSignal) (otherSignal : State -> OtherSignal)
    (utility : State -> Action -> Action -> Real)
    (observed : OwnSignal) (ownAction : Action)
    (otherPolicy : OtherSignal -> Action) : Real :=
  unnormalizedExpectedUtility prior ownSignal otherSignal utility
      observed ownAction otherPolicy /
    signalProbability prior ownSignal observed

/-- Division by the common positive signal probability preserves every pairwise
utility comparison. This is the finite justification for using the numerator
when computing an argmax. -/
lemma conditionalExpectedUtility_le_iff_unnormalized
    {State OwnSignal OtherSignal Action : Type*} [Fintype State]
    (prior : State -> NNReal)
    (ownSignal : State -> OwnSignal) (otherSignal : State -> OtherSignal)
    (utility : State -> Action -> Action -> Real)
    (observed : OwnSignal) (left right : Action)
    (otherPolicy : OtherSignal -> Action)
    (positive : 0 < signalProbability prior ownSignal observed) :
    conditionalExpectedUtility prior ownSignal otherSignal utility
        observed left otherPolicy <=
      conditionalExpectedUtility prior ownSignal otherSignal utility
        observed right otherPolicy <->
    unnormalizedExpectedUtility prior ownSignal otherSignal utility
        observed left otherPolicy <=
      unnormalizedExpectedUtility prior ownSignal otherSignal utility
        observed right otherPolicy := by
  simp only [conditionalExpectedUtility]
  exact div_le_div_iff_of_pos_right positive

/-- On a positive-probability signal fiber, normalized and unnormalized utility
have exactly the same (possibly nonunique) maximizing actions. -/
theorem conditional_argmax_iff_unnormalized_argmax
    {State OwnSignal OtherSignal Action : Type*} [Fintype State]
    (prior : State -> NNReal)
    (ownSignal : State -> OwnSignal) (otherSignal : State -> OtherSignal)
    (utility : State -> Action -> Action -> Real)
    (observed : OwnSignal) (policy : OwnSignal -> Action)
    (otherPolicy : OtherSignal -> Action)
    (positive : 0 < signalProbability prior ownSignal observed) :
    IsGreatest
        (Set.range fun action =>
          conditionalExpectedUtility prior ownSignal otherSignal utility
            observed action otherPolicy)
        (conditionalExpectedUtility prior ownSignal otherSignal utility
          observed (policy observed) otherPolicy) <->
      IsGreatest
        (Set.range fun action =>
          unnormalizedExpectedUtility prior ownSignal otherSignal utility
            observed action otherPolicy)
        (unnormalizedExpectedUtility prior ownSignal otherSignal utility
          observed (policy observed) otherPolicy) := by
  constructor
  · rintro ⟨_, maximal⟩
    refine ⟨⟨policy observed, rfl⟩, ?_⟩
    rintro _ ⟨action, rfl⟩
    exact (conditionalExpectedUtility_le_iff_unnormalized
      prior ownSignal otherSignal utility observed action
        (policy observed) otherPolicy positive).mp
      (maximal ⟨action, rfl⟩)
  · rintro ⟨_, maximal⟩
    refine ⟨⟨policy observed, rfl⟩, ?_⟩
    rintro _ ⟨action, rfl⟩
    exact (conditionalExpectedUtility_le_iff_unnormalized
      prior ownSignal otherSignal utility observed action
        (policy observed) otherPolicy positive).mpr
      (maximal ⟨action, rfl⟩)

/-- The set-valued Bayesian best-response correspondence. Only signal values
with positive prior mass impose an optimality condition; a policy is arbitrary
on impossible signal values. -/
def bestResponses
    {State OwnSignal OtherSignal Action : Type*} [Fintype State]
    (prior : State -> NNReal)
    (ownSignal : State -> OwnSignal) (otherSignal : State -> OtherSignal)
    (utility : State -> Action -> Action -> Real)
    (otherPolicy : OtherSignal -> Action) : Set (OwnSignal -> Action) :=
  {policy | forall observed,
    0 < signalProbability prior ownSignal observed ->
      IsGreatest
        (Set.range fun action =>
          conditionalExpectedUtility prior ownSignal otherSignal utility
            observed action otherPolicy)
        (conditionalExpectedUtility prior ownSignal otherSignal utility
          observed (policy observed) otherPolicy)}

/-- Every finite nonempty action space admits a Bayesian best-response policy.
No uniqueness of the maximizing action is asserted. -/
theorem bestResponses_nonempty
    {State OwnSignal OtherSignal Action : Type*}
    [Fintype State] [Finite Action] [Nonempty Action]
    (prior : State -> NNReal)
    (ownSignal : State -> OwnSignal) (otherSignal : State -> OtherSignal)
    (utility : State -> Action -> Action -> Real)
    (otherPolicy : OtherSignal -> Action) :
    (bestResponses prior ownSignal otherSignal utility otherPolicy).Nonempty := by
  classical
  choose policy maximal using fun observed : OwnSignal =>
    Finite.exists_max (fun action : Action =>
      conditionalExpectedUtility prior ownSignal otherSignal utility
        observed action otherPolicy)
  refine ⟨policy, ?_⟩
  intro observed _positive
  refine ⟨⟨policy observed, rfl⟩, ?_⟩
  rintro _ ⟨action, rfl⟩
  exact maximal observed action

/-- The other player in a two-player game. -/
def otherPlayer : Fin 2 -> Fin 2 := fun player =>
  Fin.cases 1 (fun _ => 0) player

@[simp] theorem otherPlayer_zero : otherPlayer 0 = 1 := rfl

@[simp] theorem otherPlayer_one : otherPlayer 1 = 0 := rfl

/-- Player `i`'s best responses to the other coordinate of a two-player
strategy profile. Both players use the same finite action and signal types. -/
def playerBestResponses
    {State Signal Action : Type*} [Fintype State]
    (prior : State -> NNReal) (signal : Fin 2 -> State -> Signal)
    (utility : Fin 2 -> State -> Action -> Action -> Real)
    (profile : Fin 2 -> Signal -> Action) (player : Fin 2) :
    Set (Signal -> Action) :=
  bestResponses prior (signal player) (signal (otherPlayer player))
    (utility player) (profile (otherPlayer player))

/-- The joint set-valued best-response operator for a two-player Bayesian game. -/
def jointBestResponse
    {State Signal Action : Type*} [Fintype State]
    (prior : State -> NNReal) (signal : Fin 2 -> State -> Signal)
    (utility : Fin 2 -> State -> Action -> Action -> Real)
    (profile : Fin 2 -> Signal -> Action) :
    Set (Fin 2 -> Signal -> Action) :=
  {candidate | forall player,
    candidate player ∈
      playerBestResponses prior signal utility profile player}

/-- A two-player Bayesian Nash equilibrium is a membership fixed point of the
joint best-response correspondence. -/
def IsBayesianNashEquilibrium
    {State Signal Action : Type*} [Fintype State]
    (prior : State -> NNReal) (signal : Fin 2 -> State -> Signal)
    (utility : Fin 2 -> State -> Action -> Action -> Real)
    (profile : Fin 2 -> Signal -> Action) : Prop :=
  profile ∈ jointBestResponse prior signal utility profile

/-- The fixed-point definition unfolds componentwise to each player's
membership in its best-response set against the other player's policy. -/
theorem bayesian_nash_equilibrium_iff_fixed_point
    {State Signal Action : Type*} [Fintype State]
    (prior : State -> NNReal) (signal : Fin 2 -> State -> Signal)
    (utility : Fin 2 -> State -> Action -> Action -> Real)
    (profile : Fin 2 -> Signal -> Action) :
    IsBayesianNashEquilibrium prior signal utility profile <->
      forall player,
        profile player ∈
          bestResponses prior (signal player) (signal (otherPlayer player))
            (utility player) (profile (otherPlayer player)) := by
  rfl

/-- The joint best-response set is nonempty at every profile when the common
action space is finite and nonempty. This does not assert that a BNE exists. -/
theorem jointBestResponse_nonempty
    {State Signal Action : Type*}
    [Fintype State] [Finite Action] [Nonempty Action]
    (prior : State -> NNReal) (signal : Fin 2 -> State -> Signal)
    (utility : Fin 2 -> State -> Action -> Action -> Real)
    (profile : Fin 2 -> Signal -> Action) :
    (jointBestResponse prior signal utility profile).Nonempty := by
  classical
  choose candidate member using fun player : Fin 2 =>
    bestResponses_nonempty prior (signal player)
      (signal (otherPlayer player)) (utility player)
      (profile (otherPlayer player))
  exact ⟨candidate, member⟩

/-- In the one-agent self-response specialization, equilibrium has the literal
fixed-point form `policy ∈ BR policy`. -/
def IsSingleAgentBayesianEquilibrium
    {State Signal Action : Type*} [Fintype State]
    (prior : State -> NNReal) (signal : State -> Signal)
    (utility : State -> Action -> Action -> Real)
    (policy : Signal -> Action) : Prop :=
  policy ∈ bestResponses prior signal signal utility policy

theorem single_agent_bayesian_equilibrium_iff_fixed_point
    {State Signal Action : Type*} [Fintype State]
    (prior : State -> NNReal) (signal : State -> Signal)
    (utility : State -> Action -> Action -> Real)
    (policy : Signal -> Action) :
    IsSingleAgentBayesianEquilibrium prior signal utility policy <->
      policy ∈ bestResponses prior signal signal utility policy := by
  rfl

/-- Unit prior for the concrete two-player coordination game. -/
def coordinationPrior : Unit -> NNReal := fun _ => 1

/-- Both players receive the unique signal in the concrete game. -/
def coordinationSignal : Fin 2 -> Unit -> Unit := fun _ _ => ()

/-- Each player gets utility one exactly when its action matches the other's. -/
def coordinationUtility : Fin 2 -> Unit -> Bool -> Bool -> Real :=
  fun _ _ ownAction otherAction => if ownAction = otherAction then 1 else 0

/-- The all-false coordination profile. -/
def coordinationEquilibrium : Fin 2 -> Unit -> Bool := fun _ _ => false

/-- A mismatched profile: player zero selects false and player one selects true. -/
def coordinationMismatch : Fin 2 -> Unit -> Bool := fun player _ =>
  if player = 0 then false else true

/-- The all-false strategy profile is a Bayesian Nash equilibrium of the
two-player, two-action coordination game. -/
theorem coordination_false_profile_is_bayesian_nash :
    IsBayesianNashEquilibrium coordinationPrior coordinationSignal
      coordinationUtility coordinationEquilibrium := by
  rw [bayesian_nash_equilibrium_iff_fixed_point]
  intro player
  simp only [bestResponses, Set.mem_setOf_eq]
  intro observed _positive
  refine ⟨⟨false, rfl⟩, ?_⟩
  rintro _ ⟨action, rfl⟩
  cases action <;>
    norm_num [conditionalExpectedUtility, unnormalizedExpectedUtility,
      signalProbability, coordinationPrior, coordinationSignal,
      coordinationUtility, coordinationEquilibrium, otherPlayer]

/-- At the mismatched profile, player zero strictly improves by changing from
false to true and matching player one's action. -/
theorem coordination_mismatch_player_zero_strict_deviation :
    conditionalExpectedUtility coordinationPrior (coordinationSignal 0)
        (coordinationSignal 1) (coordinationUtility 0) () true
        (coordinationMismatch 1) >
      conditionalExpectedUtility coordinationPrior (coordinationSignal 0)
        (coordinationSignal 1) (coordinationUtility 0) () false
        (coordinationMismatch 1) := by
  norm_num [conditionalExpectedUtility, unnormalizedExpectedUtility,
    signalProbability, coordinationPrior, coordinationSignal,
    coordinationUtility, coordinationMismatch]

/-- The mismatched profile is not a BNE, as witnessed by player zero's strict
profitable deviation. -/
theorem coordination_mismatch_not_bayesian_nash :
    ¬ IsBayesianNashEquilibrium coordinationPrior coordinationSignal
      coordinationUtility coordinationMismatch := by
  intro equilibrium
  have component :=
    (bayesian_nash_equilibrium_iff_fixed_point coordinationPrior
      coordinationSignal coordinationUtility coordinationMismatch).mp
      equilibrium 0
  have response :
      coordinationMismatch 0 ∈
        bestResponses coordinationPrior (coordinationSignal 0)
          (coordinationSignal 1) (coordinationUtility 0)
          (coordinationMismatch 1) := by
    simpa [otherPlayer] using component
  have positive :
      0 < signalProbability coordinationPrior (coordinationSignal 0) () := by
    norm_num [signalProbability, coordinationPrior, coordinationSignal]
  have greatest := response () positive
  have alternativeMember :
      conditionalExpectedUtility coordinationPrior (coordinationSignal 0)
          (coordinationSignal 1) (coordinationUtility 0) () true
          (coordinationMismatch 1) ∈
        Set.range fun action =>
          conditionalExpectedUtility coordinationPrior (coordinationSignal 0)
            (coordinationSignal 1) (coordinationUtility 0) () action
            (coordinationMismatch 1) := ⟨true, rfl⟩
  have noImprovement := greatest.2 alternativeMember
  have comparison :
      conditionalExpectedUtility coordinationPrior (coordinationSignal 0)
          (coordinationSignal 1) (coordinationUtility 0) () true
          (coordinationMismatch 1) <=
        conditionalExpectedUtility coordinationPrior (coordinationSignal 0)
          (coordinationSignal 1) (coordinationUtility 0) () false
          (coordinationMismatch 1) := by
    simpa [coordinationMismatch] using noImprovement
  exact (not_lt_of_ge comparison)
    coordination_mismatch_player_zero_strict_deviation

#print axioms conditional_argmax_iff_unnormalized_argmax
#print axioms bestResponses_nonempty
#print axioms bayesian_nash_equilibrium_iff_fixed_point
#print axioms jointBestResponse_nonempty
#print axioms single_agent_bayesian_equilibrium_iff_fixed_point
#print axioms coordination_false_profile_is_bayesian_nash
#print axioms coordination_mismatch_player_zero_strict_deviation
#print axioms coordination_mismatch_not_bayesian_nash

end D5.S3.ConceptDynamics.DecisionValue.BayesianBestResponseFixedPoint
