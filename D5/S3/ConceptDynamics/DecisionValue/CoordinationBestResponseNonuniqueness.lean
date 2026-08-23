/- GID: D5/S3/ConceptDynamics/DecisionValue/CoordinationBestResponseNonuniqueness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValue/CoordinationBestResponseNonuniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two coordination equilibria refute unique selection by local best responses. -/

import Mathlib.Tactic

/- Library-search audit trail (2026-08-23):
   * Repository searches found the adjacent threshold-public-good theorem, but
     its stability predicate is tied to a different cost-and-benefit utility.
   * No reusable generic equilibrium or best-response primitive exists in `D5`.
     The unilateral-deviation condition is therefore expanded in the public
     theorem statement instead of introducing a sibling family definition.
   * Pinned Mathlib searches for `NashEquilibrium`, `IsNash`, `NashStable`,
     `BestResponse`, and coordination found no game-theory declaration.
     The `loogle` and `leansearch` executables are absent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DecisionValue.CoordinationBestResponseNonuniqueness

/-- In the two-player equality-payoff coordination game, both constant action
profiles consist entirely of best responses, so local optimality does not
select a unique collective outcome. -/
theorem local_best_responses_do_not_select_unique_outcome
    (utility : Fin 2 -> (Fin 2 -> Bool) -> Nat)
    (hutility : ∀ player actions,
      utility player actions = if actions 0 = actions 1 then 1 else 0) :
    let locallyStable := fun actions : Fin 2 -> Bool =>
      ∀ (player : Fin 2) (alternative : Bool),
        utility player (Function.update actions player alternative) ≤
          utility player actions
    locallyStable (fun _ => false) ∧
      locallyStable (fun _ => true) ∧
      ¬ ∃! actions : Fin 2 -> Bool, locallyStable actions := by
  dsimp only
  have hzero : ∀ (player : Fin 2) (alternative : Bool),
      utility player
          (Function.update (fun _ : Fin 2 => false) player alternative) ≤
        utility player (fun _ : Fin 2 => false) := by
    intro player alternative
    fin_cases player <;> cases alternative <;>
      simp [hutility, Function.update]
  have hone : ∀ (player : Fin 2) (alternative : Bool),
      utility player
          (Function.update (fun _ : Fin 2 => true) player alternative) ≤
        utility player (fun _ : Fin 2 => true) := by
    intro player alternative
    fin_cases player <;> cases alternative <;>
      simp [hutility, Function.update]
  refine ⟨hzero, hone, ?_⟩
  rintro ⟨actions, _hstable, hunique⟩
  have hzeroActions : (fun _ : Fin 2 => false) = actions :=
    hunique _ hzero
  have honeActions : (fun _ : Fin 2 => true) = actions :=
    hunique _ hone
  have hprofiles : (fun _ : Fin 2 => false) = (fun _ : Fin 2 => true) :=
    hzeroActions.trans honeActions.symm
  have hfalseTrue : false = true := congrFun hprofiles 0
  exact Bool.false_ne_true hfalseTrue

example :
    ∃ utility : Fin 2 -> (Fin 2 -> Bool) -> Nat,
      ∀ player actions,
        utility player actions = if actions 0 = actions 1 then 1 else 0 := by
  exact ⟨fun _ actions => if actions 0 = actions 1 then 1 else 0,
    fun _ _ => rfl⟩

example : Fin 2 := 0

#print axioms local_best_responses_do_not_select_unique_outcome

end D5.S3.ConceptDynamics.DecisionValue.CoordinationBestResponseNonuniqueness
