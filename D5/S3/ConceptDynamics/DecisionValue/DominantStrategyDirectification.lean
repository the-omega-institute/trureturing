/- GID: D5/S3/ConceptDynamics/DecisionValue/DominantStrategyDirectification
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValue/DominantStrategyDirectification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Dominant strategies induce truthful dominance in the direct mechanism. -/

import Mathlib.Data.Real.Basic

/- Library-search audit trail (2026-08-22):
   * Repository searches for dominant strategies, truthful reporting, direct
     mechanisms, direct revelation, and incentive compatibility found no exact
     theorem. `StrictSeparationImpossibility` and
     `ContributionIncentiveThreshold` use adjacent utility vocabulary but prove
     different statements and export no general mechanism carrier to reuse.
   * Pinned Mathlib searches for the same mechanism-design vocabulary were
     exact misses. Its exact `Function.update_self` and
     `Function.update_of_ne` lemmas transport a dependent strategy family
     across one agent-coordinate update and are applied directly below.
   * No exact pinned-Mathlib theorem packages the source directification. The
     `loogle` and `leansearch` executables were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DecisionValue.DominantStrategyDirectification

/-- For heterogeneous finite-agent type and message spaces, compose the
original mechanism with every agent's dominant strategy. In the resulting
direct mechanism, reporting the true type weakly dominates every alternative
report for every profile of the other agents' reports. -/
theorem dominant_strategy_directification
    {n : Nat}
    (TypeSpace Message : Fin n → Type*)
    {Outcome : Type*}
    (mechanism : (∀ i, Message i) → Outcome)
    (strategy : ∀ i, TypeSpace i → Message i)
    (utility : ∀ i, TypeSpace i → Outcome → Real)
    (dominant : ∀ (i) (trueType : TypeSpace i)
      (otherMessages : ∀ j, Message j) (alternative : Message i),
      utility i trueType
          (mechanism (Function.update otherMessages i (strategy i trueType))) ≥
        utility i trueType
          (mechanism (Function.update otherMessages i alternative))) :
    let directMechanism : (∀ i, TypeSpace i) → Outcome :=
      fun reports ↦ mechanism (fun i ↦ strategy i (reports i))
    ∀ (i) (trueType : TypeSpace i) (otherReports : ∀ j, TypeSpace j)
      (alternativeReport : TypeSpace i),
      utility i trueType
          (directMechanism (Function.update otherReports i trueType)) ≥
        utility i trueType
          (directMechanism (Function.update otherReports i alternativeReport)) := by
  dsimp
  intro i trueType otherReports alternativeReport
  have strategyUpdate (report : TypeSpace i) :
      (fun j ↦ strategy j ((Function.update otherReports i report) j)) =
        Function.update (fun j ↦ strategy j (otherReports j)) i
          (strategy i report) := by
    funext j
    by_cases sameAgent : j = i
    · subst j
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne sameAgent, Function.update_of_ne sameAgent]
  rw [strategyUpdate trueType, strategyUpdate alternativeReport]
  exact dominant i trueType (fun j ↦ strategy j (otherReports j))
    (strategy i alternativeReport)

/-- A one-agent unit mechanism satisfies the complete public hypothesis set,
and the theorem specializes to its truthful direct report. -/
example :
    let mechanism : (∀ _ : Fin 1, Unit) → Unit := fun _ ↦ ()
    let strategy : ∀ _ : Fin 1, Unit → Unit := fun _ _ ↦ ()
    let utility : ∀ _ : Fin 1, Unit → Unit → Real := fun _ _ _ ↦ 0
    let directMechanism : (∀ _ : Fin 1, Unit) → Unit :=
      fun reports ↦ mechanism (fun i ↦ strategy i (reports i))
    ∀ (i : Fin 1) (trueType : Unit) (otherReports : ∀ _ : Fin 1, Unit)
      (alternativeReport : Unit),
      utility i trueType
          (directMechanism (Function.update otherReports i trueType)) ≥
        utility i trueType
          (directMechanism (Function.update otherReports i alternativeReport)) := by
  apply dominant_strategy_directification
    (TypeSpace := fun _ : Fin 1 ↦ Unit)
    (Message := fun _ : Fin 1 ↦ Unit)
    (mechanism := fun _ ↦ ())
    (strategy := fun _ _ ↦ ())
    (utility := fun _ _ _ ↦ 0)
  simp

#print axioms dominant_strategy_directification

end D5.S3.ConceptDynamics.DecisionValue.DominantStrategyDirectification
