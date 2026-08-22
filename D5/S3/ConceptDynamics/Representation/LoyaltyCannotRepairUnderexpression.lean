/- GID: D5/S3/ConceptDynamics/Representation/LoyaltyCannotRepairUnderexpression
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Representation/LoyaltyCannotRepairUnderexpression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A loyal mandate factorization can remain insufficient for its target. -/

import D5.S3.ConceptDynamics.Decision.MixedFiberZeroErrorImpossible
import D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionObstruction

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'loyalty_cannot_repair_underexpression' D5 Golden/Frozen/accepted`
     returned no matches.
   * The required search for `loyal|faithful|mandate|representation|delegate` under
     concept dynamics found adjacent faithfulness and representation results, but no
     theorem separating loyal factorization of `J` from pointwise sufficiency for `T`.
   * `mixed_fiber_zero_error_impossible` allows arbitrary state and evidence types but
     fixes decisions and targets to `Bool`; it proves a universal error disjunction, not
     the required existential loyal-but-insufficient instance. It is reused below for
     the concrete separation witness.
   * `history_sensitive_evaluation_not_outcome_reducible` works for an arbitrary target
     type and rules out factorization of a target that varies inside one interface fiber.
     It is reused to derive the general loyal-representation obstruction.
   * Pinned Mathlib provides `Function.factorsThrough_iff`, already used by the latter
     repository theorem. No further library machinery is needed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Representation.LoyaltyCannotRepairUnderexpression

open D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionObstruction
open D5.S3.ConceptDynamics.Decision.MixedFiberZeroErrorImpossible

/-- A representation is loyal to a mandate interface when it strictly factors through
that interface. -/
def RepresentationLoyal {State Mandate Target : Type*} (M : State -> Mandate)
    (J : State -> Target) : Prop :=
  ∃ j : Mandate -> Target, J = j ∘ M

/-- A representation is sufficient for a target when it agrees with that target at
every state. -/
def RepresentationSufficient {State Target : Type*} (J T : State -> Target) : Prop :=
  ∀ state, J state = T state

/-- A mandate collision between states with different targets forces every loyal
representation to be insufficient. -/
theorem loyal_representation_fails_under_collision {State Mandate Target : Type*}
    (M : State -> Mandate) (T J : State -> Target) (loyal : RepresentationLoyal M J)
    (underexpressed : ∃ x y, M x = M y ∧ T x ≠ T y) :
    ¬RepresentationSufficient J T := by
  intro sufficient
  obtain ⟨j, representationFactors⟩ := loyal
  apply history_sensitive_evaluation_not_outcome_reducible M T underexpressed
  refine ⟨j, ?_⟩
  funext state
  exact (sufficient state).symm.trans (congrFun representationFactors state)

/-- There exists a mandate interface and a representation that is fully loyal to it
but is not sufficient for the target, witnessing that loyalty does not imply
sufficiency. -/
theorem loyalty_cannot_repair_underexpression :
    ∃ (M : Bool -> Unit) (T J : Bool -> Bool),
      RepresentationLoyal M J ∧
        (∃ x y, M x = M y ∧ T x ≠ T y) ∧
          ¬RepresentationSufficient J T := by
  let M : Bool -> Unit := fun _ => ()
  let T : Bool -> Bool := id
  let J : Bool -> Bool := fun _ => false
  have loyal : RepresentationLoyal M J := by
    exact ⟨fun _ : Unit => false, rfl⟩
  have underexpressed : ∃ x y, M x = M y ∧ T x ≠ T y := by
    exact ⟨true, false, rfl, Ne.symm Bool.false_ne_true⟩
  have insufficient : ¬RepresentationSufficient J T := by
    intro sufficient
    rcases mixed_fiber_zero_error_impossible M T true false rfl rfl rfl
        (fun _ : Unit => false) with errorAtTrue | errorAtFalse
    · exact errorAtTrue (sufficient true)
    · exact errorAtFalse (sufficient false)
  exact ⟨M, T, J, loyal, underexpressed, insufficient⟩

example :
    RepresentationLoyal (fun _ : Bool => ()) (fun _ => false) ∧
      ¬RepresentationSufficient (fun _ : Bool => false) id := by
  constructor
  · exact ⟨fun _ : Unit => false, rfl⟩
  · intro sufficient
    exact Bool.false_ne_true (sufficient true)

#print axioms loyalty_cannot_repair_underexpression

end D5.S3.ConceptDynamics.Representation.LoyaltyCannotRepairUnderexpression
