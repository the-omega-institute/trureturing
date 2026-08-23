/- GID: D5/S3/ConceptDynamics/Decision/MixedFiberZeroErrorImpossible
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Decision/MixedFiberZeroErrorImpossible
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Opposite labels in one evidence fiber force a tight one-of-two decision error. -/

import Mathlib.Data.Bool.Basic

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'mixed_fiber_zero_error_impossible' D5 Golden/Frozen/accepted`
     returned no matches.
   * The required `zero.*error|decision|mixed.*fiber|Bayes` search under concept
     dynamics found related decision modules and `SafeAnswerCoverageMaximality`, but no
     theorem asserting an error for every deterministic rule on a mixed fiber.
   * `SafeAnswerCoverageMaximality` concerns an Option-valued canonical answerer, an
     admission predicate, and maximal answer coverage on inhabited fibers. This theorem
     instead quantifies over every total `Evidence -> Bool` rule and rules out zero error
     on two oppositely labelled states with identical evidence, so the results do not
     duplicate one another and its fiber/admission definitions do not apply here.
   * Pinned Mathlib has general `hammingDist` machinery, but no theorem with this
     two-state mixed-fiber shape. The proof uses function congruence, Bool constructors,
     equality transitivity, and arithmetic simplification of the explicit two-point count.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Decision.MixedFiberZeroErrorImpossible

/-- Whether a deterministic evidence-based decision is wrong at one state. -/
def decisionError {State Evidence : Type*} (evidence : State -> Evidence)
    (label : State -> Bool) (decide : Evidence -> Bool) (state : State) : Bool :=
  decide (evidence state) != label state

/-- The number of errors made by a decision rule on the ordered pair `(x, y)`. -/
def pairErrorCount {State Evidence : Type*} (evidence : State -> Evidence)
    (label : State -> Bool) (decide : Evidence -> Bool) (x y : State) : Nat :=
  (decisionError evidence label decide x).toNat +
    (decisionError evidence label decide y).toNat

/-- If one evidence fiber contains a positive and a negative state, every deterministic
decision rule that sees only evidence is wrong on at least one of those states. The
universal quantifier over `decide` expresses insufficiency of the evidence interface,
not a limitation of a particular decision maker. -/
theorem mixed_fiber_zero_error_impossible {State Evidence : Type*}
    (evidence : State -> Evidence) (label : State -> Bool) (x y : State)
    (sameEvidence : evidence x = evidence y) (positive : label x = true)
    (negative : label y = false) :
    forall decide : Evidence -> Bool,
      decide (evidence x) ≠ label x ∨ decide (evidence y) ≠ label y := by
  intro decide
  by_cases correctAtX : decide (evidence x) = label x
  · right
    intro correctAtY
    have labelsEqual : label x = label y := by
      calc
        label x = decide (evidence x) := correctAtX.symm
        _ = decide (evidence y) := congrArg decide sameEvidence
        _ = label y := correctAtY
    exact Bool.noConfusion (positive.symm.trans (labelsEqual.trans negative))
  · exact Or.inl correctAtX

/-- The one-error lower bound is sharp: every rule makes at least one error on the pair,
and a constant rule attains exactly one error. -/
theorem mixed_fiber_error_bound_is_tight {State Evidence : Type*}
    (evidence : State -> Evidence) (label : State -> Bool) (x y : State)
    (sameEvidence : evidence x = evidence y) (positive : label x = true)
    (negative : label y = false) :
    (forall decide : Evidence -> Bool, 1 <= pairErrorCount evidence label decide x y) ∧
      exists decide : Evidence -> Bool, pairErrorCount evidence label decide x y = 1 := by
  constructor
  · intro decide
    rcases mixed_fiber_zero_error_impossible evidence label x y sameEvidence positive
        negative decide with errorAtX | errorAtY
    · have errorBitAtX : decisionError evidence label decide x = true := by
        simp [decisionError, errorAtX]
      rw [pairErrorCount, errorBitAtX]
      simp
    · have errorBitAtY : decisionError evidence label decide y = true := by
        simp [decisionError, errorAtY]
      rw [pairErrorCount, errorBitAtY]
      simp
  · refine ⟨(fun _ => true), ?_⟩
    simp [pairErrorCount, decisionError, positive, negative]

example :
    forall decide : Bool -> Bool,
      decide false ≠ (fun state : Bool => state) true ∨
        decide false ≠ (fun state : Bool => state) false := by
  exact mixed_fiber_zero_error_impossible (fun _ : Bool => false)
    (fun state : Bool => state) true false rfl rfl rfl

#print axioms mixed_fiber_zero_error_impossible

end D5.S3.ConceptDynamics.Decision.MixedFiberZeroErrorImpossible
