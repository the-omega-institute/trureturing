/- GID: D5/S3/ConceptDynamics/Modularity/InterfaceInsufficiency
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Modularity/InterfaceInsufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Componentwise-equal interfaces cannot verify a differing global target. -/

import D5.S3.ConceptDynamics.Contestability.InvisibleDefectUnrepairable

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'modular_interfaces_cannot_verify_global_target' \`
     `D5 Golden/Frozen/accepted` returned no matches.
   * Searching `challenge_blind|review_exists` under `D5/S3/ConceptDynamics`
     found `challenge_blind_review_cannot_separate` and its coverage iff only in
     `Contestability/InvisibleDefectUnrepairable.lean`.
   * The main proof specializes that obstruction to a unit-indexed challenge whose
     response is the product of the two component interfaces; the component
     equalities construct the required equality of challenge responses.
   * No theorem already exposing this componentwise product structure was found.
     The positive direction below uses function composition and congruence only. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Modularity.InterfaceInsufficiency

open D5.S3.ConceptDynamics.Contestability.InvisibleDefectUnrepairable

/-- The public interface of a composite state reads each component separately. -/
def jointInterface {X₁ X₂ Interface₁ Interface₂ : Type*}
    (C₁ : X₁ -> Interface₁) (C₂ : X₂ -> Interface₂) :
    X₁ × X₂ -> Interface₁ × Interface₂ :=
  fun state => (C₁ state.1, C₂ state.2)

/-- A verifier is interface-blind when equal public component interfaces force equal
verification results. -/
def InterfaceBlind {X₁ X₂ Interface₁ Interface₂ Target : Type*}
    (C₁ : X₁ -> Interface₁) (C₂ : X₂ -> Interface₂)
    (verify : X₁ × X₂ -> Target) : Prop :=
  ChallengeBlind (fun (_ : Unit) => jointInterface C₁ C₂) verify

/-- Componentwise interface equality cannot support a correct verifier when the
global target distinguishes the corresponding composite states. -/
theorem modular_interfaces_cannot_verify_global_target
    {X₁ X₂ Interface₁ Interface₂ Target : Type*}
    (C₁ : X₁ -> Interface₁) (C₂ : X₂ -> Interface₂)
    (T : X₁ × X₂ -> Target) (x₁ y₁ : X₁) (x₂ y₂ : X₂)
    (same₁ : C₁ x₁ = C₁ y₁) (same₂ : C₂ x₂ = C₂ y₂)
    (different : T (x₁, x₂) ≠ T (y₁, y₂)) :
    ¬(∃ verify : X₁ × X₂ -> Target,
      InterfaceBlind C₁ C₂ verify ∧ ∀ state, verify state = T state) := by
  apply challenge_blind_review_cannot_separate
    (fun (_ : Unit) => jointInterface C₁ C₂) T (x₁, x₂) (y₁, y₂)
  · intro _
    exact congrArg₂ (fun first second => (first, second)) same₁ same₂
  · exact different

/-- A global target that factors through the joint public interface has a correct
interface-blind verifier. -/
theorem factorized_target_has_interface_blind_verifier
    {X₁ X₂ Interface₁ Interface₂ Target : Type*}
    (C₁ : X₁ -> Interface₁) (C₂ : X₂ -> Interface₂)
    (T : X₁ × X₂ -> Target)
    (factorization : ∃ f : Interface₁ × Interface₂ -> Target,
      T = f ∘ jointInterface C₁ C₂) :
    ∃ verify : X₁ × X₂ -> Target,
      InterfaceBlind C₁ C₂ verify ∧ ∀ state, verify state = T state := by
  rcases factorization with ⟨f, hT⟩
  refine ⟨f ∘ jointInterface C₁ C₂, ?_, ?_⟩
  · intro s t sameResponses
    exact congrArg f (sameResponses ())
  · intro state
    exact (congrFun hT state).symm

/-- Constant component interfaces hide the Boolean conjunction target on two
explicit composite states. -/
theorem constant_bool_interfaces_cannot_verify_conjunction :
    ¬(∃ verify : Bool × Bool -> Bool,
      InterfaceBlind (fun _ : Bool => ()) (fun _ : Bool => ()) verify ∧
        ∀ state, verify state = (fun p : Bool × Bool => p.1 && p.2) state) := by
  apply modular_interfaces_cannot_verify_global_target
    (fun _ : Bool => ()) (fun _ : Bool => ())
    (fun p : Bool × Bool => p.1 && p.2) true false true false
  · rfl
  · rfl
  · decide

example :
    ¬(∃ verify : Bool × Bool -> Bool,
      InterfaceBlind (fun _ : Bool => ()) (fun _ : Bool => ()) verify ∧
        ∀ state, verify state = (fun p : Bool × Bool => p.1 && p.2) state) :=
  constant_bool_interfaces_cannot_verify_conjunction

#print axioms modular_interfaces_cannot_verify_global_target

end D5.S3.ConceptDynamics.Modularity.InterfaceInsufficiency
