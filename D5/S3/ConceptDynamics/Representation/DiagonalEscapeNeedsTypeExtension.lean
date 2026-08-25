/- GID: D5/S3/ConceptDynamics/Representation/DiagonalEscapeNeedsTypeExtension
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Representation/DiagonalEscapeNeedsTypeExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Six pair witnesses separate four closures; empty and unit cases are audited. -/

import D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-25):
   * Repository searches found no prior definitions of state faithfulness or
     representation surjectivity.
   * `DeterministicInterfaceEquivalence.EffectiveDescent` is the exact existing
     dynamic-closure predicate and is reused below without a replacement definition.
   * The `D5/S0/Diagonal` family supplies typed self-application and Lawvere escape;
     `QualitativeEscape.escaped_of_fixedPointFree` is the closest repository theorem.
   * Pinned Mathlib supplies `Function.exists_fixed_point_of_surjective`, used to
     refute a Boolean evaluator that purports to encode every Boolean endomap.
   * `MinimalPredictiveCompletionQuotient` was read; its quotient descent result is
     adjacent, but it does not compare the four predicates formalized here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Representation.DiagonalEscapeNeedsTypeExtension

open D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence

/-- Different states have different interface readouts. -/
def StateFaithfulness {X B : Type*} (q : X -> B) : Prop :=
  Function.Injective q

/-- Every state is represented by at least one interface coordinate. -/
def RepresentationSurjectivity {X B : Type*} (g : B -> X) : Prop :=
  Function.Surjective g

/-- Every endomap has an internal code, so in particular the evaluator's diagonal
endomap has a code in the same type. -/
def SelfDescriptionClosure (X : Type*) : Prop :=
  ∃ evaluator : X -> X -> X, Function.Surjective evaluator

private theorem bool_not_self_description :
    ¬ SelfDescriptionClosure Bool := by
  rintro ⟨evaluator, hSurjective⟩
  obtain ⟨value, hFixed⟩ :=
    Function.exists_fixed_point_of_surjective evaluator hSurjective Bool.not
  cases value <;> simp at hFixed

/-- An injective Boolean readout does not make a constant representation map surjective. -/
theorem state_faithfulness_not_representation_surjectivity :
    StateFaithfulness (id : Bool -> Bool) ∧
      ¬ RepresentationSurjectivity (fun _ : Bool => false) := by
  constructor
  · intro x y hxy
    exact hxy
  · intro hSurjective
    obtain ⟨value, hValue⟩ := hSurjective true
    simp at hValue
#print axioms state_faithfulness_not_representation_surjectivity

/-- Constant readout dynamics descend although the readout is not injective. -/
theorem effective_descent_not_state_faithfulness :
    EffectiveDescent (fun _ : Bool => false) (id : Bool -> Bool) ∧
      ¬ StateFaithfulness (fun _ : Bool => false) := by
  constructor
  · apply ((deterministic_interface_sixfold_equivalence
      (fun _ : Bool => false) (id : Bool -> Bool)).out 1 0).mp
    intro x y _
    rfl
  · intro hInjective
    have hFalseTrue : false = true := hInjective rfl
    simp at hFalseTrue
#print axioms effective_descent_not_state_faithfulness

/-- An injective Boolean readout exists although Bool cannot encode all its endomaps. -/
theorem state_faithfulness_not_self_description_closure :
    StateFaithfulness (id : Bool -> Bool) ∧ ¬ SelfDescriptionClosure Bool := by
  constructor
  · intro x y hxy
    exact hxy
  · exact bool_not_self_description
#print axioms state_faithfulness_not_self_description_closure

/-- Identity dynamics descend although a constant representation map is not surjective. -/
theorem effective_descent_not_representation_surjectivity :
    EffectiveDescent (id : Bool -> Bool) (id : Bool -> Bool) ∧
      ¬ RepresentationSurjectivity (fun _ : Bool => false) := by
  constructor
  · apply ((deterministic_interface_sixfold_equivalence
      (id : Bool -> Bool) (id : Bool -> Bool)).out 1 0).mp
    intro x y hxy
    exact hxy
  · intro hSurjective
    obtain ⟨value, hValue⟩ := hSurjective true
    simp at hValue
#print axioms effective_descent_not_representation_surjectivity

/-- The identity representation is surjective although Bool cannot encode all endomaps. -/
theorem representation_surjectivity_not_self_description_closure :
    RepresentationSurjectivity (id : Bool -> Bool) ∧
      ¬ SelfDescriptionClosure Bool := by
  constructor
  · intro value
    exact ⟨value, rfl⟩
  · exact bool_not_self_description
#print axioms representation_surjectivity_not_self_description_closure

/-- Boolean negation descends along identity although Bool is not self-describing. -/
theorem effective_descent_not_self_description_closure :
    EffectiveDescent (id : Bool -> Bool) Bool.not ∧
      ¬ SelfDescriptionClosure Bool := by
  constructor
  · apply ((deterministic_interface_sixfold_equivalence
      (id : Bool -> Bool) Bool.not).out 1 0).mp
    intro x y hxy
    exact congrArg Bool.not hxy
  · exact bool_not_self_description
#print axioms effective_descent_not_self_description_closure

/-- On the empty type both identity maps and identity dynamics are closed, but no
internal code can represent its unique endomap. -/
theorem empty_degenerate_audit :
    StateFaithfulness (id : Empty -> Empty) ∧
      RepresentationSurjectivity (id : Empty -> Empty) ∧
      EffectiveDescent (id : Empty -> Empty) (id : Empty -> Empty) ∧
      ¬ SelfDescriptionClosure Empty := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    exact hxy
  · intro value
    exact ⟨value, rfl⟩
  · apply ((deterministic_interface_sixfold_equivalence
      (id : Empty -> Empty) (id : Empty -> Empty)).out 1 0).mp
    intro x y hxy
    exact hxy
  · rintro ⟨evaluator, hSurjective⟩
    obtain ⟨code, _⟩ := hSurjective (id : Empty -> Empty)
    exact code.elim
#print axioms empty_degenerate_audit

/-- On the singleton type identity readout, representation, dynamics, and a constant
evaluator satisfy all four closure predicates. -/
theorem unit_degenerate_audit :
    StateFaithfulness (id : Unit -> Unit) ∧
      RepresentationSurjectivity (id : Unit -> Unit) ∧
      EffectiveDescent (id : Unit -> Unit) (id : Unit -> Unit) ∧
      SelfDescriptionClosure Unit := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y _
    exact Subsingleton.elim x y
  · intro value
    exact ⟨value, rfl⟩
  · apply ((deterministic_interface_sixfold_equivalence
      (id : Unit -> Unit) (id : Unit -> Unit)).out 1 0).mp
    intro x y _
    exact Subsingleton.elim x y
  · refine ⟨fun _ _ => (), ?_⟩
    intro endomap
    refine ⟨(), ?_⟩
    funext value
    exact Subsingleton.elim _ _
#print axioms unit_degenerate_audit

end D5.S3.ConceptDynamics.Representation.DiagonalEscapeNeedsTypeExtension
