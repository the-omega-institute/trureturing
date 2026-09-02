/- GID: D5/S3/ConceptDynamics/Epistemic/GettierWitness
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Epistemic/GettierWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Gettier belief admits a same-evidence counterexample. -/

import Mathlib.Data.Nat.Basic

/- Library-search audit trail (2026-09-02):
   * Exact repository searches for `Gettier` returned no declaration. Searches
     for belief, justification, and epistemic truth found the adjacent
     `robustKnowledge`, whose fiberwise truth excludes the false same-evidence
     witness required here, so it is not an exact reusable primitive.
   * Pinned Mathlib searches for `Gettier` and `justified true belief` returned
     no declaration. Loogle's quoted-name query returned zero declarations.
   * LeanSearch's first ten natural-language results were generic facts and
     propositional simplifications, not an epistemic or Gettier definition.
     The atom-specific predicate therefore uses only core conjunction,
     equality, negation, and existential quantification. -/

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Epistemic.GettierWitness

/-- A Gettier witness is true and believed with justification at the anchor,
while an admissible state with the same evidence falsifies the predicate. The
belief operator explicitly receives the evidence map represented by its source
subscript. -/
def gettier {X B : Type*}
    (predicate : X -> Prop) (evidence : X -> B)
    (belief : (X -> B) -> (X -> Prop) -> X -> Prop)
    (justified : B -> (X -> Prop) -> Prop)
    (admissible : X -> Prop) (anchor : X) : Prop :=
  predicate anchor /\
    belief evidence predicate anchor /\
    justified (evidence anchor) predicate /\
    Exists fun witness =>
      admissible witness /\
        evidence witness = evidence anchor /\
        Not (predicate witness)

/-- The public predicate unfolds to exactly the seven visible source clauses. -/
theorem gettier_iff {X B : Type*}
    (predicate : X -> Prop) (evidence : X -> B)
    (belief : (X -> B) -> (X -> Prop) -> X -> Prop)
    (justified : B -> (X -> Prop) -> Prop)
    (admissible : X -> Prop) (anchor : X) :
    Iff (gettier predicate evidence belief justified admissible anchor)
      (predicate anchor /\
        belief evidence predicate anchor /\
        justified (evidence anchor) predicate /\
        Exists fun witness =>
          admissible witness /\
            evidence witness = evidence anchor /\
            Not (predicate witness)) :=
  Iff.rfl

/-- The definition is nontrivial. With truth concentrated at `0`, constant
evidence `7`, and admissible counterexample `1`, belief at `0` gives a Gettier
witness. Changing only the belief predicate to require anchor `1` makes the
same anchor fail the definition. -/
theorem gettier_concrete_examples :
    let predicate : Nat -> Prop := fun n => n = 0
    let evidence : Nat -> Nat := fun _ => 7
    let beliefAtZero : (Nat -> Nat) -> (Nat -> Prop) -> Nat -> Prop :=
      fun _ _ n => n = 0
    let beliefAtOne : (Nat -> Nat) -> (Nat -> Prop) -> Nat -> Prop :=
      fun _ _ n => n = 1
    let justified : Nat -> (Nat -> Prop) -> Prop :=
      fun value _ => value = 7
    let admissible : Nat -> Prop := fun n => n = 1
    gettier predicate evidence beliefAtZero justified admissible 0 /\
      Not (gettier predicate evidence beliefAtOne justified admissible 0) := by
  dsimp only [gettier]
  constructor
  · exact ⟨rfl, rfl, rfl, 1, rfl, rfl, Nat.one_ne_zero⟩
  · rintro ⟨_, impossible, _, _⟩
    exact Nat.zero_ne_one impossible

#print axioms gettier_concrete_examples

end D5.S3.ConceptDynamics.Epistemic.GettierWitness
