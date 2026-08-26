/- GID: D5/S3/ConceptDynamics/Transportability/MacroInterventionCarryCharacterization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transportability/MacroInterventionCarryCharacterization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Intervention carry characterizes effective-image macro descent. -/

import D5.S3.ConceptDynamics.Transport.MacroInterventionCriterion

/- Library-search audit trail (2026-08-26).
   * The frozen `MacroInterventionCriterion` family supplies the canonical
     `MacroIntervention`, `Carry`, and `EffectiveImageDescent` primitives. Its
     theorem is not an exact hit because global finite/decidable instances
     unnecessarily restrict the forward implication and it omits the explicit
     carry-witness clause.
   * Repository searches for the source-shaped three-clause criterion found no
     exact hit. `FiniteReverseCriterion.finite_reverse_criterion` has the right
     unique effective-image conclusion but carries unused finite hypotheses.
   * Pinned Mathlib has no macro-intervention theorem. Exact support hits
     `Set.rangeFactorization`, `Set.rangeSplitting`, and
     `Set.apply_rangeSplitting` construct and verify the effective-image map. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Transportability.MacroInterventionCarryCharacterization

open D5.S3.ConceptDynamics.Transport.FiniteReverseCriterion
open D5.S3.ConceptDynamics.Transport.MacroInterventionCriterion

/-- An ambient macro intervention excludes intervention carry. Conversely,
empty carry determines a unique intervention on the realized image. A concrete
carry inhabitant is therefore an explicit witness that no ambient macro
intervention exists. -/
theorem macro_intervention_carry_characterization
    {X Z : Type*} (F : X -> X) (C : X -> Z) :
    ((∃ G : Z -> Z, MacroIntervention F C C G) ->
        IsEmpty (Carry F C C)) /\
      (IsEmpty (Carry F C C) ->
        ∃! G : Set.range C -> Z, EffectiveImageDescent F C C G) /\
      (Carry F C C ->
        ¬ ∃ G : Z -> Z, MacroIntervention F C C G) := by
  have forward :
      (∃ G : Z -> Z, MacroIntervention F C C G) ->
        IsEmpty (Carry F C C) := by
    rintro ⟨G, hG⟩
    constructor
    rintro ⟨⟨x, y⟩, hxy, hSeparated⟩
    apply hSeparated
    calc
      C (F x) = G (C x) := (hG x).symm
      _ = G (C y) := congrArg G hxy
      _ = C (F y) := hG y
  refine ⟨forward, ?_, ?_⟩
  · intro carryEmpty
    let intervention : Set.range C -> Z := fun value =>
      C (F (Set.rangeSplitting C value))
    have hIntervention : EffectiveImageDescent F C C intervention := by
      intro x
      have hC :
          C (Set.rangeSplitting C (Set.rangeFactorization C x)) = C x := by
        simpa using Set.apply_rangeSplitting C (Set.rangeFactorization C x)
      by_contra hne
      exact carryEmpty.false
        ⟨(Set.rangeSplitting C (Set.rangeFactorization C x), x), hC, hne⟩
    refine ⟨intervention, hIntervention, ?_⟩
    intro candidate hCandidate
    funext value
    obtain ⟨x, hx⟩ := value.property
    have hValue : Set.rangeFactorization C x = value := Subtype.ext hx
    rw [<- hValue]
    exact (hCandidate x).trans (hIntervention x).symm
  · intro carryWitness ambientIntervention
    exact (forward ambientIntervention).false carryWitness

/-- The forward premise and empty-carry conclusion are jointly inhabited. -/
example :
    (∃ G : Bool -> Bool,
      MacroIntervention (fun x : Bool => x) (fun x : Bool => x)
        (fun x : Bool => x) G) /\
    IsEmpty
      (Carry (fun x : Bool => x) (fun x : Bool => x)
        (fun x : Bool => x)) := by
  have ambient :
      ∃ G : Bool -> Bool,
        MacroIntervention (fun x : Bool => x) (fun x : Bool => x)
          (fun x : Bool => x) G := ⟨id, by intro x; rfl⟩
  exact ⟨ambient,
    (macro_intervention_carry_characterization
      (fun x : Bool => x) (fun x : Bool => x)).1 ambient⟩

/-- The canonical effective image used by the reverse clause is inhabited. -/
example : Set.range (fun x : Bool => x) := ⟨true, true, rfl⟩

/-- Swapping coordinates supplies an actual intervention-carry witness. -/
example : Carry (fun p : Bool × Bool => (p.2, p.1)) Prod.fst Prod.fst :=
  ⟨((false, false), (false, true)), rfl, by decide⟩

/-- The same concrete carry type is the premise of the public nonexistence
clause, ruling out an ambient intervention through the concept readout. -/
example
    (carryWitness :
      Carry (fun p : Bool × Bool => (p.2, p.1)) Prod.fst Prod.fst) :
    ¬ ∃ G : Bool -> Bool,
      MacroIntervention (fun p : Bool × Bool => (p.2, p.1))
        Prod.fst Prod.fst G :=
  (macro_intervention_carry_characterization
    (fun p : Bool × Bool => (p.2, p.1)) Prod.fst).2.2 carryWitness

#print axioms macro_intervention_carry_characterization

end D5.S3.ConceptDynamics.Transportability.MacroInterventionCarryCharacterization
