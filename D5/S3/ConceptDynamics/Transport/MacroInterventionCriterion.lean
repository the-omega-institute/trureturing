/- GID: D5/S3/ConceptDynamics/Transport/MacroInterventionCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transport/MacroInterventionCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Macro interventions are characterized by empty carry. -/

import D5.S3.ConceptDynamics.Transport.FiniteReverseCriterion

/- Library-search audit trail (2026-08-21).
   * `rg -n -i "macro.*intervention|intervention.*carry|ICarry|effective image|
     effective_image|macro intervention|commut.*intervention" D5 Blueprint
     -g '*.lean' -g '*.scribe.cs'` found the exact repository precursor
     `FiniteReverseCriterion.finite_reverse_criterion` for the reverse implication.
   * `rg -n -i "ExistsUnique|range.*finite|finite.*range|Function\.Surjective|
     Set\.range|factor.*through|descend.*quotient" D5 -g '*.lean'` also found
     `DynamicsDescent.dynamics_descends_iff`, an adjacent quotient-level result.
   * `rg -n -i "existsUnique|Surjective.*exists|range.*Finite|FactorsThrough|
     factor.*through" .lake/packages/mathlib/Mathlib -g '*.lean'` found the
     range primitives reused by `FiniteReverseCriterion`, but no exact theorem
     packaging both implications of this intervention criterion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Transport.MacroInterventionCriterion

open D5.S3.ConceptDynamics.Transport.FiniteReverseCriterion

/-- A macro intervention on the ambient readout codomain makes the
process/readout square commute on every source state. -/
def MacroIntervention {X Y BC BD : Type*} (F : X → Y) (qC : X → BC)
    (qD : Y → BD) (G : BC → BD) : Prop :=
  ∀ x, G (qC x) = qD (F x)

/-- Existence of an ambient macro intervention forces the intervention carry
to be empty. Conversely, in the finite decidable model, empty carry determines
a unique macro intervention on the effective image of the current readout. -/
theorem macro_intervention_carry_criterion
    {X Y BC BD : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype BC] [DecidableEq BC]
    [Fintype BD] [DecidableEq BD]
    (F : X → Y) (qC : X → BC) (qD : Y → BD) :
    ((∃ G : BC → BD, MacroIntervention F qC qD G) →
        IsEmpty (Carry F qC qD)) ∧
      (IsEmpty (Carry F qC qD) →
        ∃! G : Set.range qC → BD, EffectiveImageDescent F qC qD G) := by
  constructor
  · rintro ⟨G, hG⟩
    constructor
    rintro ⟨⟨x, y⟩, hxy, hSeparated⟩
    apply hSeparated
    calc
      qD (F x) = G (qC x) := (hG x).symm
      _ = G (qC y) := congrArg G hxy
      _ = qD (F y) := hG y
  · exact finite_reverse_criterion F qC qD

/-- The finite Boolean model realizes both nonvacuous sides of the criterion. -/
example :
    (∃ G : Bool → Bool,
      MacroIntervention (fun x : Bool ↦ x) (fun x : Bool ↦ x)
        (fun x : Bool ↦ x) G) ∧
    IsEmpty
      (Carry (fun x : Bool ↦ x) (fun x : Bool ↦ x)
        (fun x : Bool ↦ x)) := by
  refine ⟨⟨id, ?_⟩, ?_⟩
  · intro x
    rfl
  · exact (macro_intervention_carry_criterion
      (fun x : Bool ↦ x) (fun x : Bool ↦ x) (fun x : Bool ↦ x)).1
      ⟨id, by intro x; rfl⟩

example : Set.range (fun x : Bool ↦ x) := ⟨true, true, rfl⟩

#print axioms macro_intervention_carry_criterion

end D5.S3.ConceptDynamics.Transport.MacroInterventionCriterion
