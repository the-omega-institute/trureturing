/- GID: D5/S0/Naming/Conservation/GreenMassDescriptionSeparation
   generality: G
   mirror-B: D5/B/S0/Naming/Conservation/GreenMassDescriptionSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Green mass and description cost vary independently on one binary table carrier. -/

import D5.S0.Computability.DescriptionComplexity.XorTransformationTightness
import D5.S0.Naming.Conservation.GreenClassNamingConservation

/- Library-search audit trail (2026-09-05):
   * D5 has exact owners for uniform Green-class mass, countable naming
     conservation, logarithmically described zero tables, and incompressible
     binary masks, but no theorem coupling their conclusions on one carrier.
   * `GreenClassNamingConservation.green_class_naming_conservation` and
     `XorTransformationTightness.xor_transformation_description_tight` are
     applied directly below. No source primitive is restated.
   * Pinned Mathlib supplies the finite-product measure and arithmetic APIs
     used by those owners, but no description-complexity model. Searches of
     the installed non-Mathlib packages found no matching coupling theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Naming.Conservation.GreenMassDescriptionSeparation

open MeasureTheory
open scoped ENNReal

open D5.S0.Computability.DescriptionComplexity.TransformationDescriptionBound
open D5.S0.Computability.DescriptionComplexity.XorTransformationTightness
open D5.S0.Naming
open D5.S0.Naming.GreenClassMeasure
open D5.S0.Naming.Conservation.GreenClassNamingConservation

noncomputable section

universe v

/-- Uniform Green mass and countable-name conservation coexist on the same
binary sequence carrier. Compressible zero tables retain the exact
budget-indexed mass at every length, while an incompressible table at the same
budget has that identical mass and strictly larger description complexity. -/
theorem green_mass_naming_conservation_and_description_separation
    {overhead : Nat} (machine : BinaryDescriptionMachine overhead)
    (S : Finset Nat) (t : Nat -> Fin 2) :
    letI : MeasureSpace (Nat -> Fin 2) := ⟨stringMeasure (Fin 2)⟩
    (forall {J : Type v} [Countable J]
      (systems : J -> NamingSystem (Nat -> Fin 2)),
      stringMeasure (Fin 2) (greenClass S t) =
          ((Fintype.card (Fin 2) : ENNReal))⁻¹ ^ S.card /\
        0 < stringMeasure (Fin 2) (greenClass S t) /\
        (Set.iUnion fun j => (systems j).named).Countable /\
        stringMeasure (Fin 2) (Set.iUnion fun j => (systems j).named) = 0 /\
        stringMeasure (Fin 2) (Set.iUnion fun j => (systems j).named)ᶜ = 1 /\
        forall j Q,
          stringMeasure (Fin 2)
            {x | exists name, name ∈ (systems j).layer Q /\
              (systems j).assignment name = some x}ᶜ = 1) /\
    (forall length,
      stringMeasure (Fin 2)
          (greenClass (Finset.range length) (fun _ => (0 : Fin 2))) =
          ((Fintype.card (Fin 2) : ENNReal))⁻¹ ^ length /\
        descriptionComplexity (machine.objects length)
            (0 : Fin length -> Fin 2) <=
          2 * Nat.log 2 (length + 1) + overhead) /\
    (forall length,
      2 * Nat.log 2 (length + 1) + overhead < length ->
      exists mask : Fin length -> Fin 2,
        exists target : Nat -> Fin 2,
          (forall i : Fin length, target i = mask i) /\
          descriptionComplexity (machine.objects length) (0 : Fin length -> Fin 2) <
            descriptionComplexity (machine.objects length) mask /\
          stringMeasure (Fin 2) (greenClass (Finset.range length) target) =
            ((Fintype.card (Fin 2) : ENNReal))⁻¹ ^ length /\
          stringMeasure (Fin 2)
              (greenClass (Finset.range length) (fun _ => (0 : Fin 2))) =
            ((Fintype.card (Fin 2) : ENNReal))⁻¹ ^ length) := by
  classical
  refine ⟨green_class_naming_conservation S t, ?_, ?_⟩
  · intro length
    constructor
    · simpa using
        greenClass_measure (O := Fin 2) (Finset.range length) (fun _ => (0 : Fin 2))
    · calc
        descriptionComplexity (machine.objects length) (0 : Fin length -> Fin 2) <=
            (machine.objects length).codeCost (machine.zeroCode length) := by
          unfold descriptionComplexity
          apply Nat.find_min'
          exact ⟨machine.zeroCode length, machine.zeroCode_realizes length, rfl⟩
        _ = (machine.zeroCode length).length := machine.object_cost length _
        _ <= 2 * Nat.log 2 (length + 1) + overhead :=
          machine.zeroCode_length_le length
  · intro length hgap
    obtain ⟨mask, hmask, _, _, _, _, _⟩ :=
      xor_transformation_description_tight machine length
    have hzero :
        descriptionComplexity (machine.objects length) (0 : Fin length -> Fin 2) <=
          2 * Nat.log 2 (length + 1) + overhead := by
      calc
        descriptionComplexity (machine.objects length) (0 : Fin length -> Fin 2) <=
            (machine.objects length).codeCost (machine.zeroCode length) := by
          unfold descriptionComplexity
          apply Nat.find_min'
          exact ⟨machine.zeroCode length, machine.zeroCode_realizes length, rfl⟩
        _ = (machine.zeroCode length).length := machine.object_cost length _
        _ <= 2 * Nat.log 2 (length + 1) + overhead :=
          machine.zeroCode_length_le length
    let target : Nat -> Fin 2 :=
      fun i => if h : i < length then mask ⟨i, h⟩ else 0
    refine ⟨mask, target, ?_, (hzero.trans_lt hgap).trans_le hmask, ?_, ?_⟩
    · intro i
      simp [target, i.isLt]
    · simpa using
        greenClass_measure (O := Fin 2) (Finset.range length) target
    · simpa using
        greenClass_measure (O := Fin 2) (Finset.range length) (fun _ => (0 : Fin 2))

#print axioms green_mass_naming_conservation_and_description_separation

end


end D5.S0.Naming.Conservation.GreenMassDescriptionSeparation
