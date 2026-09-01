/- GID: D5/S0/Naming/Conservation/GreenClassNamingConservation
   generality: G
   mirror-B: D5/B/S0/Naming/Conservation/GreenClassNamingConservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Uniform Green mass and countable-name conservation share one product carrier. -/

import D5.S0.Asymptotics.MetricGeometry.GreenClassHausdorffDimension
import D5.S0.Naming.Conservation.NamingTowerConservation

namespace D5.S0.Naming.Conservation.GreenClassNamingConservation

open MeasureTheory
open D5.S0.Asymptotics.MetricGeometry.GreenClassHausdorffDimension
open D5.S0.Naming.GreenClassMeasure
open D5.S0.Naming.Conservation.NamingTowerConservation
open scoped ENNReal

noncomputable section

universe v

/-- A finite Green certificate over a uniform nontrivial alphabet has exact
positive mass depending only on its budget. On the same product carrier, a
countable family of naming systems names only a null countable set; its
anonymous complement and every finite height layer's complement have full
measure. -/
theorem green_class_naming_conservation
    {O : Type*} [Fintype O] [Nonempty O] [Nontrivial O]
    [MeasurableSpace O] [MeasurableSingletonClass O]
    [TopologicalSpace O] [DiscreteTopology O]
    (S : Finset Nat) (t : Nat -> O) :
    letI : MeasureSpace (Nat -> O) := ⟨stringMeasure O⟩
    ∀ {J : Type v} [Countable J] (systems : J -> NamingSystem (Nat -> O)),
      stringMeasure O (greenClass S t) =
          ((Fintype.card O : ENNReal))⁻¹ ^ S.card ∧
        0 < stringMeasure O (greenClass S t) ∧
        (Set.iUnion fun j => (systems j).named).Countable ∧
        stringMeasure O (Set.iUnion fun j => (systems j).named) = 0 ∧
        stringMeasure O (Set.iUnion fun j => (systems j).named)ᶜ = 1 ∧
        ∀ j Q,
          stringMeasure O
            {x | ∃ name ∈ (systems j).layer Q,
              (systems j).assignment name = some x}ᶜ = 1 := by
  letI : MeasureSpace (Nat -> O) := ⟨stringMeasure O⟩
  intro J countableJ systems
  letI : Countable J := countableJ
  have namingDimensionPositive : 0 < namingDim O := by
    exact Real.logb_pos (by norm_num : (1 : Real) < 2)
      (by exact_mod_cast Fintype.one_lt_card (α := O))
  have singletonZero (x : Nat -> O) : stringMeasure O {x} = 0 := by
    have diameterBound := stringMeasure_le_ediam_rpow (O := O) ({x} : Set (Nat -> O))
    simpa [ENNReal.zero_rpow_of_pos namingDimensionPositive] using diameterBound
  let volumeNoAtoms : NullSingletonClass (volume : Measure (Nat -> O)) :=
    ⟨singletonZero⟩
  letI : NullSingletonClass (volume : Measure (Nat -> O)) := volumeNoAtoms
  letI : IsProbabilityMeasure (stringMeasure O) := by
    rw [stringMeasure]
    infer_instance
  letI : Uncountable (Nat -> O) := ⟨by
    intro countableCarrier
    letI : Countable (Nat -> O) := countableCarrier
    have univZero :=
      Set.countable_univ.measure_zero (volume : Measure (Nat -> O))
    rw [measure_univ] at univZero
    exact one_ne_zero univZero⟩
  have towerResult :=
    @countable_tower_anonymous_full_measure (Nat -> O) _ _ volumeNoAtoms _ J
      countableJ systems
  have volumeEqualsStringMeasure :
      (volume : Measure (Nat -> O)) = stringMeasure O := rfl
  rw [volumeEqualsStringMeasure] at towerResult
  refine ⟨greenClass_measure S t, greenClass_measure_pos S t,
    towerResult.1, towerResult.2.1, ?_, ?_⟩
  · simpa using towerResult.2.2
  · intro j Q
    let layerImage : Set (Nat -> O) :=
      {x | ∃ name ∈ (systems j).layer Q,
        (systems j).assignment name = some x}
    have layerSubset : layerImage ⊆ Set.iUnion fun k => (systems k).named := by
      rintro x ⟨name, _, assignment⟩
      rw [Set.mem_iUnion]
      exact ⟨j, name, assignment⟩
    have layerNull : stringMeasure O layerImage = 0 :=
      measure_mono_null layerSubset towerResult.2.1
    have doubleComplementNull : stringMeasure O layerImageᶜᶜ = 0 := by
      simpa only [compl_compl] using layerNull
    simpa only [layerImage, compl_compl, measure_univ] using
      (measure_of_measure_compl_eq_zero
        (μ := stringMeasure O) (s := layerImageᶜ) doubleComplementNull)

end

end D5.S0.Naming.Conservation.GreenClassNamingConservation
