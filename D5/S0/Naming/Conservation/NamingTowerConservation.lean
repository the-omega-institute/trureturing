/- GID: D5/S0/Naming/Conservation/NamingTowerConservation
   generality: G
   mirror-B: D5/B/S0/Naming/Conservation/NamingTowerConservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Countable naming towers leave a full-measure anonymous complement. -/

import D5.S0.Naming.NamingSystem
import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.NullMeasurable

namespace D5.S0.Naming.Conservation.NamingTowerConservation

open MeasureTheory

universe u v

set_option checkBinderAnnotations false in
/-- Even a countably infinite tower of naming systems has only countably many named points;
under an atomless sigma-finite measure its named union is null and its anonymous complement has
the measure of the whole carrier. -/
theorem countable_tower_anonymous_full_measure
    {X : Type u} [MeasureSpace X] [Uncountable X]
    [NoAtoms (volume : Measure X)] [SigmaFinite (volume : Measure X)]
    {J : Type v} [Countable J] (systems : J -> NamingSystem X) :
    (Set.iUnion fun j => (systems j).named).Countable /\
      volume (Set.iUnion fun j => (systems j).named) = 0 /\
      volume (Set.iUnion fun j => (systems j).named)ᶜ = volume (Set.univ : Set X) := by
  have named_countable : (Set.iUnion fun j => (systems j).named).Countable :=
    Set.countable_iUnion fun j =>
      D5.S0.Naming.named_countable (X := X) (systems j)
  have named_null : volume (Set.iUnion fun j => (systems j).named) = 0 :=
    @D5.S0.Naming.dark_side_conservation X _ _ ‹NoAtoms volume› _ J _ systems
  refine ⟨named_countable, named_null, ?_⟩
  have named_double_compl_null :
      volume (Set.iUnion fun j => (systems j).named)ᶜᶜ = 0 := by
    simpa only [compl_compl] using named_null
  simpa only [compl_compl] using
    (measure_of_measure_compl_eq_zero
      (μ := volume) (s := (Set.iUnion fun j => (systems j).named)ᶜ)
      named_double_compl_null)

/-- The theorem's carrier and countable tower-index domains are inhabited. -/
example : Nonempty (Real × Nat) := inferInstance

/-- A constant tower with no named points simultaneously witnesses all structural and measure
hypotheses on the real line. -/
example :
    let systems : Nat -> NamingSystem Real := fun _ =>
      { Name := Fin 1
        assignment := fun _ => none
        height := fun _ => 0
        finite_layer := fun _ => Set.toFinite _ }
    (Set.iUnion fun j => (systems j).named).Countable /\
      volume (Set.iUnion fun j => (systems j).named) = 0 /\
      volume (Set.iUnion fun j => (systems j).named)ᶜ = volume (Set.univ : Set Real) := by
  dsimp only
  exact @countable_tower_anonymous_full_measure Real _ _
    (show NoAtoms (volume : Measure Real) from
      { measure_singleton := fun x => measure_singleton x }) _ Nat _ _

end D5.S0.Naming.Conservation.NamingTowerConservation
