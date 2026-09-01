/- GID: D5/S0/Naming/Conservation/PositiveMeasureJurisdiction
   generality: G
   mirror-B: D5/B/S0/Naming/Conservation/PositiveMeasureJurisdiction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive-measure naming jurisdictions contain uncountably many source points. -/

import D5.S0.Naming.NamingSystem
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/- Library-search audit trail (2026-08-15):
   * Pinned Mathlib provides the exact nullity lemma `Set.Countable.measure_zero` for atomless
     measures. The proof applies it directly rather than reproving countable-set nullity.
   * Pinned-Mathlib searches found no rate-distortion API and no theorem already phrased for a
     naming-system jurisdiction. Repository searches found null named images and finite naming
     layers, but no positive-measure-fiber uncountability declaration.
-/

namespace D5.S0.Naming.Conservation.PositiveMeasureJurisdiction

open MeasureTheory

universe u

set_option checkBinderAnnotations false in
/-- A jurisdiction is the source fiber assigned to one name by an encoder. Under an atomless
measure, positive measure forces that fiber to contain more than countably many source points. -/
theorem positive_measure_jurisdiction_uncountable
    {X : Type u} [MeasureSpace X] [NoAtoms (volume : Measure X)]
    (system : NamingSystem X) (encode : X -> system.Name) (name : system.Name)
    (positive : 0 < volume (encode ⁻¹' {name})) :
    ¬ (encode ⁻¹' {name}).Countable := by
  intro countable
  exact (ne_of_gt positive) (@Set.Countable.measure_zero X _ _ countable volume ‹NoAtoms volume›)

/- The hypotheses are jointly inhabited: a constant encoding of the real line has the whole
source as its sole jurisdiction, which has positive volume. -/
example :
    let system : NamingSystem Real :=
      { Name := Unit
        assignment := fun _ => none
        height := fun _ => 0
        finite_layer := fun _ => Set.toFinite _ }
    ∃ encode : Real -> system.Name, ∃ name : system.Name,
      0 < volume (encode ⁻¹' {name}) := by
  dsimp only
  refine ⟨fun _ => (), (), ?_⟩
  simp

#print axioms positive_measure_jurisdiction_uncountable

end D5.S0.Naming.Conservation.PositiveMeasureJurisdiction
