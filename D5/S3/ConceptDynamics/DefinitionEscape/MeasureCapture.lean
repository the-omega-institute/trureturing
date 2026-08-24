/- GID: D5/S3/ConceptDynamics/DefinitionEscape/MeasureCapture
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/MeasureCapture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Arbitrary measures make residual-intersection capture submodular. -/

import Mathlib.MeasureTheory.Measure.Count

/- Library-search audit trail (2026-08-25):
   * Repository searches for `measure_capture_submodular`, arbitrary-set measure
     submodularity, and residual capture found no existing D5 theorem with this
     statement.
   * Pinned Mathlib supplies `measure_union_add_inter` when one set is measurable,
     plus `measure_union_toMeasurable`, `measure_toMeasurable`, and
     `subset_toMeasurable`.  Together they prove the arbitrary-set inequality
     without adding measurability assumptions to the residual or cuts. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.MeasureCapture

open MeasureTheory

/-- Every Mathlib measure is submodular on arbitrary sets.  A measurable hull
of the right set has the same measure and the same union measure; monotonicity
controls the possibly nonmeasurable intersection. -/
theorem measure_union_add_inter_le_arbitrary
    {Edge : Type*} [MeasurableSpace Edge] (nu : Measure Edge)
    (left right : Set Edge) :
    nu (left ∪ right) + nu (left ∩ right) ≤ nu left + nu right := by
  have intersection_le :
      nu (left ∩ right) ≤ nu (left ∩ toMeasurable nu right) :=
    measure_mono fun _ edge_in_intersection =>
      ⟨edge_in_intersection.1,
        subset_toMeasurable nu right edge_in_intersection.2⟩
  calc
    nu (left ∪ right) + nu (left ∩ right) =
        nu (left ∪ toMeasurable nu right) + nu (left ∩ right) := by
      rw [measure_union_toMeasurable]
    _ ≤ nu (left ∪ toMeasurable nu right) +
        nu (left ∩ toMeasurable nu right) :=
      add_le_add_right intersection_le _
    _ = nu left + nu (toMeasurable nu right) :=
      measure_union_add_inter left (measurableSet_toMeasurable nu right)
    _ = nu left + nu right := by rw [measure_toMeasurable]

/-- Measure of the residual edges captured by a definition set is submodular.
The residual and every cut are arbitrary sets; no measurability premise is
needed. -/
theorem measure_capture_submodular
    {Edge Definition : Type*} [MeasurableSpace Edge] (nu : Measure Edge)
    (residual : Set Edge) (cut : Definition → Set Edge)
    (A B : Set Definition) :
    let captured := fun S : Set Definition =>
      residual ∩ ⋃ definition ∈ S, cut definition
    nu (captured (A ∪ B)) + nu (captured (A ∩ B)) ≤
      nu (captured A) + nu (captured B) := by
  classical
  dsimp only
  let captured := fun S : Set Definition =>
    residual ∩ ⋃ definition ∈ S, cut definition
  change nu (captured (A ∪ B)) + nu (captured (A ∩ B)) ≤
    nu (captured A) + nu (captured B)
  have captured_union : captured (A ∪ B) = captured A ∪ captured B := by
    ext edge
    simp only [captured, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_union]
    aesop
  have captured_intersection_subset :
      captured (A ∩ B) ⊆ captured A ∩ captured B := by
    intro edge edge_captured
    simp only [captured, Set.mem_inter_iff, Set.mem_iUnion] at edge_captured ⊢
    aesop
  rw [captured_union]
  exact (add_le_add_right (measure_mono captured_intersection_subset) _).trans
    (measure_union_add_inter_le_arbitrary nu (captured A) (captured B))

#print axioms measure_capture_submodular
end D5.S3.ConceptDynamics.DefinitionEscape.MeasureCapture
