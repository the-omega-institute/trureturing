/- GID: D5/S3/ConceptDynamics/DefinitionCapture/MeasureCapture
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionCapture/MeasureCapture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Additive weights make residual-intersection capture submodular. -/

import D5.S3.AnalyticClosure.Budget.BudgetedEscapeRateAntitone
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Real

/- Library-search audit trail (2026-08-25):
   * Repository searches found the frozen `EscapeWeight` interface, whose mass,
     empty-mass, and nonnegativity fields already cover the source parameter's
     weight, count, and measure branches, but no capture-additivity law.
   * Pinned Mathlib supplies `measure_union_add_inter` when one set is measurable,
     plus `measure_union_toMeasurable`, `measure_toMeasurable`, and
     `subset_toMeasurable`. It also supplies `Set.ncard_union_add_ncard_inter`
     and `Set.ncard_le_ncard`. These prove the one extra law below for finite
     counting and finite measures; a positive point weight supplies a genuinely
     weighted instance. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionCapture.MeasureCapture

open D5.S3.AnalyticClosure.Budget.BudgetedEscapeRateAntitone
open MeasureTheory

/-- Every Mathlib measure is submodular on arbitrary sets.  A measurable hull
of the right set has the same measure and the same union measure; monotonicity
controls the possibly nonmeasurable intersection. -/
theorem measure_union_add_inter_le_arbitrary
    {Omega : Type*} [MeasurableSpace Omega] (nu : Measure Omega)
    (left right : Set Omega) :
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

/-- An `EscapeWeight` with the single extra law needed by capture: finite
additivity and nonnegativity imply this inequality by combining set
submodularity with monotonicity. Counting, nonnegative point weights, and finite
measures all satisfy it. -/
structure CaptureWeight (Omega : Type*) extends EscapeWeight Omega where
  mass_union_add_lower_le : forall (left right lower : Set Omega),
    lower ⊆ left ∩ right ->
      mass (left ∪ right) + mass lower ≤ mass left + mass right

/-- Finite counting realizes the CAS count branch as real-valued `Set.ncard`. -/
noncomputable def countingCaptureWeight (Omega : Type*) [Finite Omega] :
    CaptureWeight Omega where
  mass := fun set => set.ncard
  empty_mass := by simp
  mass_nonnegative := by intro set; positivity
  mass_union_add_lower_le := by
    intro left right lower lower_subset
    have lower_card_le : lower.ncard ≤ (left ∩ right).ncard :=
      Set.ncard_le_ncard lower_subset
    exact_mod_cast
      (calc
        (left ∪ right).ncard + lower.ncard ≤
            (left ∪ right).ncard + (left ∩ right).ncard :=
          Nat.add_le_add_left lower_card_le _
        _ = left.ncard + right.ncard :=
          Set.ncard_union_add_ncard_inter left right)

/-- A nonzero, non-counting weight: sets containing `true` have mass two. -/
noncomputable def nontrivialPointCaptureWeight : CaptureWeight Bool := by
  classical
  exact
    { mass := fun set => if true ∈ set then 2 else 0
      empty_mass := by simp
      mass_nonnegative := by
        intro set
        split <;> norm_num
      mass_union_add_lower_le := by
        intro left right lower lower_subset
        have lower_membership :
            true ∈ lower -> true ∈ left ∧ true ∈ right :=
          fun member => lower_subset member
        simp only [Set.mem_union]
        by_cases left_member : true ∈ left <;>
          by_cases right_member : true ∈ right <;>
            by_cases lower_member : true ∈ lower <;> simp_all }

/-- The nontrivial point-weight constructor explicitly inhabits the interface. -/
theorem nontrivial_point_capture_weight_nonempty :
    Nonempty (CaptureWeight Bool) :=
  ⟨nontrivialPointCaptureWeight⟩

/-- The point-weight branch is machine-checked to be nontrivial. -/
theorem nontrivial_point_capture_weight_mass :
    nontrivialPointCaptureWeight.mass {true} = 2 := by
  simp [nontrivialPointCaptureWeight]

/-- A finite Mathlib measure realizes the CAS measure branch via `ENNReal.toReal`.
Finiteness is exactly what makes real conversion preserve both additions. -/
noncomputable def measureCaptureWeight
    {Omega : Type*} [MeasurableSpace Omega] (nu : Measure Omega)
    [IsFiniteMeasure nu] : CaptureWeight Omega where
  mass := fun set => (nu set).toReal
  empty_mass := by simp
  mass_nonnegative := by intro set; positivity
  mass_union_add_lower_le := by
    intro left right lower lower_subset
    have measure_inequality :
        nu (left ∪ right) + nu lower ≤ nu left + nu right :=
      (add_le_add_right (measure_mono lower_subset) _).trans
        (measure_union_add_inter_le_arbitrary nu left right)
    rw [← ENNReal.toReal_add (measure_ne_top nu (left ∪ right))
        (measure_ne_top nu lower),
      ← ENNReal.toReal_add (measure_ne_top nu left) (measure_ne_top nu right)]
    exact ENNReal.toReal_mono (by finiteness) measure_inequality

/-- Real-valued finite counting explicitly inhabits the capture interface. -/
theorem counting_capture_weight_nonempty (Omega : Type*) [Finite Omega] :
    Nonempty (CaptureWeight Omega) :=
  ⟨countingCaptureWeight Omega⟩

/-- Every finite measure gives an explicit inhabitant through `ENNReal.toReal`. -/
theorem measure_capture_weight_nonempty
    {Omega : Type*} [MeasurableSpace Omega] (nu : Measure Omega)
    [IsFiniteMeasure nu] : Nonempty (CaptureWeight Omega) :=
  ⟨measureCaptureWeight nu⟩

/-- Mass of the residual edges captured by a definition set is submodular for
every capture weight, uniformly covering weight, count, and measure. -/
theorem capture_weight_submodular
    {Edge Definition : Type*} (nu : CaptureWeight Edge)
    (residual : Set Edge) (cut : Definition → Set Edge)
    (A B : Set Definition) :
    let captured := fun S : Set Definition =>
      residual ∩ ⋃ definition ∈ S, cut definition
    nu.mass (captured (A ∪ B)) + nu.mass (captured (A ∩ B)) ≤
      nu.mass (captured A) + nu.mass (captured B) := by
  classical
  dsimp only
  let captured := fun S : Set Definition =>
    residual ∩ ⋃ definition ∈ S, cut definition
  change nu.mass (captured (A ∪ B)) + nu.mass (captured (A ∩ B)) ≤
    nu.mass (captured A) + nu.mass (captured B)
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
  exact nu.mass_union_add_lower_le
    (captured A) (captured B) (captured (A ∩ B))
    captured_intersection_subset

#print axioms capture_weight_submodular
end D5.S3.ConceptDynamics.DefinitionCapture.MeasureCapture
