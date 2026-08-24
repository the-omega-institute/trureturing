/- GID: D5/S3/ConceptDynamics/DefinitionCapture/MeasureCapture
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionCapture/MeasureCapture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Extended nonnegative masses make residual-intersection capture submodular. -/

import Mathlib.Data.Real.ENatENNReal
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Real

/- Library-search audit trail (2026-08-25):
   * Repository searches found the real-valued `EscapeWeight` interface, but its
     codomain excludes infinite counts and nonfinite measures.  `CaptureWeight`
     therefore uses `ENNReal` and only the law consumed by capture submodularity.
   * Pinned Mathlib supplies `measure_union_add_inter` when one set is measurable,
     plus `measure_union_toMeasurable`, `measure_toMeasurable`, and
     `subset_toMeasurable`. It also supplies `Set.encard_union_add_encard_inter`
     and `Set.encard_le_encard`. These prove the law below for arbitrary counting
     and arbitrary Mathlib measures; a nonadditive coverage weight supplies a
     genuinely non-measure instance. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionCapture.MeasureCapture

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

/-- An extended-nonnegative set weight with exactly the law used by capture.
The codomain admits infinite counts and measure values. -/
structure CaptureWeight (Omega : Type*) where
  mass : Set Omega -> ENNReal
  mass_union_add_lower_le : forall (left right lower : Set Omega),
    lower ⊆ left ∩ right ->
      mass (left ∪ right) + mass lower ≤ mass left + mass right

/-- Extended cardinality realizes counting without a finiteness assumption. -/
noncomputable def countingCaptureWeight (Omega : Type*) :
    CaptureWeight Omega where
  mass := fun set => set.encard
  mass_union_add_lower_le := by
    intro left right lower lower_subset
    exact_mod_cast
      (calc
        (left ∪ right).encard + lower.encard ≤
            (left ∪ right).encard + (left ∩ right).encard :=
          add_le_add le_rfl (Set.encard_le_encard lower_subset)
        _ = left.encard + right.encard :=
          Set.encard_union_add_encard_inter left right)

/-- A non-count, non-measure coverage weight: every nonempty set has mass one. -/
noncomputable def nonadditiveCoverageCaptureWeight : CaptureWeight Bool := by
  classical
  exact
    { mass := fun set => if set.Nonempty then 1 else 0
      mass_union_add_lower_le := by
        intro left right lower lower_subset
        by_cases left_nonempty : left.Nonempty
        · by_cases right_nonempty : right.Nonempty
          · have union_nonempty : (left ∪ right).Nonempty :=
              left_nonempty.mono Set.subset_union_left
            by_cases lower_nonempty : lower.Nonempty <;>
              simp [left_nonempty, right_nonempty, union_nonempty,
                lower_nonempty]
          · rw [Set.not_nonempty_iff_eq_empty.mp right_nonempty] at lower_subset ⊢
            have lower_empty : lower = ∅ := by
              apply Set.eq_empty_of_subset_empty
              intro edge edge_in_lower
              exact (lower_subset edge_in_lower).2
            simp [left_nonempty, lower_empty]
        · rw [Set.not_nonempty_iff_eq_empty.mp left_nonempty] at lower_subset ⊢
          have lower_empty : lower = ∅ := by
            apply Set.eq_empty_of_subset_empty
            intro edge edge_in_lower
            exact (lower_subset edge_in_lower).1
          simp [lower_empty] }

/-- The genuinely non-measure weight explicitly inhabits the interface. -/
theorem nonadditive_coverage_capture_weight_nonempty :
    Nonempty (CaptureWeight Bool) :=
  ⟨nonadditiveCoverageCaptureWeight⟩

/-- The weight is nonadditive, so it is neither counting nor a measure. -/
theorem nonadditive_coverage_capture_weight_not_additive :
    nonadditiveCoverageCaptureWeight.mass ({false} ∪ {true}) ≠
      nonadditiveCoverageCaptureWeight.mass {false} +
        nonadditiveCoverageCaptureWeight.mass {true} := by
  norm_num [nonadditiveCoverageCaptureWeight]

/-- Every Mathlib measure realizes the measure branch with its native values. -/
noncomputable def measureCaptureWeight
    {Omega : Type*} [MeasurableSpace Omega] (nu : Measure Omega) :
    CaptureWeight Omega where
  mass := nu
  mass_union_add_lower_le := by
    intro left right lower lower_subset
    exact (add_le_add_right (measure_mono lower_subset) _).trans
      (measure_union_add_inter_le_arbitrary nu left right)

/-- Counting on every type explicitly inhabits the capture interface. -/
theorem counting_capture_weight_nonempty (Omega : Type*) :
    Nonempty (CaptureWeight Omega) :=
  ⟨countingCaptureWeight Omega⟩

/-- Counting retains an infinite value on an infinite carrier. -/
theorem infinite_counting_capture_weight_mass :
    (countingCaptureWeight Nat).mass Set.univ = ⊤ := by
  simp [countingCaptureWeight]

/-- Every measure gives an explicit inhabitant without a finiteness premise. -/
theorem measure_capture_weight_nonempty
    {Omega : Type*} [MeasurableSpace Omega] (nu : Measure Omega) :
    Nonempty (CaptureWeight Omega) :=
  ⟨measureCaptureWeight nu⟩

/-- An infinite measure distinct from counting is retained without conversion:
adding a Dirac mass makes the singleton at zero have mass two. -/
theorem nonfinite_noncounting_measure_capture_weight_mass :
    letI : MeasurableSpace Nat := ⊤
    let weight := measureCaptureWeight (Measure.count + Measure.dirac 0)
    weight.mass {0} = 2 ∧ weight.mass Set.univ = ⊤ := by
  norm_num [measureCaptureWeight, Measure.count_apply]

/-- Mass of the residual edges captured by a definition set is submodular for
every extended-nonnegative weight satisfying the single capture law. -/
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

/-- Capture is submodular for every Mathlib measure, including measures taking
the value infinity. No measurability premise is imposed on residual or cuts. -/
theorem measure_capture_submodular
    {Edge Definition : Type*} [MeasurableSpace Edge] (nu : Measure Edge)
    (residual : Set Edge) (cut : Definition → Set Edge)
    (A B : Set Definition) :
    let captured := fun S : Set Definition =>
      residual ∩ ⋃ definition ∈ S, cut definition
    nu (captured (A ∪ B)) + nu (captured (A ∩ B)) ≤
      nu (captured A) + nu (captured B) := by
  exact capture_weight_submodular (measureCaptureWeight nu) residual cut A B

#print axioms capture_weight_submodular
#print axioms measure_capture_submodular
end D5.S3.ConceptDynamics.DefinitionCapture.MeasureCapture
