/- GID: D5/S3/ConceptDynamics/DefinitionCapture/MeasureCapture
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionCapture/MeasureCapture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Capture mass is submodular; the infinite CAS bridge fails in its relation model. -/

import D5.S3.ConceptDynamics.DefinitionEscape.ResidualJoinLaw
import Mathlib.Data.Real.ENatENNReal
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Real

/- Library-search audit trail (2026-08-25):
   * `rg -n 'Set \(X × X\)' D5` found the canonical `defectRelation` in
     `TargetRisk/RefinementRiskCostTradeoff.lean`, plus adjacent kernel and
     residual relations. The theorem below imports and uses that exact relation;
     it introduces no second residual.
   * Shape search `rg -n '⋃|iUnion' D5/S3/ConceptDynamics/DefinitionCapture
     D5/S3/ConceptDynamics/DefinitionEscape` found the existing captured-set
     formula here and the finite-cover family in `FiniteCoverCounting`. Synonym
     searches for residual/escape/defect, cut/separator/kernel/complement, and
     count/measure/weight/capture/coverage (including 残差/逃逸/缺陷, 切开/分离/核,
     and 计数/测度/权重/捕获/覆盖) found `defectRelation`, `Setoid.ker`,
     `EscapeWeight`, and `CaptureWeight`; none is replaced or renamed here.
   * `ls D5/S3/ConceptDynamics/DefinitionCapture` and
     `git grep -n '^def \|^  def \|^structure ' --
     D5/S3/ConceptDynamics/DefinitionCapture | head -60` found only this module
     and its `CaptureWeight` structure. Repository search for the theorem name
     found only its existing consumers in `DirectlyProvableLaws` and Scribe.
   * Pinned Mathlib supplies `measure_union_add_inter`,
     `measure_union_toMeasurable`, `measure_toMeasurable`,
     `subset_toMeasurable`, `Set.encard_union_add_encard_inter`,
     `Set.encard_le_encard`, `Set.infinite_range_of_injective`, and
     `Measure.count_apply_infinite`. The exact joined-residual identity is the
     repository theorem `residual_join_law`, which is imported rather than
     reproved. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionCapture.MeasureCapture

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.DefinitionEscape.ResidualJoinLaw
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

/-- CAS section 4.4's difference bridge fails inside its own relation model.
For `X = Nat × Bool`, the baseline residual, the pairs left after adding
`Prod.snd`, and the pairs captured by that definition are all infinite. Thus
ordinary counting gives `⊤ - ⊤ = 0` for `F({d})`, while captured mass is `⊤`.
The statement also verifies symmetry, absence of diagonal pairs, and the exact
joined-residual identity, so the witness cannot be widened to arbitrary sets.
It refutes only the compatibility of `F(S) = M(∅) - M(S)` with interpreting
`F` as captured mass at infinite values; it does not refute submodularity. -/
theorem infinite_counting_cas_bridge_fails :
    let X := Nat × Bool
    let q : Concept X Unit := fun _ => ()
    let target : Concept X X := id
    let definition : Concept X Bool := Prod.snd
    let residual := defectRelation q target
    let capturedCut := residual ∩
      ({pair : X × X | Setoid.ker definition pair.1 pair.2} : Set (X × X))ᶜ
    let remaining := residual \ capturedCut
    let weight := countingCaptureWeight (X × X)
    let baselineMass := weight.mass residual
    let remainingMass := weight.mass remaining
    let casF := baselineMass - remainingMass
    (∀ x y, (x, y) ∈ residual ↔ (y, x) ∈ residual) ∧
      (∀ x, (x, x) ∉ residual) ∧
      (∀ x y, (x, y) ∈ capturedCut ↔ (y, x) ∈ capturedCut) ∧
      (∀ x, (x, x) ∉ capturedCut) ∧
      remaining = defectRelation (conceptJoin q definition) target ∧
      baselineMass = ⊤ ∧ remainingMass = ⊤ ∧ casF = 0 ∧
      weight.mass capturedCut = ⊤ ∧ casF ≠ weight.mass capturedCut := by
  classical
  dsimp only
  have residualInfinite :
      (defectRelation (fun _ : Nat × Bool => ())
        (id : Concept (Nat × Bool) (Nat × Bool))).Infinite := by
    have rangeInjective : Function.Injective (fun n : Nat =>
        ((n, false), (n, true))) := by
      intro left right samePair
      exact congrArg (fun pair => pair.1.1) samePair
    exact (Set.infinite_range_of_injective rangeInjective).mono (by
      rintro pair ⟨n, rfl⟩
      exact ⟨rfl, by simp⟩)
  have remainingInfinite :
      (defectRelation
        (conceptJoin (fun _ : Nat × Bool => ()) (Prod.snd : Nat × Bool → Bool))
        (id : Concept (Nat × Bool) (Nat × Bool))).Infinite := by
    have rangeInjective : Function.Injective (fun n : Nat =>
        ((n, false), (n + 1, false))) := by
      intro left right samePair
      exact congrArg (fun pair => pair.1.1) samePair
    exact (Set.infinite_range_of_injective rangeInjective).mono (by
      rintro pair ⟨n, rfl⟩
      exact ⟨rfl, by simp⟩)
  have capturedInfinite :
      (defectRelation (fun _ : Nat × Bool => ())
          (id : Concept (Nat × Bool) (Nat × Bool)) ∩
        ({pair : (Nat × Bool) × (Nat × Bool) |
            Setoid.ker (Prod.snd : Nat × Bool → Bool) pair.1 pair.2} :
          Set ((Nat × Bool) × (Nat × Bool)))ᶜ).Infinite := by
    have rangeInjective : Function.Injective (fun n : Nat =>
        ((n, false), (n, true))) := by
      intro left right samePair
      exact congrArg (fun pair => pair.1.1) samePair
    exact (Set.infinite_range_of_injective rangeInjective).mono (by
      rintro pair ⟨n, rfl⟩
      exact ⟨⟨rfl, by simp⟩, by simp [Setoid.ker_def]⟩)
  have remaining_eq_joined :
      defectRelation (fun _ : Nat × Bool => ())
          (id : Concept (Nat × Bool) (Nat × Bool)) \
        (defectRelation (fun _ : Nat × Bool => ())
            (id : Concept (Nat × Bool) (Nat × Bool)) ∩
          ({pair : (Nat × Bool) × (Nat × Bool) |
              Setoid.ker (Prod.snd : Nat × Bool → Bool) pair.1 pair.2} :
            Set ((Nat × Bool) × (Nat × Bool)))ᶜ) =
        defectRelation
          (conceptJoin (fun _ : Nat × Bool => ())
            (Prod.snd : Nat × Bool → Bool))
          (id : Concept (Nat × Bool) (Nat × Bool)) := by
    calc
      _ = defectRelation (fun _ : Nat × Bool => ())
            (id : Concept (Nat × Bool) (Nat × Bool)) ∩
          {pair : (Nat × Bool) × (Nat × Bool) |
            Setoid.ker (Prod.snd : Nat × Bool → Bool) pair.1 pair.2} := by
        ext pair
        simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff,
          Set.mem_setOf_eq]
        tauto
      _ = _ := (residual_join_law (fun _ : Nat × Bool => ())
        (Prod.snd : Nat × Bool → Bool)
        (id : Concept (Nat × Bool) (Nat × Bool))).symm
  have residualMassTop :
      (countingCaptureWeight ((Nat × Bool) × (Nat × Bool))).mass
        (defectRelation (fun _ : Nat × Bool => ())
          (id : Concept (Nat × Bool) (Nat × Bool))) = ⊤ := by
    change ((defectRelation (fun _ : Nat × Bool => ())
      (id : Concept (Nat × Bool) (Nat × Bool))).encard : ENNReal) = ⊤
    rw [residualInfinite.encard_eq]
    rfl
  have remainingMassTop :
      (countingCaptureWeight ((Nat × Bool) × (Nat × Bool))).mass
        (defectRelation (fun _ : Nat × Bool => ())
            (id : Concept (Nat × Bool) (Nat × Bool)) \
          (defectRelation (fun _ : Nat × Bool => ())
              (id : Concept (Nat × Bool) (Nat × Bool)) ∩
            ({pair : (Nat × Bool) × (Nat × Bool) |
                Setoid.ker (Prod.snd : Nat × Bool → Bool) pair.1 pair.2} :
              Set ((Nat × Bool) × (Nat × Bool)))ᶜ)) = ⊤ := by
    rw [remaining_eq_joined]
    change ((defectRelation
      (conceptJoin (fun _ : Nat × Bool => ())
        (Prod.snd : Nat × Bool → Bool))
      (id : Concept (Nat × Bool) (Nat × Bool))).encard : ENNReal) = ⊤
    rw [remainingInfinite.encard_eq]
    rfl
  have capturedMassTop :
      (countingCaptureWeight ((Nat × Bool) × (Nat × Bool))).mass
        (defectRelation (fun _ : Nat × Bool => ())
            (id : Concept (Nat × Bool) (Nat × Bool)) ∩
          ({pair : (Nat × Bool) × (Nat × Bool) |
              Setoid.ker (Prod.snd : Nat × Bool → Bool) pair.1 pair.2} :
            Set ((Nat × Bool) × (Nat × Bool)))ᶜ) = ⊤ := by
    change ((defectRelation (fun _ : Nat × Bool => ())
        (id : Concept (Nat × Bool) (Nat × Bool)) ∩
      ({pair : (Nat × Bool) × (Nat × Bool) |
          Setoid.ker (Prod.snd : Nat × Bool → Bool) pair.1 pair.2} :
        Set ((Nat × Bool) × (Nat × Bool)))ᶜ).encard : ENNReal) = ⊤
    rw [capturedInfinite.encard_eq]
    rfl
  refine ⟨?_, ?_, ?_, ?_, remaining_eq_joined, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp [defectRelation, eq_comm]
  · intro x
    simp [defectRelation]
  · intro x y
    simp [defectRelation, Setoid.ker_def, eq_comm]
  · intro x
    simp [defectRelation]
  · exact residualMassTop
  · exact remainingMassTop
  · rw [residualMassTop, remainingMassTop]
    rfl
  · exact capturedMassTop
  · rw [residualMassTop, remainingMassTop, capturedMassTop]
    exact ENNReal.zero_ne_top

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
#print axioms infinite_counting_cas_bridge_fails
end D5.S3.ConceptDynamics.DefinitionCapture.MeasureCapture
