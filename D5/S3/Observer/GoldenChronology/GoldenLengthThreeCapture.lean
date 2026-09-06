/- GID: D5/S3/Observer/GoldenChronology/GoldenLengthThreeCapture
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact shared-arena capture detects redundancy among golden count and Magnus views. -/

import D5.S3.Observer.GoldenChronology.GoldenMagnusParityRecovery
import D5.S3.ConceptDynamics.InformationEscape.StructuralNovelty

/-!
# Intrinsic capture on the complete length-three golden object

This is the entire language of length-three golden factors, not a sample of
occurrence indices. A proved equivalence transports the finite presentation
to the canonical factor subtype, preserving the actual matrix/count readouts.
Each theorem unit is native: its law constrains a typed CUT realization.
There is no `Statement := True`, external score, historical baseline, or
user-chosen weight. Counts use the existing Catalog/ExactRate engine.

The two explicit catalogs below are analysis views. They do not claim to be
the registry's maximal catalog under a designated system sealing root. The
positive two-view result cannot certify admission when a full-matrix peer is
also present. The three-view result explicitly proves zero unique capture
for all three peers. No registration is split into artificial singleton roots.

The normative v4.3 StructuralArena and disposition registry are not present
as executable owners on the pinned base; this file does not fabricate them.
One ordinary Lean build checks the finite count equations and their proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Observer.GoldenChronology.GoldenLengthThreeCapture

open D5.S1.Words
open D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge
open D5.S3.Observer.GoldenChronology.GoldenMagnusParityRecovery
open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape

/-- All four length-three factors, ordered SLS, SLL, LSL, LLS. -/
def factorWord : Fin 4 → List Bool :=
  ![[false, true, false], [false, true, true],
    [true, false, true], [true, true, false]]

private def occurrenceStart : Fin 4 → ℕ := ![4, 1, 0, 2]

/-- Every represented state is an actual consecutive golden factor. -/
theorem factor_word_occurs (i : Fin 4) :
    factorWord i = goldenFactor 3 (occurrenceStart i) := by
  fin_cases i <;> decide

/-- The four represented word contents are distinct. -/
theorem factor_word_injective : Function.Injective factorWord := by decide

/-- Exact enumeration of the whole object, using the frozen complexity theorem. -/
theorem factor_word_image_complete :
    Finset.univ.image factorWord = goldenFactorSet 3 := by
  classical
  have hsub : Finset.univ.image factorWord ⊆ goldenFactorSet 3 := by
    intro word hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact mem_goldenFactorSet.mpr ⟨occurrenceStart i, factor_word_occurs i⟩
  have hcard : (Finset.univ.image factorWord).card = 4 := by
    rw [Finset.card_image_of_injective _ factor_word_injective]
    decide
  apply Finset.eq_of_subset_of_card_le hsub
  simpa only [hcard, golden_factor_complexity] using (show 3 + 1 ≤ 4 from by decide)

/-- Word-preserving equivalence to the full canonical factor subtype. -/
noncomputable def factorWordEquiv : Fin 4 ≃ ↥(goldenFactorSet 3) :=
  Equiv.ofBijective
    (fun i => ⟨factorWord i,
      mem_goldenFactorSet.mpr ⟨occurrenceStart i, factor_word_occurs i⟩⟩)
    (by
      constructor
      · intro i j h
        exact factor_word_injective (congrArg Subtype.val h)
      · intro word
        have hmem : word.val ∈ Finset.univ.image factorWord := by
          rw [factor_word_image_complete]
          exact word.property
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
        exact ⟨i, Subtype.ext hi⟩)

/-- A shared finite arena for the complete length-three golden object. -/
def goldenLengthThreeArena : Arena := Arena.ofFintype (Fin 4)

/-- Count CUT, computed from word contents. -/
def countReadout (i : Fin 4) : ℕ × ℕ :=
  ((factorWord i).count true, (factorWord i).count false)

/-- Oriented central Magnus CUT, computed by the existing Chen observer. -/
def centerReadout (i : Fin 4) : ℤ := magnusCenter (factorWord i)

/-- Full ordered Parikh matrix CUT. -/
def matrixReadout (i : Fin 4) : IntegerMatrix3 := binaryParikhMatrix (factorWord i)

/-- The semantic equivalence preserves all three actual readouts, not just cardinality. -/
theorem factor_equiv_readout_transport (i : Fin 4) :
    countReadout i = ((factorWordEquiv i).val.count true,
      (factorWordEquiv i).val.count false) ∧
    centerReadout i = magnusCenter (factorWordEquiv i).val ∧
    matrixReadout i = binaryParikhMatrix (factorWordEquiv i).val := by
  exact ⟨rfl, rfl, rfl⟩

private def oneCut (Output : Type) [DecidableEq Output] :
    PrimitiveSignature (Fin 4) where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Output
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by intro i; decide
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

/-- Native count law on the same canonical arena. -/
def countLawArena : PrimitiveLawArena where
  toArena := goldenLengthThreeArena
  signature := oneCut (ℕ × ℕ)
  Law := fun r => ∀ x y,
    r.readout 0 x = r.readout 0 y ↔ (x = 0 ↔ y = 0)

/-- Native oriented-center law on that same arena. -/
def centerLawArena : PrimitiveLawArena where
  toArena := goldenLengthThreeArena
  signature := oneCut ℤ
  Law := fun r => ∀ x y,
    r.readout 0 x = r.readout 0 y ↔
      x = y ∨ (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0)

/-- Native full-word recovery law on that same arena. -/
def matrixLawArena : PrimitiveLawArena where
  toArena := goldenLengthThreeArena
  signature := oneCut IntegerMatrix3
  Law := fun r => Function.Injective (r.readout 0)

/-- Count realization bound to actual letter counts. -/
def countRealization : PrimitiveRealization countLawArena.signature where
  readout := fun _ => countReadout
  anchor := Fin.elim0

/-- Center realization bound to the existing Magnus coordinate. -/
def centerRealization : PrimitiveRealization centerLawArena.signature where
  readout := fun _ => centerReadout
  anchor := Fin.elim0

/-- Matrix realization bound to the actual ordered product. -/
def matrixRealization : PrimitiveRealization matrixLawArena.signature where
  readout := fun _ => matrixReadout
  anchor := Fin.elim0

/-- The count kernel has one singleton and one three-state class. -/
theorem count_partition_law : countLawArena.Law countRealization := by decide

/-- The center kernel has one two-state class and two singleton classes. -/
theorem center_partition_law : centerLawArena.Law centerRealization := by decide

/-- The full matrix readout recovers every state of the complete arena. -/
theorem matrix_recovery_law : matrixLawArena.Law matrixRealization := by decide

private def countUnit : TheoremUnit goldenLengthThreeArena :=
  NativeTheoremUnit.toTheoremUnit (arena := countLawArena)
    ⟨countRealization, count_partition_law⟩

private def centerUnit : TheoremUnit goldenLengthThreeArena :=
  NativeTheoremUnit.toTheoremUnit (arena := centerLawArena)
    ⟨centerRealization, center_partition_law⟩

private def matrixUnit : TheoremUnit goldenLengthThreeArena :=
  NativeTheoremUnit.toTheoremUnit (arena := matrixLawArena)
    ⟨matrixRealization, matrix_recovery_law⟩

/-- Analysis view containing only the two complementary coordinates. -/
def twoCoordinateAnalysisView : Catalog goldenLengthThreeArena :=
  Catalog.ofVector ![countUnit, centerUnit]

/-- Analysis view retaining the full-matrix peer as well. No peer is hidden. -/
def fullPresentationAnalysisView : Catalog goldenLengthThreeArena :=
  Catalog.ofVector ![countUnit, centerUnit, matrixUnit]

/-- Counts and center have incomparable kernels, with two explicit pair witnesses. -/
theorem count_center_kernel_incomparability :
    countReadout 1 = countReadout 3 ∧ centerReadout 1 ≠ centerReadout 3 ∧
    centerReadout 0 = centerReadout 2 ∧ countReadout 0 ≠ countReadout 2 := by decide

/-- Exact leave-one-out counts on the complete shared arena. -/
theorem exact_two_coordinate_capture :
    escapeDenominator goldenLengthThreeArena = 12 ∧
    twoCoordinateAnalysisView.escapeNumerator ∅ = 12 ∧
    twoCoordinateAnalysisView.escapeNumerator {0} = 6 ∧
    twoCoordinateAnalysisView.escapeNumerator {1} = 2 ∧
    twoCoordinateAnalysisView.escapeNumerator twoCoordinateAnalysisView.fullIndexSet = 0 ∧
    twoCoordinateAnalysisView.uniqueCaptureCount 0 = 2 ∧
    twoCoordinateAnalysisView.uniqueCaptureCount 1 = 6 := by decide

/-- The exact local analysis-view rates, without weights or thresholds. -/
theorem exact_two_coordinate_rates :
    twoCoordinateAnalysisView.theoremGainRate 0 = (1 / 6 : ℚ) ∧
    twoCoordinateAnalysisView.theoremGainRate 1 = (1 / 2 : ℚ) := by decide

/-- Keeping all three peers makes every exclusive capture zero. -/
theorem full_presentation_exclusive_capture_zero :
    ∀ i : Fin 3, fullPresentationAnalysisView.uniqueCaptureCount i = 0 := by decide

/-- A faithful joint readout does not imply intrinsic irredundance. -/
theorem full_presentation_faithful_but_not_irredundant :
    fullPresentationAnalysisView.escapeNumerator fullPresentationAnalysisView.fullIndexSet = 0 ∧
      ¬ (∀ i : Fin 3, fullPresentationAnalysisView.LowersEscape i) := by decide

#print axioms factor_word_image_complete
#print axioms factor_equiv_readout_transport
#print axioms count_partition_law
#print axioms center_partition_law
#print axioms matrix_recovery_law
#print axioms exact_two_coordinate_capture
#print axioms exact_two_coordinate_rates
#print axioms full_presentation_exclusive_capture_zero
#print axioms full_presentation_faithful_but_not_irredundant

end D5.S3.Observer.GoldenChronology.GoldenLengthThreeCapture
