import Reg.D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindowModel
import D5.S3.Analytic.Oscillation.SpectrumCommensurateAlignment

/-! The positive weight readout in the commensurate spectrum law. -/

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.Analytic.Oscillation.SpectrumCommensurateAlignment

open _root_.D5.S3.Analytic.Oscillation.OrdinateCounting (Spectrum)
open _root_.D5.S3.Analytic.Oscillation.SpectrumPhaseCutoff (mass sine)
open _root_.D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindow (HasLogSquaredMass)
open _root_.D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindow (HasLogarithmicSquareTail)
open _root_.D5.S3.Analytic.Oscillation.SpectrumCommensurateAlignment (exists_logarithmic_full_alignment)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open SpectrumCriticalMissingWindowModel (weightSignature weightActual weightRejected weight_dependence)
open LeanInformationAudit

abbrev alignmentWeightArena : Arena where
  signature := weightSignature
  Law V := ∃ (S : Spectrum) (w : S.index → ℝ), Infinite S.index ∧
    (∀ j, 0 < V.readout () ⟨S, w⟩ j) ∧ HasLogSquaredMass S w ∧ HasLogarithmicSquareTail S w ∧
    ∀ T : ℝ, 5 ≤ T → 0 < mass S w T ∧
      ∃ q : ℕ, 0 < q ∧ (q : ℝ) + 1 ≤ Real.log T / Real.log 2 ∧
        (∀ (m : ℤ) (X : ℝ), X ≤ T →
          sine S w X (Real.pi * (q : ℝ) / 2 + (m : ℝ) * (2 * Real.pi * q)) = mass S w X) ∧
        ∀ A : ℝ, ∃ m : ℤ, Real.pi * (q : ℝ) / 2 + (m : ℝ) * (2 * Real.pi * q) ∈
          Set.Ioo A (A + (2 * Real.pi / Real.log 2) * Real.log T)

private theorem alignmentWeightRejected : ¬ alignmentWeightArena.Law weightRejected := by
  rintro ⟨S, _, hInf, hw, _⟩
  obtain ⟨j⟩ : Nonempty S.index := @Infinite.nonempty _ hInf
  exact (lt_irrefl 0) (hw j)

private theorem alignmentWeightSensitivity : Sensitivity alignmentWeightArena weightActual := by
  constructor
  · intro i
    refine ⟨weightRejected, ?_, ?_, alignmentWeightRejected⟩
    · intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def alignmentWeightEvidence :
    Registration alignmentWeightArena (type_of% @exists_logarithmic_full_alignment) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨@exists_logarithmic_full_alignment, weightRejected, alignmentWeightRejected⟩
  sensitivity := alignmentWeightSensitivity
  dependence := weight_dependence

def alignmentWeightAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_logarithmic_full_alignment) (Realization weightSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Oscillation.SpectrumCommensurateAlignment.alignmentWeightUnit
  realizationName := `Reg.D5.S3.Analytic.Oscillation.SpectrumCommensurateAlignment.alignmentWeightEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨alignmentWeightArena⟩
  objectArena := .source ⟨alignmentWeightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source alignmentWeightArena ⟨alignmentWeightEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature (fun _ p j => p.2 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Oscillation.SpectrumCommensurateAlignment
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "fn", "arg", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms alignmentWeightAudit

end Reg.D5.S3.Analytic.Oscillation.SpectrumCommensurateAlignment
