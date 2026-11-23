import Reg.D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindowModel
import D5.S3.Analytic.Oscillation.SpectrumTwoTermCountAlignment

/-! The harmonic weight readout in the comparison spectrum with bounded count discrepancy. -/

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.Analytic.Oscillation.SpectrumTwoTermCountAlignment

open Filter
open _root_.D5.S3.Analytic.Oscillation.OrdinateCounting (Spectrum)
open _root_.D5.S3.Analytic.Oscillation.SpectrumPhaseCutoff (mass sine)
open _root_.D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindow (HasLogSquaredMass)
open _root_.D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindow (HasLogarithmicSquareTail)
open _root_.D5.S3.Analytic.Oscillation.SpectrumTwoTermCountAlignment
  (exists_two_term_count_alignment)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open SpectrumCriticalMissingWindowModel
  (weightSignature weightActual weightRejected weight_dependence)
open LeanInformationAudit

abbrev harmonicWeightArena : Arena where
  signature := weightSignature
  Law V := ∃ (S : Spectrum) (w : S.index → ℝ), Infinite S.index ∧
    (∀ j, S.mult j = 1 ∧ V.readout () ⟨S, w⟩ j = S.gamma j / (1 / 4 + S.gamma j ^ 2)) ∧
    (∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ T : ℝ in atTop,
      |(S.N T : ℝ) - T / (2 * Real.pi) * (Real.log (T / (2 * Real.pi)) - 1)| ≤ D) ∧
    HasLogSquaredMass S w ∧ HasLogarithmicSquareTail S w ∧
    ∀ᶠ T : ℝ in atTop, 0 < mass S w T ∧
      ∃ q : ℕ, 0 < q ∧ (q : ℝ) + 1 ≤ 21 * (Real.log (21 * T) / Real.log 2) ∧
        (∀ (m : ℤ) (X : ℝ), X ≤ T →
          sine S w X (Real.pi * (q : ℝ) / 2 + (m : ℝ) * (2 * Real.pi * (q : ℝ))) =
            mass S w X) ∧
        ∀ A : ℝ, ∃ m : ℤ, Real.pi * (q : ℝ) / 2 + (m : ℝ) * (2 * Real.pi * (q : ℝ)) ∈
          Set.Ioo A (A + (42 * Real.pi / Real.log 2) * Real.log (21 * T))

private theorem harmonicWeightRejected : ¬ harmonicWeightArena.Law weightRejected := by
  rintro ⟨S, _, hInf, hw, _⟩
  obtain ⟨j⟩ : Nonempty S.index := @Infinite.nonempty _ hInf
  have heq : (0 : ℝ) = S.gamma j / (1 / 4 + S.gamma j ^ 2) := (hw j).2
  have hpos : 0 < S.gamma j / (1 / 4 + S.gamma j ^ 2) :=
    div_pos (S.gamma_pos j) (by positivity)
  exact hpos.ne' heq.symm

private theorem harmonicWeightSensitivity : Sensitivity harmonicWeightArena weightActual := by
  constructor
  · intro i
    refine ⟨weightRejected, ?_, ?_, harmonicWeightRejected⟩
    · intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def harmonicWeightEvidence :
    Registration harmonicWeightArena (type_of% @exists_two_term_count_alignment) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨@exists_two_term_count_alignment, weightRejected, harmonicWeightRejected⟩
  sensitivity := harmonicWeightSensitivity
  dependence := weight_dependence

def harmonicWeightAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_two_term_count_alignment) (Realization weightSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Oscillation.SpectrumTwoTermCountAlignment.harmonicWeightUnit
  realizationName :=
    `Reg.D5.S3.Analytic.Oscillation.SpectrumTwoTermCountAlignment.harmonicWeightEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨harmonicWeightArena⟩
  objectArena := .source ⟨harmonicWeightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source harmonicWeightArena ⟨harmonicWeightEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature (fun _ p j => p.2 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Oscillation.SpectrumTwoTermCountAlignment
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "fn", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms harmonicWeightAudit

end Reg.D5.S3.Analytic.Oscillation.SpectrumTwoTermCountAlignment
