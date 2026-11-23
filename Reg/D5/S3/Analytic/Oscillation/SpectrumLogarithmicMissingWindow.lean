import Reg.D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindow
import D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindowModel

/-! The score readout in the logarithmic missing-window bound. -/

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindow

open _root_.D5.S3.Analytic.Oscillation.OrdinateCounting (Spectrum)
open _root_.D5.S3.Analytic.Oscillation.SpectrumPhaseCutoff (mass sine)
open _root_.D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindow (HasLogSquaredMass)
open _root_.D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindow
open _root_.D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindowModel (exists_infinite_logarithmic_model)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open SpectrumCriticalMissingWindow (scoreSignature scoreActual scoreRejected score_sensitivity score_dependence)
open LeanInformationAudit Filter Set
open scoped Topology

abbrev logarithmicScoreArena : Arena where
  signature := scoreSignature
  Law V := ∀ (S : Spectrum) (w : S.index → ℝ)
    (_ : ∀ j, 0 ≤ w j) (_ : LinearIndependent ℚ S.gamma)
    (_ : HasLogSquaredMass S w) (_ : HasLogarithmicSquareTail S w)
    {r β : ℝ}, 0 < r → 0 < β → β < 1 →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop, 0 < mass S w T ∧
      ∀ A : ℝ, ∃ a > A, ∀ u ∈ Icc a (a + Real.exp (c * T ^ β * Real.log T)),
        V.readout () ⟨S, w, T⟩ (u / r) < β ^ 2 * mass S w T - Real.log T

private theorem logarithmic_score_rejected : ¬ logarithmicScoreArena.Law scoreRejected := by
  intro h
  obtain ⟨S, w, _, hw, hli, hmass, htail⟩ := exists_infinite_logarithmic_model
  obtain ⟨c, _, hwindow⟩ := h S w (fun j => (hw j).le) hli hmass htail
    (r := 1) (β := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨T, ⟨hW, hwindowT⟩, hT⟩ := (hwindow.and (eventually_ge_atTop (1 : ℝ))).exists
  obtain ⟨a, _, ha⟩ := hwindowT 0
  have hlt := ha a ⟨le_rfl, le_add_of_nonneg_right (Real.exp_pos _).le⟩
  change mass S w T < (1 / 2 : ℝ) ^ 2 * mass S w T - Real.log T at hlt
  linarith only [hlt, hW, Real.log_nonneg hT]

def logarithmicScoreEvidence :
    Registration logarithmicScoreArena (type_of% @eventual_logarithmic_missing_window) where
  actual := scoreActual
  bridge := Iff.rfl
  variation := ⟨@eventual_logarithmic_missing_window, scoreRejected, logarithmic_score_rejected⟩
  sensitivity := score_sensitivity logarithmicScoreArena.Law logarithmic_score_rejected
  dependence := score_dependence

def logarithmicScoreAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@eventual_logarithmic_missing_window) (Realization scoreSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindow.logarithmicScoreUnit
  realizationName := `Reg.D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindow.logarithmicScoreEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨logarithmicScoreArena⟩
  objectArena := .source ⟨logarithmicScoreArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source logarithmicScoreArena ⟨logarithmicScoreEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scoreSignature
    (fun _ p v => sine p.1 p.2.1 p.2.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindow
    definition := none
    coordinates := #[0, 1, 12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "arg", "fn", "arg", "body", "arg", "body", "arg",
        "body", "arg", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms logarithmicScoreAudit

end Reg.D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindow
