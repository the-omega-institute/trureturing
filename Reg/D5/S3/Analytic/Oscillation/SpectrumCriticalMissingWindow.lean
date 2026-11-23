import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindowModel
import Reg.Support.DependentFamily

/-! The weighted sine score depends on time and can lie below the critical mass fraction. -/

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindow

open _root_.D5.S3.Analytic.Oscillation.OrdinateCounting (Spectrum)
open _root_.D5.S3.Analytic.Oscillation.SpectrumPhaseCutoff (mass sine)
open _root_.D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindow
open _root_.D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindowModel
  (exists_infinite_critical_model)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter Set
open scoped Topology

private abbrev unitSpectrum : Spectrum where
  index := Unit
  gamma := fun _ => 1
  mult := fun _ => 1
  gamma_pos _ := zero_lt_one
  gamma_injective := fun _ _ _ => Subsingleton.elim _ _
  mult_pos _ := Nat.one_pos
  finite_le _ := Set.toFinite _

abbrev scoreSignature : Signature where
  Params := Σ S : Spectrum, Σ _ : S.index → ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def scoreActual : Realization scoreSignature :=
  realize scoreSignature (fun _ p v => sine p.1 p.2.1 p.2.2 v) (fun e => nomatch e)

private def scoreRejected : Realization scoreSignature :=
  realize scoreSignature (fun _ p _ => mass p.1 p.2.1 p.2.2) (fun e => nomatch e)

abbrev scoreArena : Arena where
  signature := scoreSignature
  Law V := ∀ (S : Spectrum) (w : S.index → ℝ)
    (_ : ∀ j, 0 ≤ w j) (_ : LinearIndependent ℚ S.gamma)
    (_ : HasLogSquaredMass S w) (_ : HasSmallSquareTail S w)
    {r β : ℝ}, 0 < r → 0 < β → β < 1 →
    ∀ᶠ T : ℝ in atTop, 0 < mass S w T ∧
      ∀ A : ℝ, ∃ a > A, ∀ u ∈ Icc a (a + Real.exp (T ^ β)),
        V.readout () ⟨S, w, T⟩ (u / r) < β ^ 2 * mass S w T - Real.log T

private theorem score_rejected : ¬ scoreArena.Law scoreRejected := by
  intro h
  obtain ⟨S, w, _, hw, hli, hmass, htail⟩ := exists_infinite_critical_model
  have hevent := (h S w (fun j => (hw j).le) hli hmass htail
    (r := 1) (β := 1 / 2) (by norm_num) (by norm_num) (by norm_num)).and
    (eventually_ge_atTop (1 : ℝ))
  obtain ⟨T, ⟨hW, hwindow⟩, hT⟩ := hevent.exists
  obtain ⟨a, _, ha⟩ := hwindow 0
  have hlt := ha a ⟨le_rfl, le_add_of_nonneg_right (Real.exp_pos _).le⟩
  change mass S w T < (1 / 2 : ℝ) ^ 2 * mass S w T - Real.log T at hlt
  linarith only [hlt, hW, Real.log_nonneg hT]

private theorem score_dependence : ObservationalDependence scoreSignature scoreActual := by
  rintro ⟨⟩
  refine ⟨⟨unitSpectrum, fun _ => 1, 1⟩, 0, Real.pi / 2, ?_⟩
  have hcut : unitSpectrum.cut 1 = {()} := by
    ext j
    cases j
    have hmem : () ∈ {j | unitSpectrum.gamma j ≤ (1 : ℝ)} := by
      change (1 : ℝ) ≤ 1
      exact le_rfl
    exact iff_of_true ((unitSpectrum.finite_le 1).mem_toFinset.mpr hmem)
      (Finset.mem_singleton_self _)
  change sine unitSpectrum (fun _ => 1) 1 0 ≠
    sine unitSpectrum (fun _ => 1) 1 (Real.pi / 2)
  simp [sine, hcut, Real.sin_pi_div_two]

def scoreEvidence : Registration scoreArena (type_of% @eventual_critical_missing_window) where
  actual := scoreActual
  bridge := Iff.rfl
  variation := ⟨@eventual_critical_missing_window, scoreRejected, score_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨scoreRejected, ?_, ?_, score_rejected⟩
      · intro j hj
        exact (hj (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := score_dependence

def scoreAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@eventual_critical_missing_window) (Realization scoreSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindow.scoreUnit
  realizationName := `Reg.D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindow.scoreEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨scoreArena⟩
  objectArena := .source ⟨scoreArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source scoreArena ⟨scoreEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scoreSignature
    (fun _ p v => sine p.1 p.2.1 p.2.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindow
    definition := none
    coordinates := #[0, 1, 11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "body", "arg", "body", "arg", "body", "arg",
        "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms scoreAudit

end Reg.D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindow
