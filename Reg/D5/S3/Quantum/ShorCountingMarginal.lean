import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.ShorCountingMarginal
import Reg.Support.SingleDependentReadout

/-! Source-bound normalization audit on the full target-vector readout. -/

namespace Reg.D5.S3.Quantum.ShorCountingMarginal
open QuantumShorOrderFindingCore QuantumPhaseEstimationGeneral
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Parameters × ℕ)
    (fun p => Fin p.1.dimension → ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ v => normSquared v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (c : Parameters) (n : ℕ),
    (∑ y : Fin (2 ^ n), R.readout () (c, n) (runQPE c.modularOperator n c.input y)) = 1

private def sample : Parameters := ⟨2, by norm_num, 1, by norm_num, 1, by norm_num⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h sample 0
  norm_num [rejected, realize] at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(sample, 0), (fun _ => (0 : ℂ)), fun _ => 1, ?_⟩
  norm_num [actual, realize, normSquared, sample, Parameters.dimension]

def source_registration : Registration arena (type_of% @Parameters.shor_distribution_normalized) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Parameters.shor_distribution_normalized, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@Parameters.shor_distribution_normalized) (Realization signature) Unit Unit := {
  unitName := `QuantumShorOrderFindingCore.Parameters.shor_distribution_normalized.__information_unit
  realizationName := `Reg.D5.S3.Quantum.ShorCountingMarginal.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => normSquared v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.ShorCountingMarginal
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.ShorCountingMarginal

namespace Reg.D5.S3.Quantum.ShorCountingMarginal.TargetNormSmul
open QuantumPhaseEstimationGeneral
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ TargetState (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ v => normSquared v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (z : ℂ) (ψ : TargetState d),
    R.readout () d (z • ψ) = Complex.normSq z * normSquared ψ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h (d := 1) 0 (fun _ => 0)
  norm_num [rejected, realize] at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => (0 : ℂ)), fun _ => 1, ?_⟩
  norm_num [actual, realize, normSquared]

def source_registration : Registration arena (type_of% @target_norm_smul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@target_norm_smul, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@target_norm_smul) (Realization signature) Unit Unit := {
  unitName := `QuantumPhaseEstimationGeneral.target_norm_smul.__information_unit
  realizationName := `Reg.D5.S3.Quantum.ShorCountingMarginal.TargetNormSmul.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => normSquared v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.ShorCountingMarginal
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.ShorCountingMarginal.TargetNormSmul

namespace Reg.D5.S3.Quantum.ShorCountingMarginal.ActualCountingReadout
open QuantumShorOrderFindingCore QuantumPhaseEstimationGeneral
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters
    (fun c => TargetState c.dimension) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ v => normSquared v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private def sample : Parameters := ⟨2, by norm_num, 1, by norm_num, 1, by norm_num⟩

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨sample, (fun _ => (0 : ℂ)), fun _ => 1, ?_⟩
  norm_num [actual, realize, normSquared, sample, Parameters.dimension]

def mixtureArena : Arena where
  signature := signature
  Law R := ∀ (c : Parameters) (n : ℕ) (y : Fin (2 ^ n)),
    R.readout () c (runQPE c.modularOperator n c.input y) =
      (c.period : ℝ)⁻¹ * ∑ s : Fin c.period, probability (2 ^ n) (s.val / c.period) y

private theorem rejected_mixture : ¬ mixtureArena.Law rejected := by
  intro h
  have h0 := h sample 0 0
  have hn := sample.shor_distribution_normalized 0
  change (∑ y : Fin 1, normSquared (runQPE sample.modularOperator 0 sample.input y)) = 1 at hn
  rw [Fin.sum_univ_one] at hn
  rw [sample.shor_qpe_probability_mixture] at hn
  have hz : (0 : ℝ) = (sample.period : ℝ)⁻¹ *
      ∑ s : Fin sample.period, probability (2 ^ 0) (s.val / sample.period) 0 := by
    simpa [rejected, realize] using h0
  exact zero_ne_one (hz.trans hn)

def mixtureSource : Registration mixtureArena (type_of% @Parameters.shor_qpe_probability_mixture) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Parameters.shor_qpe_probability_mixture, rejected, rejected_mixture⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity mixtureArena.Law actual rejected rejected_mixture
  dependence := dependence

def mixtureRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@Parameters.shor_qpe_probability_mixture) (Realization signature) Unit Unit := {
  unitName := `QuantumShorOrderFindingCore.Parameters.shor_qpe_probability_mixture.__information_unit
  realizationName := `Reg.D5.S3.Quantum.ShorCountingMarginal.ActualCountingReadout.mixtureSource
  realizationSource := none
  generated := false
  arena := .source ⟨mixtureArena⟩
  objectArena := .source ⟨mixtureArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source mixtureArena ⟨mixtureSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => normSquared v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.ShorCountingMarginal
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def peakArena : Arena where
  signature := signature
  Law R := ∀ (c : Parameters) (n : ℕ) (s : Fin c.period) (b : Fin (2 ^ n)),
    Nearest (2 ^ n) (s.val / c.period) b →
      (c.period : ℝ)⁻¹ * (4 / Real.pi ^ 2) ≤
        R.readout () c (runQPE c.modularOperator n c.input b)

private theorem rejected_peak : ¬ peakArena.Law rejected := by
  intro h
  have hnear : Nearest (2 ^ 0) ((0 : Fin sample.period).val / sample.period) 0 := by
    refine ⟨0, ?_⟩
    norm_num
  have h0 := h sample 0 0 0 hnear
  have hp : 0 < (sample.period : ℝ)⁻¹ * (4 / Real.pi ^ 2) :=
    mul_pos (inv_pos.mpr (Nat.cast_pos.mpr sample.period_pos))
      (div_pos (by norm_num) (pow_pos Real.pi_pos _))
  change (sample.period : ℝ)⁻¹ * (4 / Real.pi ^ 2) ≤ 0 at h0
  exact (not_le_of_gt hp) h0

def peakSource : Registration peakArena (type_of% @Parameters.shor_mixture_peak_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Parameters.shor_mixture_peak_lower_bound, rejected, rejected_peak⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity peakArena.Law actual rejected rejected_peak
  dependence := dependence

def peakRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@Parameters.shor_mixture_peak_lower_bound) (Realization signature) Unit Unit := {
  unitName := `QuantumShorOrderFindingCore.Parameters.shor_mixture_peak_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Quantum.ShorCountingMarginal.ActualCountingReadout.peakSource
  realizationSource := none
  generated := false
  arena := .source ⟨peakArena⟩
  objectArena := .source ⟨peakArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source peakArena ⟨peakSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => normSquared v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.ShorCountingMarginal
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.ShorCountingMarginal.ActualCountingReadout
