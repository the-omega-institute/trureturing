import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.PetzPhysicalFirstVariation
import Reg.Support.SingleDependentReadout

/-! Source-bound audits for the physical Petz variation and fibre. -/

set_option autoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot
open Filter
open scoped ComplexOrder Topology Matrix.Norms.Elementwise
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open _root_.D5.S3.Quantum.Recovery.BKMFlagRefinement (joint partialTracePetz)
open _root_.D5.S3.Quantum.Recovery.PetzProjectedHessian (Joint)
open _root_.D5.S3.Quantum.Recovery.PetzPhysicalFirstVariation

namespace Reg.D5.S3.Quantum.Recovery.PetzPhysicalFirstVariation

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => Joint)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

namespace RecoveryVariation

private def actual : Realization signature :=
  realize signature
    (fun _ p c => partialTracePetz (reference p.2.1 p.2.2 c) (sourceMarginal p.1 c))
    (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t : ℝ) {ε η : ℝ}, 0 < ε → ε ≤ 1 / 16 → 0 < η →
    HasDerivAt (R.readout () ⟨t, ε, η⟩) (recoveryVariation t ε η) 0 ∧
      HasDerivAt (sourceMarginal t) (qubit 0 (1 - t - t) (1 - t - t) 0) 0

private theorem derivative_ne_zero : recoveryVariation (1 / 8) (1 / 16) 1 ≠ 0 := by
  intro h
  have hentry := congrArg (fun A : Joint => (A (0, 0) (1, 0)).re) h
  have hp : 0 < recoveryEntry (1 / 8) (1 / 16) 1 := by
    unfold recoveryEntry
    positivity
  exact hp.ne' (by
    simpa [recoveryVariation, joint, Matrix.blockDiagonal_apply, flagBias, qubit] using hentry)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hd := (h (1 / 8) (ε := 1 / 16) (η := 1)
    (by norm_num) (by norm_num) (by norm_num)).1
  exact derivative_ne_zero (hd.unique (hasDerivAt_const _ _))

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  by_contra! h
  let K : ℝ → Joint := actual.readout i ⟨1 / 8, 1 / 16, 1⟩
  have hconst : K = fun _ => K 0 := by
    funext c
    exact h ⟨1 / 8, 1 / 16, 1⟩ c 0
  have hd := (physical_firstVariation (1 / 8) (ε := 1 / 16) (η := 1)
    (by norm_num) (by norm_num) (by norm_num)).1
  change HasDerivAt K _ 0 at hd
  rw [hconst] at hd
  exact derivative_ne_zero (hd.unique (hasDerivAt_const _ _))

def sourceRegistration : Registration arena (type_of% @physical_firstVariation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@physical_firstVariation, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@physical_firstVariation) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.PetzPhysicalFirstVariation.physical_firstVariation.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Recovery.PetzPhysicalFirstVariation.RecoveryVariation.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p c => partialTracePetz (reference p.2.1 p.2.2 c) (sourceMarginal p.1 c))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzPhysicalFirstVariation
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RecoveryVariation

namespace SourceFibre

private def actual : Realization signature :=
  realize signature (fun _ p c => duplicatedSource p.1 c) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {t ε η : ℝ}, 0 < t → t ≤ 1 / 8 → 0 < ε → ε ≤ 1 / 16 → 0 < η →
    ∀ᶠ c in 𝓝 (0 : ℝ),
      (R.readout () ⟨t, ε, η⟩ c).PosDef ∧ (R.readout () ⟨t, ε, η⟩ c).trace = 1 ∧
      partialTraceRight (R.readout () ⟨t, ε, η⟩ c) = sourceMarginal t c ∧
      (reference ε η c).PosDef ∧ (reference ε η c).trace = 1 ∧
      partialTraceRight (reference ε η c) = referenceMarginal η ∧
      (c ≠ 0 → ¬ Commute (R.readout () ⟨t, ε, η⟩ c) (reference ε η c))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have htrace := (h (t := 1 / 8) (ε := 1 / 16) (η := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).self_of_nhds.2.1
  norm_num [rejected, realize] at htrace

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1 / 8, 1 / 16, 1⟩, 0, 1 / 2, fun h => ?_⟩
  have hentry := congrArg (fun A : Joint => (A (0, 0) (1, 0)).re) h
  norm_num [actual, realize, duplicatedSource, joint, Matrix.blockDiagonal_apply,
    sourceMarginal, qubit, Complex.real_smul] at hentry

def sourceRegistration : Registration arena (type_of% @physical_source_on_fibre) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@physical_source_on_fibre, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@physical_source_on_fibre) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.PetzPhysicalFirstVariation.physical_source_on_fibre.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Recovery.PetzPhysicalFirstVariation.SourceFibre.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p c => duplicatedSource p.1 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzPhysicalFirstVariation
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SourceFibre

end Reg.D5.S3.Quantum.Recovery.PetzPhysicalFirstVariation
