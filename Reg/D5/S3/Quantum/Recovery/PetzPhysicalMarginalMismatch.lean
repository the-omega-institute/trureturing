import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.PetzPhysicalMarginalMismatch
import Reg.Support.SingleDependentReadout

/-! The source-bound derivative readout of the physical retained mismatch. -/

set_option autoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open _root_.D5.S3.Quantum.Recovery.BKMFlagRefinement (partialTracePetz)
open _root_.D5.S3.Quantum.Recovery.PetzPhysicalFirstVariation
open _root_.D5.S3.Quantum.Recovery.PetzPhysicalMarginalMismatch

namespace Reg.D5.S3.Quantum.Recovery.PetzPhysicalMarginalMismatch

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

private def defect (t ε η c : ℝ) : ℝ :=
  (sourceMarginal t c 0 1 -
    partialTraceRight (partialTracePetz (reference ε η c) (sourceMarginal t c)) 0 1).re

private def actual : Realization signature :=
  realize signature (fun _ p c => defect p.1 p.2.1 p.2.2 c) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨hd, _, _, hpos⟩ := physical_marginal_mismatch
    (t := 1 / 8) (ε := 1 / 16) (η := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  by_contra! he
  have hconst : defect (1 / 8) (1 / 16) 1 = fun _ => defect (1 / 8) (1 / 16) 1 0 := by
    funext c
    exact he ⟨1 / 8, 1 / 16, 1⟩ c 0
  change HasDerivAt (defect (1 / 8) (1 / 16) 1) _ 0 at hd
  rw [hconst] at hd
  exact hpos.ne' (hd.unique (hasDerivAt_const _ _))

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {t ε η : ℝ}, 0 < t → t ≤ 1 / 8 → 0 < ε → ε ≤ 1 / 16 → 0 < η →
    let B := Real.sqrt (1 - ε ^ 2)
    let μ := 1 - t - t - (partialTraceRight (recoveryVariation t ε η) 0 1).re
    HasDerivAt (fun c => R.readout () ⟨t, ε, η⟩ c) μ 0 ∧
      μ = (1 - B) * (1 - t - t) +
        2 * ε ^ 2 * (1 - t - t * η ^ 2) / (B * (η ^ 2 + 1) + 2 * η) ∧
      ε ^ 2 / 10 ≤ μ ∧ 0 < μ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨hd, _, _, hpos⟩ :=
    h (t := 1 / 8) (ε := 1 / 16) (η := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact hpos.ne' (hd.unique (hasDerivAt_const _ _))

def sourceRegistration : Registration arena (type_of% @physical_marginal_mismatch) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@physical_marginal_mismatch, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@physical_marginal_mismatch) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.PetzPhysicalMarginalMismatch.physical_marginal_mismatch.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzPhysicalMarginalMismatch.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p c => defect p.1 p.2.1 p.2.2 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzPhysicalMarginalMismatch
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.PetzPhysicalMarginalMismatch
