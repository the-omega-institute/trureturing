import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Boundary.WeightedLogDerivativeResidue
import Reg.Support.SingleDependentReadout

/-! The meromorphic order of the sum observes the presence of its simple pole. -/

open _root_.D5.S3.Analytic.Boundary.WeightedLogDerivativeResidue
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter LeanInformationAudit
open scoped Topology BigOperators

namespace Reg.D5.S3.Analytic.Boundary.WeightedLogDerivativeResidue

noncomputable section
universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℂ (fun _ => ℂ → ℂ) (fun _ => WithTop ℤ)

def actual : Realization signature :=
  realize signature (fun _ r f => meromorphicOrderAt f r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} (s : Finset ι) (f : ι → ℂ → ℂ) (a : ι → ℂ)
    (n : ι → ℤ) (r : ℂ), (∀ i ∈ s, MeromorphicAt (f i) r) →
    (∀ i ∈ s, meromorphicOrderAt (f i) r = n i) →
    let F := fun z => ∑ i ∈ s, a i * logDeriv (f i) z
    let residue := ∑ i ∈ s, a i * (n i : ℂ)
    (∃ h : ℂ → ℂ, AnalyticAt ℂ h r ∧
      F =ᶠ[𝓝[≠] r] fun z => residue / (z - r) + h z) ∧
    (R.readout () r F = -1 ↔ residue ≠ 0) ∧
    ((∃ h : ℂ → ℂ, AnalyticAt ℂ h r ∧ F =ᶠ[𝓝[≠] r] h) ↔ residue = 0)

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  let s : Finset (ULift.{u} Unit) := {⟨()⟩}
  have hzero : (∑ i ∈ s, (1 : ℂ) * ((1 : ℤ) : ℂ)) ≠ 0 := by simp [s]
  have bad := (h s (fun _ => id) (fun _ => 1) (fun _ => 1) 0
    (fun _ _ => analyticAt_id.meromorphicAt) (fun _ _ => meromorphicOrderAt_id)).2.1.mpr hzero
  change (0 : WithTop ℤ) = -1 at bad
  exact (by decide : (0 : WithTop ℤ) ≠ -1) bad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, id, fun _ => 1, ?_⟩
  change meromorphicOrderAt id (0 : ℂ) ≠ meromorphicOrderAt (fun _ : ℂ => (1 : ℂ)) 0
  rw [meromorphicOrderAt_id, meromorphicOrderAt_const]
  simp

def registration : Registration arena.{u} (type_of% @weighted_log_deriv_residue.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_log_deriv_residue.{u}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_log_deriv_residue.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Boundary.WeightedLogDerivativeResidue.audit
  realizationName := `Reg.D5.S3.Analytic.Boundary.WeightedLogDerivativeResidue.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r f => meromorphicOrderAt f r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Boundary.WeightedLogDerivativeResidue
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.Boundary.WeightedLogDerivativeResidue
