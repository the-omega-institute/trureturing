import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity
open _root_.D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the limiting rate at its denominator coordinate. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 1 / x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Preserve strict decrease from five and observe the limit value. -/
abbrev arena : Arena where
  signature := signature
  Law R := (∀ n : ℕ, 5 ≤ n → p (n + 1) < p n) ∧
    Filter.Tendsto p Filter.atTop (𝓝 (R.readout () () 4))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero : Filter.Tendsto p Filter.atTop (𝓝 (0 : ℝ)) := h.2
  have bad : (1 / 4 : ℝ) = 0 := tendsto_nhds_unique result.2 hzero
  norm_num at bad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 4, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity.unit
  realizationName := `Reg.D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 1 / x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity
    definition := some {
      owner := `D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity
      name := `D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms signature
#print axioms actual
#print axioms rejected
#print axioms arena
#print axioms rejected_law
#print axioms dependence
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.FockSpace.IdealHeraldingRateMonotonicity
