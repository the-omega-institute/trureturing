import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.Apollonian.SecondEigenvalueLimit

namespace Reg.D5.S3.Combinatorics.Apollonian.SecondEigenvalueLimit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages
open LeanInformationAudit Filter
open scoped Topology
noncomputable section
abbrev scaleSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)
def scaling : ∀ (_ : Unit) (_ : Unit), ℕ → ℝ :=
  fun _ _ n => ((2:ℝ)^((n:ℝ)/2))⁻¹
abbrev actual : Realization scaleSignature := realize scaleSignature scaling (fun e => nomatch e)
abbrev limitArena : Arena where
  signature := scaleSignature
  Law R := Tendsto (fun n => secondEigenvalue n * R.readout () () n)
    atTop (nhds (Real.sqrt 2))
private def bad : Realization scaleSignature :=
  realize scaleSignature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem bad_reject : ¬ limitArena.Law bad := by
  intro h
  have hh : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (Real.sqrt 2)) := by
    simpa [bad, realize] using h
  have he := tendsto_nhds_unique tendsto_const_nhds hh
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  linarith
private theorem bridge : limitArena.Law actual ↔
    (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.SecondEigenvalueLimit.result)) := by
  simp only [limitArena, actual, scaling, realize, limitClaim, div_eq_mul_inv]

def result_family : Registration limitArena
    (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.SecondEigenvalueLimit.result)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mpr _root_.D5.S3.Combinatorics.Apollonian.SecondEigenvalueLimit.result,
    bad, bad_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad_reject
  dependence := by
    intro i; cases i
    refine ⟨(), 0, 2, ?_⟩
    norm_num [actual, scaling, realize]
def registration_result : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.SecondEigenvalueLimit.result)
    (Realization scaleSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.SecondEigenvalueLimit.result_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.SecondEigenvalueLimit.result_family
  realizationSource := none
  generated := false
  arena := .source ⟨limitArena⟩
  objectArena := .source ⟨limitArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source limitArena ⟨result_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scaleSignature scaling (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Combinatorics.Apollonian.SecondEigenvalueLimit
