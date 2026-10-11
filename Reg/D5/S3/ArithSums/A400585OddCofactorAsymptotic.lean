import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ArithSums.A400585OddCofactorAsymptotic
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ArithSums.A400585OddCofactorAsymptotic
open LeanInformationAudit Filter Topology

noncomputable section
namespace Reg.D5.S3.ArithSums.A400585OddCofactorAsymptotic

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ N => (N : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := Tendsto (fun N : ℕ => S N / ((7 * Z3 / 48) * (R.readout () () N)^3))
    atTop (𝓝 1)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨result, rejected, ?_⟩
    intro h
    have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
    have hone : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 1) := by
      simpa [arena, rejected, realize] using h
    have hbad : (0 : ℝ) = 1 := tendsto_nhds_unique hzero hone
    norm_num at hbad
  sensitivity := by
    apply _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    intro h
    have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
    have hone : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 1) := by
      simpa [arena, rejected, realize] using h
    have hbad : (0 : ℝ) = 1 := tendsto_nhds_unique hzero hone
    norm_num at hbad
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ArithSums.A400585OddCofactorAsymptotic.result)
    (type_of% (realize signature (fun _ _ N => (N : ℝ)) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ArithSums.A400585OddCofactorAsymptotic.natural_cast_information_unit
  realizationName := `Reg.D5.S3.ArithSums.A400585OddCofactorAsymptotic.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => (N : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithSums.A400585OddCofactorAsymptotic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.ArithSums.A400585OddCofactorAsymptotic
