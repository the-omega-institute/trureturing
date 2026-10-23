import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean
import Mathlib.Analysis.Real.Pi.Bounds
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean
open _root_.D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the asserted mean at its subtracted real coordinate. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 10 / 3 - x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain integrability and observe only the value in the first-moment equation. -/
abbrev arena : Arena where
  signature := signature
  Law R := Integrable (fun y : ℝ => y * nnDensity y) ∧
    ∫ y : ℝ, y * nnDensity y = R.readout () () Real.pi

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : (10 / 3 - Real.pi : ℝ) = 0 := result.2.symm.trans h.2
  linarith [Real.pi_lt_d2]

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
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
      (@_root_.D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean.unit
  realizationName := `Reg.D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 10 / 3 - x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean
    definition := some {
      owner := `D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean
      name := `D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg"]
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
end Reg.D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean
