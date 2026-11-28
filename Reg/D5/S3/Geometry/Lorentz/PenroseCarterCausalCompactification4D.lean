import Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.MinkowskiCoordinates
import Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.MinkowskiGeometry
import Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.MinkowskiBoundary
import Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DeSitterCoordinates
import Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DeSitterGeometry
import Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.CausalGeometry
import Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.SchwarzschildCoordinates
import Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.SchwarzschildGeometry
import Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.ConformalCharts
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
open LeanInformationAudit

namespace Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MinkowskiFactor

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ T R => conformalFactor T R) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {t r : ℝ}, diamond t r → 0 < R.readout () t r

private theorem rejected : ¬ arena.Law erased := by
  intro h
  have h0 : diamond 0 0 := by
    simp [diamond, Real.pi_pos]
  exact (lt_irrefl (0 : ℝ)) (h h0)

def family : Registration arena (type_of% (@conformalFactor_pos)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@conformalFactor_pos, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨0, 0, Real.pi / 2, ?_⟩
    change conformalFactor 0 0 ≠ conformalFactor 0 (Real.pi / 2)
    norm_num [conformalFactor]

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@conformalFactor_pos) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.conformalFactor_pos.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.MinkowskiFactor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ T R => conformalFactor T R)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MinkowskiFactor
end
end Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
