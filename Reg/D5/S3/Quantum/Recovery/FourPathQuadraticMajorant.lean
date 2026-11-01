import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.FourPathQuadraticMajorant
import Reg.Support.SingleDependentReadout

/-! The complete squared four-path response as a source-bound complex observation. -/

open _root_.D5.S3.Quantum.Recovery.FourPathQuadraticMajorant
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.FourPathQuadraticMajorant

abbrev signature : Signature where
  Params := ℂ
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ xi eta =>
    ((‖xi+eta‖+‖xi-eta‖)/Real.sqrt 2 +
      ‖(Real.cos (Real.pi/8):ℂ)*xi+Complex.I*(Real.sin (Real.pi/8):ℂ)*eta‖+
      ‖(Real.cos (Real.pi/8):ℂ)*xi-Complex.I*(Real.sin (Real.pi/8):ℂ)*eta‖)^2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ xi eta =>
    (Real.sqrt 2+2*Real.cos (Real.pi/8))^2*‖xi‖^2+
      (Real.sqrt 2+2*Real.sin (Real.pi/8))^2*‖eta‖^2+1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ xi eta : ℂ, R.readout () xi eta ≤
    (Real.sqrt 2+2*Real.cos (Real.pi/8))^2*‖xi‖^2+
      (Real.sqrt 2+2*Real.sin (Real.pi/8))^2*‖eta‖^2

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hz := h 0 0
  norm_num [rejected,realize] at hz

def registration : Registration arena (type_of% four_path_quadratic_majorant) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨four_path_quadratic_majorant,rejected,rejected_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_fails
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(0:ℂ),(0:ℂ),(1:ℂ),?_⟩
    have hz : actual.readout () (0:ℂ) (0:ℂ)=0 := by simp [actual,realize]
    have ho : 0 < actual.readout () (0:ℂ) (1:ℂ) := by
      change 0 < ((‖(0:ℂ)+1‖+‖(0:ℂ)-1‖)/Real.sqrt 2 +
        ‖(Real.cos (Real.pi/8):ℂ)*0+Complex.I*(Real.sin (Real.pi/8):ℂ)*1‖+
        ‖(Real.cos (Real.pi/8):ℂ)*0-Complex.I*(Real.sin (Real.pi/8):ℂ)*1‖)^2
      apply sq_pos_of_pos
      have first : 0 < (‖(0:ℂ)+1‖+‖(0:ℂ)-1‖)/Real.sqrt 2 := by norm_num
      linarith [norm_nonneg ((Real.cos (Real.pi/8):ℂ)*0+Complex.I*(Real.sin (Real.pi/8):ℂ)*1),
        norm_nonneg ((Real.cos (Real.pi/8):ℂ)*0-Complex.I*(Real.sin (Real.pi/8):ℂ)*1)]
    change actual.readout () (0:ℂ) (0:ℂ) ≠ actual.readout () (0:ℂ) (1:ℂ)
    rw [hz]
    exact ne_of_lt ho

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    four_path_quadratic_majorant
    (type_of% (realize signature (fun _ xi eta =>
      ((‖xi+eta‖+‖xi-eta‖)/Real.sqrt 2 +
        ‖(Real.cos (Real.pi/8):ℂ)*xi+Complex.I*(Real.sin (Real.pi/8):ℂ)*eta‖+
        ‖(Real.cos (Real.pi/8):ℂ)*xi-Complex.I*(Real.sin (Real.pi/8):ℂ)*eta‖)^2)
      (fun e => nomatch e))) (Type) Unit where
  unitName := `D5.S3.Quantum.Recovery.FourPathQuadraticMajorant.four_path_quadratic_majorant.audit
  realizationName := `Reg.D5.S3.Quantum.Recovery.FourPathQuadraticMajorant.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ xi eta =>
      ((‖xi+eta‖+‖xi-eta‖)/Real.sqrt 2 +
        ‖(Real.cos (Real.pi/8):ℂ)*xi+Complex.I*(Real.sin (Real.pi/8):ℂ)*eta‖+
        ‖(Real.cos (Real.pi/8):ℂ)*xi-Complex.I*(Real.sin (Real.pi/8):ℂ)*eta‖)^2)
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.FourPathQuadraticMajorant
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.FourPathQuadraticMajorant
