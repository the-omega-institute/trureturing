import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.LatticeHalfFockChargedLZero
set_option autoImplicit false
set_option maxRecDepth 4096
namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedLZero
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFock
open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedLZero
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators TensorProduct
noncomputable section
private def hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro first second; fin_cases first <;> fin_cases second <;> rfl
  even_diagonal := by intro axis; fin_cases axis <;> exact ⟨0, rfl⟩

private theorem hyperbolic_unit : IsUnit hyperbolic.G.det := by
  have determinant : hyperbolic.G.det = -1 := by
    change (Matrix.det (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ)) = -1
    norm_num [Matrix.det_fin_two]
  rw [determinant]
  exact isUnit_neg_one

private def probeVector : ActualGround hyperbolic hyperbolic_unit := fun _ => 1

private theorem probe_vector_nonzero : probeVector ≠ 0 := by
  intro equality
  have coordinate := congrFun equality (0 : Half (groundRank hyperbolic hyperbolic_unit))
  exact one_ne_zero (show (1 : ℂ) = 0 from coordinate)

private theorem probe_leading :
    chargedCoefficient hyperbolic hyperbolic_unit 0 0
      ((1 : Oscillator hyperbolic) ⊗ₜ[ℂ] probeVector) ≠ 0 := by
  simpa [chargeNorm, bilinear] using
    charged_ground_leading hyperbolic hyperbolic_unit 0 probeVector probe_vector_nonzero


abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ lattice : LatticeData, Charge lattice) (fun _ => ℤ) (fun _ => ℂ)
def actual : Realization signature := realize signature
  (fun _ p e => (((e + bilinear p.1 p.2 p.2 : ℤ) : ℂ) / 2))
  (fun empty => nomatch empty)
def rejected : Realization signature := realize signature
  (fun _ p e => (((e + bilinear p.1 p.2 p.2 : ℤ) : ℂ) / 2) + 1)
  (fun empty => nomatch empty)
abbrev arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) (e : ℤ),
    tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 0 *
        chargedCoefficient D hu a e - chargedCoefficient D hu a e *
        tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 0 =
      readout.readout () ⟨D,a⟩ e • chargedCoefficient D hu a e

theorem source_bridge : (type_of% (@charged_tensor_L_zero_commutator)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law hyperbolic hyperbolic_unit 0 0
  have good := charged_tensor_L_zero_commutator hyperbolic hyperbolic_unit 0 0
  have zero :
      tensorL hyperbolic (ActualGround hyperbolic hyperbolic_unit)
          (HalfFockSpectralFiberSource.actualInverse hyperbolic) 0 *
          chargedCoefficient hyperbolic hyperbolic_unit 0 0 -
        chargedCoefficient hyperbolic hyperbolic_unit 0 0 *
          tensorL hyperbolic (ActualGround hyperbolic hyperbolic_unit)
            (HalfFockSpectralFiberSource.actualInverse hyperbolic) 0 = 0 := by
    simpa [bilinear] using good
  rw [zero] at bad
  have coefficient_zero : chargedCoefficient hyperbolic hyperbolic_unit 0 0 = 0 := by
    simpa [rejected, realize, bilinear] using bad.symm
  have value := congrArg (fun operator : Module.End ℂ (ActualTensor hyperbolic hyperbolic_unit) =>
    operator ((1 : Oscillator hyperbolic) ⊗ₜ[ℂ] probeVector)) coefficient_zero
  exact probe_leading (by simpa using value)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨hyperbolic,0⟩, 0, 2, ?_⟩
  norm_num [actual, realize, bilinear]

def familyRegistration : Registration arena (type_of% (@charged_tensor_L_zero_commutator)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp charged_tensor_L_zero_commutator, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@charged_tensor_L_zero_commutator)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeHalfFockChargedLZero.charged_tensor_L_zero_commutator.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedLZero.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockChargedLZero
    definition := none
    coordinates := #[0,2]
    readouts := #[{
      path := #["body","body","body","body","arg","fn","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]
end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedLZero
