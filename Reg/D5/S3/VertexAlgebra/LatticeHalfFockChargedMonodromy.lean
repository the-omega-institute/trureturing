import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy
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

abbrev Parameters := Σ D : LatticeData, Charge D

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameters (fun _ => ℤ) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ _ exponent => (-1 : ℂ) ^ exponent)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0)
  (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (exponent : ℤ),
    chargedCoefficient D hu (-charge) exponent =
      readout.readout () ⟨D, charge⟩ exponent •
        chargedCoefficient D hu charge exponent

theorem source_bridge :
    (type_of% (@charged_coefficient_coordinate_monodromy)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law hyperbolic hyperbolic_unit 0 0
  have coefficient_zero :
      chargedCoefficient hyperbolic hyperbolic_unit 0 0 = 0 := by
    simpa [rejected, realize] using bad
  have value := congrArg
    (fun operator : Module.End ℂ (ActualTensor hyperbolic hyperbolic_unit) =>
      operator ((1 : Oscillator hyperbolic) ⊗ₜ[ℂ] probeVector)) coefficient_zero
  exact probe_leading (by simpa using value)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨hyperbolic, 0⟩, 0, 1, ?_⟩
  norm_num [actual, realize]

def familyRegistration : Registration arena
    (type_of% (@charged_coefficient_coordinate_monodromy)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp charged_coefficient_coordinate_monodromy,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

/-- The scalar is an actual RHS occurrence of the unchanged full operator law.
The proof binder `hu` remains universally quantified in that law; source data
coordinates contain only the lattice and charge, as required by the contract. -/
def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@charged_coefficient_coordinate_monodromy)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy.charged_coefficient_coordinate_monodromy
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy
