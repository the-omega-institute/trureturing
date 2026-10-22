import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeHalfFockProductKernel
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality hiding commonKernel
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel

noncomputable section

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro first second; rfl
  even_diagonal := by intro colour; simp

private theorem creation_zero (data : LatticeData) (charge : Charge data) :
    halfCreationCoeff data charge 0 = 1 := by
  simp [halfCreationCoeff, exponential_constant]

abbrev signature : Signature where
  Params := Σ data : LatticeData, Charge data × Charge data × ℤ × ℤ
  State parameter := Oscillator parameter.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Oscillator parameter.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ parameter polynomial => commonKernel parameter.1 parameter.2.1
    parameter.2.2.1 parameter.2.2.2.1 parameter.2.2.2.2 polynomial)
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ parameter _ =>
    halfCreationCoeff parameter.1 parameter.2.1 parameter.2.2.2.1)
    (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law observation := ∀ (data : LatticeData) (left right : Charge data)
      (first second : ℤ) (polynomial : Oscillator data),
    observation.readout () ⟨data, left, right, first, second⟩ polynomial =
      observation.readout () ⟨data, right, left, second, first⟩ polynomial

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have impossible := law emptyLattice 0 0 0 (-1) 1
  change halfCreationCoeff emptyLattice 0 0 = halfCreationCoeff emptyLattice 0 (-1) at impossible
  rw [creation_zero] at impossible
  norm_num [halfCreationCoeff] at impossible

private theorem actual_law : arena.Law actual := by
  intro data left right first second polynomial
  exact common_kernel_branch_exchange data left right first second polynomial

private theorem actual_sensitivity : Sensitivity arena actual := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other distinct
      exact (distinct (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty

private theorem kernel_one_empty :
    commonKernel emptyLattice 0 0 0 0 (1 : Oscillator emptyLattice) = 1 := by
  have value := kernel_constant emptyLattice (0 : Charge emptyLattice)
    (0 : Charge emptyLattice) (0 : ℤ) (0 : ℤ) (1 : ℂ)
  simpa only [MvPolynomial.C_1, creation_zero, mul_one] using value

private theorem actual_dependence : ObservationalDependence signature actual := by
    intro role
    refine ⟨⟨emptyLattice, (0 : Charge emptyLattice), (0 : Charge emptyLattice),
      (0 : ℤ), (0 : ℤ)⟩, (1 : Oscillator emptyLattice),
      (0 : Oscillator emptyLattice), ?_⟩
    intro equality
    apply (one_ne_zero : (1 : Oscillator emptyLattice) ≠ 0)
    calc
      (1 : Oscillator emptyLattice) = commonKernel emptyLattice 0 0 0 0 1 :=
        kernel_one_empty.symm
      _ = commonKernel emptyLattice 0 0 0 0 0 := equality
      _ = 0 := map_zero (commonKernel emptyLattice 0 0 0 0)

def registration :
    _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration
      arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := actual_sensitivity
  dependence := actual_dependence

noncomputable def source_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.common_kernel_branch_exchange)
      (type_of% (realize signature (fun _ parameter polynomial =>
        commonKernel parameter.1 parameter.2.1 parameter.2.2.1
          parameter.2.2.2.1 parameter.2.2.2.2 polynomial)
        (fun empty => nomatch empty))) Unit Unit := {
  unitName := `D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.common_kernel_branch_exchange.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ parameter polynomial =>
    commonKernel parameter.1 parameter.2.1 parameter.2.2.1
      parameter.2.2.2.1 parameter.2.2.2.2 polynomial)
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockProductKernel
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel
