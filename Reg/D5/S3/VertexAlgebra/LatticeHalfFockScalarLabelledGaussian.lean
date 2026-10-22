import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence
import D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian

noncomputable section

local macro "probe_lattice" : term => pure (Lean.mkIdent (Lean.mkPrivateNameCore
  `Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence
  `Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence.probeLattice))

local macro "probe_native" : term => pure (Lean.mkIdent (Lean.mkPrivateNameCore
  `Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence
  `Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence.probeNative))

local macro "probe_state" : term => pure (Lean.mkIdent (Lean.mkPrivateNameCore
  `Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence
  `Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence.probeState))

local macro "probe_nonzero" : term => pure (Lean.mkIdent (Lean.mkPrivateNameCore
  `Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence
  `Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence.probe_nonzero))

abbrev Parameters := Σ object : NativeLattice,
  Σ _charge : Charge object.lattice, Index object.lattice →₀ ℂ

abbrev Parameters.object (parameter : Parameters) : NativeLattice := parameter.1
abbrev Parameters.charge (parameter : Parameters) : Charge parameter.object.lattice := parameter.2.1
abbrev Parameters.weights (parameter : Parameters) : Index parameter.object.lattice →₀ ℂ :=
  parameter.2.2

abbrev signature : Signature where
  Params := Parameters
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := NativeField parameter.object.lattice parameter.object.native
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ parameter degree => Ytw parameter.object.lattice
    parameter.object.native (Finsupp.single parameter.charge
      (sourceDirection parameter.object.lattice parameter.weights ^ degree)))
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law observation := ∀ (object : NativeLattice) (charge : Charge object.lattice)
    (weights : Index object.lattice →₀ ℂ) (degree : ℕ),
    observation.readout () ⟨object, charge, weights⟩ degree =
      degree.factorial • nativeCorrectionEvaluation object.lattice object.native charge
        (PowerSeries.coeff degree (retainedGaussian object.lattice charge weights))

private theorem actual_law : arena.Law actual := by
  intro object charge weights degree
  exact actual_source_field_gaussian_closed object charge weights degree

private theorem probe_field_nonzero :
    Ytw probe_lattice probe_native (Finsupp.single 0 1) ≠ 0 := by
  intro zero
  have coefficient := congrArg (fun field : NativeField probe_lattice probe_native =>
    field.coeff 0 probe_state) zero
  rw [Ytw_vacuum] at coefficient
  change ((HahnModule.of ℂ).symm
    ((_root_.D5.S3.VertexAlgebra.FieldNormalProduct.identityField
      (V := ActualTensor probe_lattice probe_native)) probe_state)).coeff 0 = 0 at coefficient
  rw [_root_.D5.S3.VertexAlgebra.FieldNormalProduct.identityField,
    VertexOperator.of_coeff_apply_coeff] at coefficient
  exact probe_nonzero (by simpa using coefficient)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have failed := law ⟨probe_lattice, probe_native⟩ 0 0 0
  have correct := actual_law ⟨probe_lattice, probe_native⟩ 0 0 0
  have zero := correct.trans failed.symm
  exact probe_field_nonzero (by simpa [actual, rejected, realize] using zero)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨⟨probe_lattice, probe_native⟩, 0, 0⟩, 0, 1, ?_⟩
  intro equality
  change Ytw probe_lattice probe_native (Finsupp.single 0
      (sourceDirection probe_lattice 0 ^ 0)) =
    Ytw probe_lattice probe_native (Finsupp.single 0
      (sourceDirection probe_lattice 0 ^ 1)) at equality
  exact probe_field_nonzero (by
    simpa [sourceDirection, Finsupp.sum] using equality)

def registration : Registration arena (type_of% (@actual_source_field_gaussian_closed)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other distinct
      exact (distinct (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_source_field_gaussian_closed) (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian.actual_source_field_gaussian_closed.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := ⟨.evidence, .evidence⟩
  bundleNonempty := .absent
  readout := some (realize signature (fun _ parameter degree => Ytw parameter.object.lattice
    parameter.object.native (Finsupp.single parameter.charge
      (sourceDirection parameter.object.lattice parameter.weights ^ degree)))
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

#print axioms registration

end

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian
