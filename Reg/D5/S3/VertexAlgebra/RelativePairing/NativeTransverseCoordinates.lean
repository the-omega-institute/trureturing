import D5.S3.VertexAlgebra.RelativePairing.NativeTransverseCoordinates
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Reg.D5.S3.VertexAlgebra.RelativePairing.NativeTransverseCoordinates

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
  _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
  _root_.D5.S3.VertexAlgebra.OriginalQQuartetSource
  _root_.D5.S3.VertexAlgebra.OriginalQEnergyInclusionPairing
  _root_.D5.S3.VertexAlgebra.RelativePairing.NativeTransverseCoordinates
  _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

structure Parameters where
  lattice : LatticeData
  frame : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  inverse : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  leftFrame : inverse * frame = 1
  rightFrame : frame * inverse = 1
  charge : Charge lattice
  xAxis : Fin lattice.rank
  yAxis : Fin lattice.rank
  level : ℤ

abbrev signature : Signature where
  Params := Parameters
  State parameter := TransverseDownIndex parameter.lattice parameter.xAxis parameter.yAxis
    parameter.level →₀ ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := TransverseDownIndex parameter.lattice parameter.xAxis parameter.yAxis
    parameter.level →₀ ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ parameter coefficients =>
    coordinates parameter.lattice parameter.frame parameter.inverse
      parameter.leftFrame parameter.rightFrame parameter.charge
      parameter.xAxis parameter.yAxis parameter.level
      (downState parameter.lattice parameter.frame parameter.charge
        parameter.xAxis parameter.yAxis parameter.level coefficients))
  (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law realization := ∀ parameter coefficients, realization.readout () parameter coefficients = coefficients

theorem sourceBridge : (type_of% (@coordinates_downState)) ↔ arena.Law actual := by
  constructor
  · intro source parameter coefficients
    exact source parameter.lattice parameter.frame parameter.inverse
      parameter.leftFrame parameter.rightFrame parameter.charge
      parameter.xAxis parameter.yAxis parameter.level coefficients
  · intro law lattice frame inverse leftFrame rightFrame charge xAxis yAxis level coefficients
    exact law ⟨lattice, frame, inverse, leftFrame, rightFrame, charge, xAxis, yAxis, level⟩ coefficients

abbrev ProjectorTarget := type_of% (@projector_coordinates)
abbrev ReconstructionTarget := type_of% (@downState_coordinates)
abbrev ExistingInputTarget := type_of% (@energyInput_state)
abbrev TensorTarget := type_of% (@downState_tensor)

private def witnessLattice : LatticeData where
  rank := 1
  G := 0
  symmetric := by intros; rfl
  even_diagonal := by intro axis; exact ⟨0, rfl⟩

private def witnessParameter : Parameters :=
  ⟨witnessLattice, 1, 1, by simp, by simp, 0, ⟨0, by decide⟩, ⟨0, by decide⟩, 0⟩

private def witnessIndex : TransverseDownIndex witnessLattice witnessParameter.xAxis
    witnessParameter.yAxis witnessParameter.level :=
  ⟨0, by intro frequency; rfl, by intro frequency; rfl,
    native_down_level_zero witnessLattice⟩

private def witnessCoefficient : signature.State witnessParameter := Finsupp.single witnessIndex 1

private theorem witnessCoefficient_nonzero : witnessCoefficient ≠ 0 := by
  change Finsupp.single witnessIndex (1 : ℂ) ≠ 0
  exact Finsupp.single_ne_zero.mpr one_ne_zero

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun empty => nomatch empty)

private theorem rejectedFails : ¬ arena.Law rejected := by
  intro law
  apply witnessCoefficient_nonzero
  have equality := law witnessParameter witnessCoefficient
  exact equality.symm

def sourceWitness : Registration arena (type_of% (@coordinates_downState)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp coordinates_downState, rejected, rejectedFails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejectedFails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    refine ⟨witnessParameter, witnessCoefficient, 0, ?_⟩
    change coordinates _ _ _ _ _ _ _ _ _ (downState _ _ _ _ _ _ witnessCoefficient) ≠
      coordinates _ _ _ _ _ _ _ _ _ (downState _ _ _ _ _ _ 0)
    rw [coordinates_downState, coordinates_downState]
    exact witnessCoefficient_nonzero

def coordinates_downState_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@coordinates_downState) (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.RelativePairing.NativeTransverseCoordinates.coordinates_downState.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.RelativePairing.NativeTransverseCoordinates.sourceWitness
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceWitness⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ parameter coefficients =>
      coordinates parameter.lattice parameter.frame parameter.inverse
        parameter.leftFrame parameter.rightFrame parameter.charge
        parameter.xAxis parameter.yAxis parameter.level
        (downState parameter.lattice parameter.frame parameter.charge
          parameter.xAxis parameter.yAxis parameter.level coefficients))
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.RelativePairing.NativeTransverseCoordinates
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms sourceWitness
#print axioms coordinates_downState_registration

end
end Reg.D5.S3.VertexAlgebra.RelativePairing.NativeTransverseCoordinates
