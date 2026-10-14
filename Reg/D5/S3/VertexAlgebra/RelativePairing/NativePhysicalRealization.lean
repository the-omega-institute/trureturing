import D5.S3.VertexAlgebra.RelativePairing.NativePhysicalRealization
import Reg.D5.S3.VertexAlgebra.RelativePairing.OriginalPhysicalDescent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Reg.D5.S3.VertexAlgebra.RelativePairing.NativePhysicalRealization

open _root_.D5.S3.VertexAlgebra.OriginalQPhysicalPairing
  _root_.D5.S3.VertexAlgebra.RelativePairing.NativePhysicalRealization
  _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev Parameters := OriginalPhysicalDescent.Parameters

def signature : Signature where
  Params := Parameters
  State parameter := physicalImage parameter.lattice parameter.matrix parameter.charge parameter.level
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := physicalImage parameter.lattice parameter.matrix parameter.charge parameter.level
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ parameter state =>
    (nativePhysicalEquiv parameter.lattice parameter.matrix parameter.frame parameter.inverse
      parameter.leftGram parameter.rightGram parameter.leftFrame parameter.rightFrame
      parameter.charge parameter.direction parameter.xAxis parameter.yAxis parameter.level
      parameter.critical parameter.null parameter.nonzero parameter.distinct
      parameter.xRow parameter.yRow parameter.xDual parameter.yDual parameter.shell)
      (imageProjection parameter.lattice parameter.matrix parameter.frame parameter.inverse
        parameter.leftGram parameter.rightGram parameter.leftFrame parameter.rightFrame
        parameter.charge parameter.direction parameter.xAxis parameter.yAxis parameter.level
        parameter.critical parameter.null parameter.nonzero parameter.distinct
        parameter.xRow parameter.yRow parameter.xDual parameter.yDual parameter.shell state))
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law realization := ∀ parameter state, realization.readout () parameter state = state

theorem sourceBridge : (type_of% (@nativeImage_imageProjection)) ↔ arena.Law actual := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.matrix parameter.frame parameter.inverse
      parameter.leftGram parameter.rightGram parameter.leftFrame parameter.rightFrame
      parameter.charge parameter.direction parameter.xAxis parameter.yAxis parameter.level
      parameter.critical parameter.null parameter.nonzero parameter.distinct
      parameter.xRow parameter.yRow parameter.xDual parameter.yDual parameter.shell state
  · intro law lattice matrix frame inverse leftGram rightGram leftFrame rightFrame
      charge direction xAxis yAxis level critical null nonzero distinct
      xRow yRow xDual yDual shell state
    exact law ⟨lattice, matrix, frame, inverse, leftGram, rightGram, leftFrame, rightFrame,
      charge, direction, xAxis, yAxis, level, critical, null, nonzero, distinct,
      xRow, yRow, xDual, yDual, shell⟩ state

abbrev InclusionTarget := type_of% (@inclusion_physical)
abbrev OriginalClassTarget := type_of% (@nativeImage_originalClass)
abbrev RelativeProjectionTarget := type_of% (@projection_relative)
abbrev CoefficientProjectionTarget := type_of% (@projection_coordinate_recovery)
abbrev GhostProjectionTarget := type_of% (@projection_ghost_one)
abbrev NativeLeftInverseTarget := type_of% (@physicalProjection_lift)
abbrev BoundaryTarget := type_of% (@physicalProjection_boundary)
abbrev RepresentativeRecoveryTarget := type_of% (@imageProjection_representative)
abbrev LeftInverseTarget := type_of% (@imageProjection_nativeImage)
abbrev PhysicalRepresentativeTarget := type_of% (@nativeImage_representative)
abbrev FormTarget := type_of% (@nativeImage_form)

end
end Reg.D5.S3.VertexAlgebra.RelativePairing.NativePhysicalRealization
