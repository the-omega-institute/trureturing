import D5.S3.VertexAlgebra.OriginalQRelativeAmbientPreimage
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace Reg.D5.S3.VertexAlgebra.OriginalQRelativeAmbientPreimage

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
  _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
  _root_.D5.S3.VertexAlgebra.OriginalQQuartetSource
  _root_.D5.S3.VertexAlgebra.OriginalBrstReassembly
  _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

structure Parameters where
  lattice : LatticeData
  matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  frame : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  inverse : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  leftGram : matrix * gramComplex lattice = 1
  rightGram : gramComplex lattice * matrix = 1
  leftFrame : inverse * frame = 1
  rightFrame : frame * inverse = 1
  charge : Charge lattice
  direction : Fin lattice.rank → ℂ
  xAxis : Fin lattice.rank
  yAxis : Fin lattice.rank
  level : ℤ
  critical : lattice.rank = 26
  null : gramPair lattice direction direction = 0
  nonzero : chosenP lattice charge direction ≠ 0
  distinct : xAxis ≠ yAxis
  xRow : frame xAxis = direction
  yRow : frame yAxis = adaptedPartner lattice charge direction
  xDual : ∀ row, gramPair lattice (frame yAxis) (frame row) = if row = xAxis then 1 else 0
  yDual : ∀ row, gramPair lattice (frame xAxis) (frame row) = if row = yAxis then 1 else 0
  shell : chosenH lattice charge + (level : ℂ) - 1 = 0
  degree : ℤ

abbrev Sector (parameter : Parameters) :=
  originalEnergySector parameter.lattice parameter.matrix parameter.charge parameter.level

def signature : Signature where
  Params := Parameters
  State parameter := ↥(Sector parameter)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ↥(Sector parameter)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ parameter state => energyTransferHomotopy parameter.lattice parameter.matrix
      parameter.frame parameter.inverse parameter.leftGram parameter.rightGram
      parameter.leftFrame parameter.rightFrame parameter.charge parameter.direction
      parameter.xAxis parameter.yAxis parameter.level state)
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law realization := ∀ (parameter : Parameters) (state : ↥(Sector parameter)),
    B parameter.lattice 0 state.val = 0 →
    Q parameter.lattice parameter.matrix state.val = 0 →
    state.val ∈ ghostPart parameter.lattice parameter.degree →
    (∃ preimage : State parameter.lattice,
      Q parameter.lattice parameter.matrix preimage = state.val) →
    B parameter.lattice 0 (realization.readout () parameter state).val = 0 ∧
      (realization.readout () parameter state).val ∈
        ghostPart parameter.lattice (parameter.degree - 1) ∧
      Q parameter.lattice parameter.matrix (realization.readout () parameter state).val = state.val

theorem sourceBridge :
    (type_of% (@relative_ambient_boundary_homotopy_preimage)) ↔ arena.Law actual := by
  constructor
  · intro source parameter state relative cycle homogeneous boundary
    exact source parameter.lattice parameter.matrix parameter.frame parameter.inverse
      parameter.leftGram parameter.rightGram parameter.leftFrame parameter.rightFrame
      parameter.charge parameter.direction parameter.xAxis parameter.yAxis parameter.level
      parameter.critical parameter.null parameter.nonzero parameter.distinct parameter.xRow
      parameter.yRow parameter.xDual parameter.yDual parameter.shell parameter.degree state
      relative cycle homogeneous boundary
  · intro law lattice matrix frame inverse leftGram rightGram leftFrame rightFrame
      charge direction xAxis yAxis level critical null nonzero distinct xRow yRow xDual yDual
      shell degree state relative cycle homogeneous boundary
    exact law ⟨lattice, matrix, frame, inverse, leftGram, rightGram, leftFrame, rightFrame,
      charge, direction, xAxis, yAxis, level, critical, null, nonzero, distinct, xRow,
      yRow, xDual, yDual, shell, degree⟩ state relative cycle homogeneous boundary

abbrev LiteralEqualityTarget := type_of% (@literal_physical_equality_iff_relative_preimage)

end

end Reg.D5.S3.VertexAlgebra.OriginalQRelativeAmbientPreimage
