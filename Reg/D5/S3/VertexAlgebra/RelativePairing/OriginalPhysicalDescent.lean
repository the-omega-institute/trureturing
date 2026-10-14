import D5.S3.VertexAlgebra.RelativePairing.OriginalPhysicalDescent
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace Reg.D5.S3.VertexAlgebra.RelativePairing.OriginalPhysicalDescent

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
  _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostNeutralCohomology
  _root_.D5.S3.VertexAlgebra.OriginalBrstReassembly
  _root_.D5.S3.VertexAlgebra.OriginalQQuartetSource
  _root_.D5.S3.VertexAlgebra.OriginalQPhysicalPairing
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

abbrev Sector (parameter : Parameters) :=
  originalEnergySector parameter.lattice parameter.matrix parameter.charge parameter.level

structure FourStates (parameter : Parameters) where
  first : Sector parameter
  second : Sector parameter
  third : Sector parameter
  fourth : Sector parameter

structure Physical (parameter : Parameters) (state : FourStates parameter) : Prop where
  firstCycle : Q parameter.lattice parameter.matrix state.first.val = 0
  secondCycle : Q parameter.lattice parameter.matrix state.second.val = 0
  thirdCycle : Q parameter.lattice parameter.matrix state.third.val = 0
  fourthCycle : Q parameter.lattice parameter.matrix state.fourth.val = 0
  firstRelative : B parameter.lattice 0 state.first.val = 0
  secondRelative : B parameter.lattice 0 state.second.val = 0
  thirdRelative : B parameter.lattice 0 state.third.val = 0
  fourthRelative : B parameter.lattice 0 state.fourth.val = 0
  firstDegree : state.first.val ∈ ghostPart parameter.lattice 1
  secondDegree : state.second.val ∈ ghostPart parameter.lattice 1
  thirdDegree : state.third.val ∈ ghostPart parameter.lattice 1
  fourthDegree : state.fourth.val ∈ ghostPart parameter.lattice 1
  leftEquality : (OriginalBoundaries parameter.lattice parameter.matrix).mkQ
      (⟨state.first.val, firstCycle⟩ : OriginalCycles parameter.lattice parameter.matrix) =
    (OriginalBoundaries parameter.lattice parameter.matrix).mkQ
      (⟨state.second.val, secondCycle⟩ : OriginalCycles parameter.lattice parameter.matrix)
  rightEquality : (OriginalBoundaries parameter.lattice parameter.matrix).mkQ
      (⟨state.third.val, thirdCycle⟩ : OriginalCycles parameter.lattice parameter.matrix) =
    (OriginalBoundaries parameter.lattice parameter.matrix).mkQ
      (⟨state.fourth.val, fourthCycle⟩ : OriginalCycles parameter.lattice parameter.matrix)

def signature : Signature where
  Params := Parameters
  State := FourStates
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ parameter state => F parameter.lattice state.first.val
    (C parameter.lattice 0 state.third.val)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law realization := ∀ parameter state, Physical parameter state →
    realization.readout () parameter state = F parameter.lattice state.second.val
      (C parameter.lattice 0 state.fourth.val)

theorem sourceBridge : (type_of% (@representative_independent)) ↔ arena.Law actual := by
  constructor
  · intro source parameter state physical
    exact source parameter.lattice parameter.matrix parameter.charge parameter.level
      parameter.frame parameter.inverse parameter.leftGram parameter.rightGram
      parameter.leftFrame parameter.rightFrame parameter.direction parameter.xAxis parameter.yAxis
      parameter.critical parameter.null parameter.nonzero parameter.distinct parameter.xRow
      parameter.yRow parameter.xDual parameter.yDual parameter.shell
      state.first state.second state.third state.fourth physical.firstCycle physical.secondCycle
      physical.thirdCycle physical.fourthCycle physical.firstRelative physical.secondRelative
      physical.thirdRelative physical.fourthRelative physical.firstDegree physical.secondDegree
      physical.thirdDegree physical.fourthDegree physical.leftEquality physical.rightEquality
  · intro law lattice matrix charge level frame inverse leftGram rightGram leftFrame rightFrame
      direction xAxis yAxis critical null nonzero distinct xRow yRow xDual yDual shell
      first second third fourth firstCycle secondCycle thirdCycle fourthCycle
      firstRelative secondRelative thirdRelative fourthRelative firstDegree secondDegree
      thirdDegree fourthDegree leftEquality rightEquality
    exact law ⟨lattice, matrix, frame, inverse, leftGram, rightGram, leftFrame, rightFrame,
      charge, direction, xAxis, yAxis, level, critical, null, nonzero, distinct, xRow, yRow,
      xDual, yDual, shell⟩ ⟨first, second, third, fourth⟩
      ⟨firstCycle, secondCycle, thirdCycle, fourthCycle, firstRelative, secondRelative,
        thirdRelative, fourthRelative, firstDegree, secondDegree, thirdDegree, fourthDegree,
        leftEquality, rightEquality⟩

abbrev BoundaryTarget := type_of% (@physical_boundary_vanishing)
abbrev InclusionTarget := type_of% (@inclusion_injective)
abbrev OriginalClassTarget := type_of% (@inclusion_mk)
abbrev ImageTarget := type_of% (@physicalImage_eq)
abbrev QuotientRecoveryTarget := type_of% (@quotientForm_mk)
abbrev ImageRecoveryTarget := type_of% (@imageForm_recovery)
abbrev QuotientHermitianTarget := type_of% (@quotientForm_hermitian)
abbrev ImageHermitianTarget := type_of% (@imageForm_hermitian)

end

end Reg.D5.S3.VertexAlgebra.RelativePairing.OriginalPhysicalDescent
