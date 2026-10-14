import D5.S3.VertexAlgebra.OriginalQTransferredTermComputationTransient
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.OriginalQTransferredTermComputationTransient

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraVirasoro
  LatticeBcGhostBrstCharge BcGhostFockSupport OriginalQQuartetSource

noncomputable section

structure Parameters where
  lattice : LatticeData
  gramInverse : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  frame : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  inverse : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  leftGramInverse : gramInverse * gramComplex lattice = 1
  rightGramInverse : gramComplex lattice * gramInverse = 1
  leftFrameInverse : inverse * frame = 1
  rightFrameInverse : frame * inverse = 1
  beta : Charge lattice
  nullDirection : Fin lattice.rank → ℂ
  xAxis : Fin lattice.rank
  yAxis : Fin lattice.rank
  null : gramPair lattice nullDirection nullDirection = 0
  nonzero : chosenP lattice beta nullDirection ≠ 0
  distinct : xAxis ≠ yAxis
  xRow : frame xAxis = nullDirection
  yRow : frame yAxis = adaptedPartner lattice beta nullDirection
  xDual : ∀ row, gramPair lattice (frame yAxis) (frame row) = if row = xAxis then 1 else 0
  yDual : ∀ row, gramPair lattice (frame xAxis) (frame row) = if row = yAxis then 1 else 0
  level : ℤ
  steps : ℕ

abbrev signature : Signature where
  Params := Parameters
  State parameters := originalEnergySector parameters.lattice parameters.gramInverse
    parameters.beta parameters.level
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameters := State parameters.lattice
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ parameters state =>
      ((-(S parameters.lattice parameters.frame parameters.inverse
        parameters.leftFrameInverse parameters.rightFrameInverse parameters.xAxis parameters.yAxis
        (chosenP parameters.lattice parameters.beta parameters.nullDirection) *
        (Q parameters.lattice parameters.gramInverse - delta parameters.lattice
          (adaptedPartner parameters.lattice parameters.beta parameters.nullDirection)
          (chosenP parameters.lattice parameters.beta parameters.nullDirection)))) ^ parameters.steps)
        (P parameters.lattice parameters.frame parameters.inverse parameters.leftFrameInverse
          parameters.rightFrameInverse parameters.xAxis parameters.yAxis state.val))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameters state, observation.readout () parameters state ∈
    signedEnergyFiltration parameters.lattice parameters.frame parameters.beta
      parameters.xAxis parameters.yAxis parameters.level (parameters.steps : ℤ)

abbrev statement : Prop :=
  type_of% (@_root_.D5.S3.VertexAlgebra.OriginalQQuartetSource.original_projected_correction_pow_mem_filtration)

theorem bridge : statement ↔ arena.Law actual := by
  constructor
  · intro law parameters state
    exact law parameters.lattice parameters.gramInverse parameters.frame parameters.inverse
      parameters.leftGramInverse parameters.rightGramInverse parameters.leftFrameInverse
      parameters.rightFrameInverse parameters.beta parameters.nullDirection parameters.xAxis
      parameters.yAxis parameters.null parameters.nonzero parameters.distinct parameters.xRow
      parameters.yRow parameters.xDual parameters.yDual parameters.level state.val
      state.property.1 state.property.2 parameters.steps
  · intro law lattice gramInverse frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis null nonzero distinct
      xRow yRow xDual yDual level state sector energy steps
    exact law ⟨lattice, gramInverse, frame, inverse, leftGramInverse, rightGramInverse,
      leftFrameInverse, rightFrameInverse, beta, nullDirection, xAxis, yAxis, null, nonzero,
      distinct, xRow, yRow, xDual, yDual, level, steps⟩ ⟨state, sector, energy⟩

theorem actual_positive : arena.Law actual :=
  bridge.mp _root_.D5.S3.VertexAlgebra.OriginalQQuartetSource.original_projected_correction_pow_mem_filtration

end

end Reg.D5.S3.VertexAlgebra.OriginalQTransferredTermComputationTransient
