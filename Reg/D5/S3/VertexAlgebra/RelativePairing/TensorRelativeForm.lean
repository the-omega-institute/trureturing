import D5.S3.VertexAlgebra.RelativePairing.TensorRelativeForm
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.RelativePairing.TensorRelativeForm

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
  _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianRelative
  _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

structure Parameters where
  lattice : LatticeData
  matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  leftGram : matrix * gramComplex lattice = 1
  rightGram : gramComplex lattice * matrix = 1

def signature : Signature where
  Params := Parameters
  State parameter := State parameter.lattice × State parameter.lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ × ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ parameter state =>
    (F parameter.lattice (Q parameter.lattice parameter.matrix state.1)
      (C parameter.lattice 0 state.2),
     F parameter.lattice state.2
      (C parameter.lattice 0 (Q parameter.lattice parameter.matrix state.1))))
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law realization := ∀ parameter state,
    B parameter.lattice 0 state.1 = 0 → B parameter.lattice 0 state.2 = 0 →
    Q parameter.lattice parameter.matrix state.2 = 0 →
    realization.readout () parameter state = (0, 0)

theorem sourceBridge : (type_of% (@boundary_pairing_vanishes)) ↔ arena.Law actual := by
  constructor
  · intro source parameter state relativePreimage relativeCycle closed
    exact Prod.ext
      (source parameter.lattice parameter.matrix parameter.leftGram parameter.rightGram
        state.1 state.2 relativePreimage relativeCycle closed).1
      (source parameter.lattice parameter.matrix parameter.leftGram parameter.rightGram
        state.1 state.2 relativePreimage relativeCycle closed).2
  · intro law lattice matrix leftGram rightGram preimage cycle relativePreimage relativeCycle closed
    have equality := law ⟨lattice, matrix, leftGram, rightGram⟩ (preimage, cycle)
      relativePreimage relativeCycle closed
    exact ⟨congrArg Prod.fst equality, congrArg Prod.snd equality⟩

abbrev AntighostTarget := type_of% (@F_B)
abbrev IsotropyTarget := type_of% (@relative_isotropic)
abbrev ParityTarget := type_of% (@Pi_relative)
abbrev ZeroModeSupportTarget := type_of% (@V0_relative)
abbrev LeftObstructionTarget := type_of% (@left_boundary_obstruction)
abbrev RightObstructionTarget := type_of% (@right_boundary_obstruction)

end

end Reg.D5.S3.VertexAlgebra.RelativePairing.TensorRelativeForm
