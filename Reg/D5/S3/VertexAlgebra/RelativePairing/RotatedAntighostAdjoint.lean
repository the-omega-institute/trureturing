import D5.S3.VertexAlgebra.RelativePairing.RotatedAntighostAdjoint
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.RelativePairing.RotatedAntighostAdjoint

open _root_.D5.S3.VertexAlgebra.BcGhostRotatedForm
  _root_.D5.S3.VertexAlgebra.BcGhostBpZForm
  _root_.D5.S3.VertexAlgebra.BcGhostFockSupport
  _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

def signature : Signature where
  Params := ℤ × _root_.D5.S3.VertexAlgebra.BcGhostBpZForm.GhostFock
  State _ := _root_.D5.S3.VertexAlgebra.BcGhostBpZForm.GhostFock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ parameter state => Hplus (b parameter.1 parameter.2) state)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law realization := ∀ parameter state,
    realization.readout () parameter state = Hplus (Pi parameter.2) (b (-parameter.1) state)

theorem sourceBridge : (type_of% (@Hplus_b)) ↔ arena.Law actual := by
  constructor
  · intro source parameter state
    exact source parameter.1 parameter.2 state
  · intro law mode left right
    exact law (mode, left) right

abbrev BilinearTarget := type_of% (@Gplus_b)

end

end Reg.D5.S3.VertexAlgebra.RelativePairing.RotatedAntighostAdjoint
