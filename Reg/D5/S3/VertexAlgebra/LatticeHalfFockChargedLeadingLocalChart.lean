import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockChargedLeadingLocalChart

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedLeadingLocalChart

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedLeadingLocalChart

noncomputable section

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  left : Charge lattice
  right : Charge lattice
  first : ℤ
  second : ℤ
  state : ActualTensor lattice native
  offset : ℕ

def signature : Signature where
  Params := Parameters
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def readout : Realization signature :=
  realize signature (fun _ parameter _ =>
    let gram := bilinear parameter.lattice parameter.left parameter.right
    (clearedProductTerm parameter.lattice parameter.native parameter.left parameter.right
      parameter.first parameter.second parameter.state parameter.offset,
      (((-1 : ℂ) ^ parameter.offset) * (gram.natAbs.choose parameter.offset : ℂ)) •
        ((chargeScalar parameter.lattice parameter.left *
          chargeScalar parameter.lattice parameter.right) •
          tensorCoefficientExpansion parameter.lattice parameter.native parameter.left
            parameter.right (halfContraction parameter.lattice parameter.left parameter.right)
            (parameter.first - 2 * (((gram.natAbs - parameter.offset : ℕ) : ℤ)) +
              chargeNorm parameter.lattice parameter.left)
            (parameter.second - 2 * (parameter.offset : ℤ) +
              chargeNorm parameter.lattice parameter.right) parameter.state)))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter, ∀ input : Unit,
    (observation.readout () parameter input).1 =
      (observation.readout () parameter input).2

theorem bridge : (type_of% (@cleared_product_term_expansion)) ↔ arena.Law readout := by
  constructor
  · intro source parameter input
    exact source parameter.lattice parameter.native parameter.left parameter.right
      parameter.first parameter.second parameter.state parameter.offset
  · intro law lattice native left right first second state offset
    exact law ⟨lattice, native, left, right, first, second, state, offset⟩ ()

def escapeFrom := @clearedProductTerm
def continuation : Contract.Continuation Unit := .unknown
abbrev realizationObligation := Registration arena (type_of% (@cleared_product_term_expansion))
abbrev contractObligation := Contract.Registration (@cleared_product_term_expansion)
  (type_of% readout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedLeadingLocalChart
