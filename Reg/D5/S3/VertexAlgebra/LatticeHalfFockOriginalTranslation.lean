import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation

noncomputable section

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  exponent : ℤ

def signature : Signature where
  Params := Parameters
  State parameter := Carrier parameter.lattice × ActualTensor parameter.lattice parameter.native
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def readout : Realization signature :=
  realize signature (fun _ parameter states =>
    ((Ytw parameter.lattice parameter.native
      (_root_.D5.S3.VertexAlgebra.LatticeSugawaraConformal.translation parameter.lattice states.1)).coeff
        parameter.exponent states.2,
      (((parameter.exponent + 2 : ℤ) : ℂ) / 2) •
        (Ytw parameter.lattice parameter.native states.1).coeff (parameter.exponent + 2) states.2))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter states,
    (observation.readout () parameter states).1 = (observation.readout () parameter states).2

theorem sourceBridge : (type_of% (@Ytw_translation_physical)) ↔ arena.Law readout := by
  constructor
  · intro source parameter states
    exact source parameter.lattice parameter.native states.1 parameter.exponent states.2
  · intro law lattice native source exponent vector
    exact law ⟨lattice, native, exponent⟩ (source, vector)

def escapeFrom := @_root_.D5.S3.VertexAlgebra.LatticeSugawaraConformal.translation
def continuation : Contract.Continuation Unit := .unknown
abbrev realizationObligation := Registration arena (type_of% (@Ytw_translation_physical))
abbrev contractObligation := Contract.Registration (@Ytw_translation_physical)
  (type_of% readout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
