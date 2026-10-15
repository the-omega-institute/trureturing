import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockIntegralOddFixedSector

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockIntegralOddFixedSector

open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeHalfFock
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaFixed
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockIntegralOddFixedSector
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

def signature : Signature where
  Params := LeechNativeSpectrum
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter :=
    Submodule ℂ (ActualTensor LeechData parameter.native) ×
      Submodule ℂ (ActualTensor LeechData parameter.native)
  Anchor := Empty
  finiteAnchor := inferInstance

def readout : Realization signature :=
  realize signature (fun _ parameter _ =>
    ((⨆ value : ℤ, integralSector parameter value),
      oddTarget LeechData parameter.native)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter state,
    (observation.readout () parameter state).1 =
      (observation.readout () parameter state).2

theorem bridge : (type_of% (@integralSector_supremum)) ↔ arena.Law readout := by
  constructor
  · intro source parameter state
    exact source parameter
  · intro law spectrum
    exact law spectrum ()

def escapeFrom := @integralSector
def continuation : Contract.Continuation Unit := .unknown
abbrev realizationObligation := Registration arena (type_of% (@integralSector_supremum))
abbrev contractObligation := Contract.Registration (@integralSector_supremum)
  (type_of% readout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockIntegralOddFixedSector
