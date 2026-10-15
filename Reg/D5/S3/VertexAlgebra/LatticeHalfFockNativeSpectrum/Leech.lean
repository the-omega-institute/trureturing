import Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.WeightTwo
import Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.DirectSum
import D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Leech

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Leech

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped TensorProduct

noncomputable section

def leechSignature : Signature where
  Params := Unit
  State _ := Fin LeechData.rank ×
    _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.Half
      (groundRank LeechData explicitLeechSpectrum.native)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ActualTensor LeechData explicitLeechSpectrum.native ×
    ActualTensor LeechData explicitLeechSpectrum.native
  Anchor := Empty
  finiteAnchor := inferInstance

def leechReadout : Realization leechSignature :=
  realize leechSignature (fun _ _ label =>
    ((explicitLeechSpectrum.basis label).val,
      (MvPolynomial.X (label.1, 0) : Oscillator LeechData) ⊗ₜ[ℂ] Pi.single label.2 (1 : ℂ)))
    (fun empty => nomatch empty)

def leechArena : Arena where
  signature := leechSignature
  Law readout := ∀ parameter label,
    (readout.readout () parameter label).1 = (readout.readout () parameter label).2

theorem leechLaw : leechArena.Law leechReadout := by
  intro parameter label
  exact explicitLeechSpectrum.basisVectors label

def leechEscapeFrom := @explicitLeechSpectrum
def leechContinuation : Contract.Continuation Unit := .unknown
abbrev leechRegistrationObligation := Registration leechArena (leechArena.Law leechReadout)

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Leech
