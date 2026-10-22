import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeHalfFockChargedTranslation
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedTranslation

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTranslation
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open scoped TensorProduct

noncomputable section

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  charge : Charge lattice
  exponent : ℤ

def signature : Signature where
  Params := Parameters
  State parameter := ActualGround parameter.lattice parameter.native
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def readout : Realization signature :=
  realize signature (fun _ parameter ground =>
    ((Ytw parameter.lattice parameter.native
      (_root_.D5.S3.VertexAlgebra.LatticeSugawaraConformal.translation parameter.lattice
        (Finsupp.single parameter.charge 1))).coeff parameter.exponent (1 ⊗ₜ[ℂ] ground),
      (((parameter.exponent + 2 : ℤ) : ℂ) / 2) •
        (Ytw parameter.lattice parameter.native (Finsupp.single parameter.charge 1)).coeff
          (parameter.exponent + 2) (1 ⊗ₜ[ℂ] ground)))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter ground,
    (observation.readout () parameter ground).1 = (observation.readout () parameter ground).2

theorem sourceBridge : (type_of% (@original_ground_translation_physical)) ↔ arena.Law readout := by
  constructor
  · intro source parameter ground
    exact source parameter.lattice parameter.native parameter.charge parameter.exponent ground
  · intro law lattice native charge exponent ground
    exact law ⟨lattice, native, charge, exponent⟩ ground

def escapeFrom := @halfCreationExponential
def continuation : Contract.Continuation Unit := .unknown
abbrev realizationObligation := Registration arena (type_of% (@original_ground_translation_physical))
abbrev contractObligation := Contract.Registration (@original_ground_translation_physical)
  (type_of% readout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedTranslation
