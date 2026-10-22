import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeHalfFockChargedTranslationExtension
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedTranslationExtension

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockTranslationCalculus
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTranslationExtension

noncomputable section

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  charge : Charge lattice
  exponent : ℤ

def signature : Signature where
  Params := Parameters
  State parameter := ActualTensor parameter.lattice parameter.native
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def readout : Realization signature :=
  realize signature (fun _ parameter vector =>
    ((Ytw parameter.lattice parameter.native
      (_root_.D5.S3.VertexAlgebra.LatticeSugawaraConformal.translation parameter.lattice
        (Finsupp.single parameter.charge 1))).coeff parameter.exponent vector,
      (physicalDerivative parameter.lattice parameter.native
        (chargedField parameter.lattice parameter.native parameter.charge)).coeff
          parameter.exponent vector)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter vector,
    (observation.readout () parameter vector).1 = (observation.readout () parameter vector).2

theorem sourceBridge : (type_of% (@charged_physical_translation)) ↔ arena.Law readout := by
  constructor
  · intro source parameter vector
    exact congrArg (fun field => field.coeff parameter.exponent vector)
      (source parameter.lattice parameter.native parameter.charge)
  · intro law lattice native charge
    apply HVertexOperator.coeff_inj
    funext exponent
    apply LinearMap.ext
    intro vector
    exact law ⟨lattice, native, charge, exponent⟩ vector

def escapeFrom := @chargedCoefficient
def continuation : Contract.Continuation Unit := .unknown
abbrev realizationObligation := Registration arena (type_of% (@charged_physical_translation))
abbrev contractObligation := Contract.Registration (@charged_physical_translation)
  (type_of% readout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedTranslationExtension
