import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeHalfFockTranslationCalculus
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockTranslationCalculus

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockTranslationCalculus

noncomputable section

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  index : Index lattice
  field : NativeField lattice native
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

def derivativeReadout : Realization signature :=
  realize signature (fun _ parameter vector =>
    ((physicalDerivative parameter.lattice parameter.native
      (normalInsertion parameter.lattice parameter.native parameter.index parameter.field)).coeff
        parameter.exponent vector,
      (((parameter.index.2 + 1 : ℂ) • normalInsertion parameter.lattice parameter.native
        (parameter.index.1, parameter.index.2 + 1) parameter.field +
          normalInsertion parameter.lattice parameter.native parameter.index
            (physicalDerivative parameter.lattice parameter.native parameter.field)).coeff
              parameter.exponent vector)))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter vector,
    (observation.readout () parameter vector).1 = (observation.readout () parameter vector).2

theorem derivativeBridge : (type_of% (@normalInsertion_physical_derivative)) ↔
    arena.Law derivativeReadout := by
  constructor
  · intro source parameter vector
    exact congrArg (fun field => field.coeff parameter.exponent vector)
      (source parameter.lattice parameter.native parameter.index parameter.field)
  · intro law lattice native index field
    apply HVertexOperator.coeff_inj
    funext exponent
    apply LinearMap.ext
    intro vector
    exact law ⟨lattice, native, index, field, exponent⟩ vector

def escapeFrom := @normalInsertion
def continuation : Contract.Continuation Unit := .unknown

abbrev derivativeRealizationObligation := Registration arena
  (type_of% (@normalInsertion_physical_derivative))
abbrev derivativeContractObligation := Contract.Registration (@normalInsertion_physical_derivative)
  (type_of% derivativeReadout) (type_of% escapeFrom) Unit

def wordReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (word : List (Index lattice)) (field : NativeField lattice native) :=
  (physicalDerivative lattice native (normalSequence lattice native field word),
    ((labelledRemainders lattice word).map (fun entry =>
      (sourceWeight lattice entry.1 : ℂ) •
        normalInsertion lattice native (entry.1.1, entry.1.2 + 1)
          (normalSequence lattice native field entry.2))).sum +
      normalSequence lattice native (physicalDerivative lattice native field) word)

abbrev wordContractObligation := Contract.Registration (@normalSequence_physical_derivative)
  (type_of% wordReadout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockTranslationCalculus
