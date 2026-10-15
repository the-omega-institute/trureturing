import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendant
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendant

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendant
open scoped BigOperators

noncomputable section

def correctionReadout (lattice : LatticeData) (charge : Charge lattice)
    (colour : Fin lattice.rank) :=
  (Corr lattice charge (MvPolynomial.X (colour, 0)),
    Finsupp.single 0 (MvPolynomial.X (colour, 0)) +
      Finsupp.single 1 (-((bilinear lattice (unitCharge lattice colour) charge : ℂ) / 2) •
        (1 : Oscillator lattice)))

def fieldReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (charge : Charge lattice) (colour : Fin lattice.rank) :=
  (Ytw lattice native (Finsupp.single charge (MvPolynomial.X (colour, 0))),
    normalInsertion lattice native (colour, 0) (chargedField lattice native charge) -
      ((bilinear lattice (unitCharge lattice colour) charge : ℂ) / 2) •
        shiftLinear lattice native 1 (chargedField lattice native charge))

def sumFieldReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (weights : Fin lattice.rank → ℂ) (charge : Charge lattice) :=
  (Ytw lattice native (originalFirstDescendant lattice weights charge),
    ∑ colour, weights colour • (fieldReadout lattice native charge colour).2)

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  weights : Fin lattice.rank → ℂ
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

def coefficientReadout : Realization signature :=
  realize signature (fun _ parameter vector =>
    ((Ytw parameter.lattice parameter.native
      (originalFirstDescendant parameter.lattice parameter.weights parameter.charge)).coeff
        parameter.exponent vector,
      (∑ colour, parameter.weights colour •
        (normalInsertion parameter.lattice parameter.native (colour, 0)
          (chargedField parameter.lattice parameter.native parameter.charge)).coeff
            parameter.exponent vector) -
      (chargePairing parameter.lattice parameter.weights parameter.charge / 2) •
        chargedCoefficient parameter.lattice parameter.native parameter.charge
          (parameter.exponent + 2) vector))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter vector,
    (observation.readout () parameter vector).1 = (observation.readout () parameter vector).2

theorem coefficientBridge : (type_of% (@originalFirstDescendant_coefficient)) ↔
    arena.Law coefficientReadout := by
  constructor
  · intro source parameter vector
    exact source parameter.lattice parameter.native parameter.weights parameter.charge
      parameter.exponent vector
  · intro law lattice native weights charge exponent vector
    exact law ⟨lattice, native, weights, charge, exponent⟩ vector

def escapeFrom := @Ytw
def continuation : Contract.Continuation Unit := .unknown

abbrev correctionContractObligation := Contract.Registration (@Corr_charged_first_oscillator)
  (type_of% correctionReadout) (type_of% (@Corr)) Unit
abbrev fieldContractObligation := Contract.Registration (@charged_first_descendant_field)
  (type_of% fieldReadout) (type_of% escapeFrom) Unit
abbrev sumFieldContractObligation := Contract.Registration (@originalFirstDescendant_field)
  (type_of% sumFieldReadout) (type_of% escapeFrom) Unit
abbrev coefficientRealizationObligation := Registration arena
  (type_of% (@originalFirstDescendant_coefficient))
abbrev coefficientContractObligation := Contract.Registration (@originalFirstDescendant_coefficient)
  (type_of% coefficientReadout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendant
