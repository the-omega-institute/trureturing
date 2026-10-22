import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendantCuts
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendantCuts

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendant
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendantCuts
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open scoped BigOperators

noncomputable section

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  weights : Fin lattice.rank → ℂ
  charge : Charge lattice
  exponent : ℤ

def signature : Signature where
  Params := Parameters
  State parameter := ℤ × ActualTensor parameter.lattice parameter.native
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def mixedReadout : Realization signature :=
  realize signature (fun _ parameter input =>
    ((Ytw parameter.lattice parameter.native
      (originalFirstDescendant parameter.lattice parameter.weights parameter.charge)).coeff
        parameter.exponent input.2 +
      (((input.1 : ℂ) + 1 / 2) *
        chargePairing parameter.lattice parameter.weights parameter.charge) •
      chargedCoefficient parameter.lattice parameter.native parameter.charge
        (parameter.exponent + 2) input.2,
    (∑ᶠ offset : ℕ, leftTerm parameter.lattice parameter.native parameter.weights
      parameter.charge parameter.exponent input.1 input.2 offset) +
    ∑ᶠ offset : ℕ, rightTerm parameter.lattice parameter.native parameter.weights
      parameter.charge parameter.exponent input.1 input.2 offset))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter input,
    (observation.readout () parameter input).1 = (observation.readout () parameter input).2

theorem mixedBridge : (type_of% (@native_first_descendant_mixed_iterate)) ↔
    arena.Law mixedReadout := by
  constructor
  · intro source parameter input
    exact source parameter.lattice parameter.native parameter.weights parameter.charge
      parameter.exponent input.1 input.2
  · intro law lattice native weights charge exponent cut vector
    exact law ⟨lattice, native, weights, charge, exponent⟩ ⟨cut, vector⟩

def summandReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (weights : Fin lattice.rank → ℂ) (charge : Charge lattice) (exponent cut : ℤ)
    (vector : ActualTensor lattice native) :=
  fun mode => cutSummand lattice native weights charge exponent cut mode vector

def leftReadout := @leftTerm
def rightReadout := @rightTerm

def stepReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (weights : Fin lattice.rank → ℂ) (charge : Charge lattice) (exponent cut : ℤ)
    (vector : ActualTensor lattice native) :=
  (cutProduct lattice native weights charge exponent (cut + 1) vector -
    cutProduct lattice native weights charge exponent cut vector,
    chargePairing lattice weights charge •
      chargedCoefficient lattice native charge (exponent + 2) vector)

def telescopeReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (weights : Fin lattice.rank → ℂ) (charge : Charge lattice) (exponent cut : ℤ)
    (vector : ActualTensor lattice native) :=
  (cutProduct lattice native weights charge exponent cut vector,
    cutProduct lattice native weights charge exponent 0 vector +
      ((cut : ℂ) * chargePairing lattice weights charge) •
        chargedCoefficient lattice native charge (exponent + 2) vector)

def reindexReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (weights : Fin lattice.rank → ℂ) (charge : Charge lattice) (exponent cut : ℤ)
    (vector : ActualTensor lattice native) :=
  (cutProduct lattice native weights charge exponent cut vector,
    (∑ᶠ offset : ℕ, leftTerm lattice native weights charge exponent cut vector offset) +
      ∑ᶠ offset : ℕ, rightTerm lattice native weights charge exponent cut vector offset)

def normalReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (weights : Fin lattice.rank → ℂ) (charge : Charge lattice) (exponent : ℤ)
    (vector : ActualTensor lattice native) :=
  (cutProduct lattice native weights charge exponent 0 vector,
    ∑ colour, weights colour •
      (normalInsertion lattice native (colour, 0) (chargedField lattice native charge)).coeff
        exponent vector)

def coefficientReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (weights : Fin lattice.rank → ℂ) (charge : Charge lattice) (exponent : ℤ)
    (vector : ActualTensor lattice native) :=
  ((Ytw lattice native (originalFirstDescendant lattice weights charge)).coeff exponent vector,
    cutProduct lattice native weights charge exponent 0 vector -
      (chargePairing lattice weights charge / 2) •
        chargedCoefficient lattice native charge (exponent + 2) vector)

def escapeFrom := @cutSummand
def continuation : Contract.Continuation Unit := .unknown
abbrev finiteContractObligation := Contract.Registration (@cutSummand_finite)
  (type_of% summandReadout) (type_of% escapeFrom) Unit
abbrev stepContractObligation := Contract.Registration (@cutProduct_step)
  (type_of% stepReadout) (type_of% escapeFrom) Unit
abbrev telescopeContractObligation := Contract.Registration (@cutProduct_telescope)
  (type_of% telescopeReadout) (type_of% escapeFrom) Unit
abbrev leftContractObligation := Contract.Registration (@leftTerm_finite)
  (type_of% leftReadout) (type_of% escapeFrom) Unit
abbrev rightContractObligation := Contract.Registration (@rightTerm_finite)
  (type_of% rightReadout) (type_of% escapeFrom) Unit
abbrev reindexContractObligation := Contract.Registration (@cutProduct_nat_reindex)
  (type_of% reindexReadout) (type_of% escapeFrom) Unit
abbrev normalContractObligation := Contract.Registration (@cutProduct_zero_normal)
  (type_of% normalReadout) (type_of% escapeFrom) Unit
abbrev coefficientContractObligation := Contract.Registration (@native_first_descendant_coefficient)
  (type_of% coefficientReadout) (type_of% escapeFrom) Unit
abbrev mixedRealizationObligation := Registration arena
  (type_of% (@native_first_descendant_mixed_iterate))
abbrev mixedContractObligation := Contract.Registration (@native_first_descendant_mixed_iterate)
  (type_of% mixedReadout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendantCuts
