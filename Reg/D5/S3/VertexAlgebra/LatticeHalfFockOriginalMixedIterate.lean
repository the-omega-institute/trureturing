import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeHalfFockOriginalMixedIterate
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalMixedIterate

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendant
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendantCuts
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockOriginalMixedIterate
open scoped VertexOperator

noncomputable section

def groundReadout (lattice : LatticeData) (weights : Fin lattice.rank → ℂ)
    (charge : Charge lattice) :=
  ((((sourceCurrent lattice weights)[[-1]]) (Finsupp.single charge 1),
      originalFirstDescendant lattice weights charge),
    (((sourceCurrent lattice weights)[[0]]) (Finsupp.single charge 1),
      chargePairing lattice weights charge • Finsupp.single charge (1 : Oscillator lattice)),
    fun mode : ℤ => ((sourceCurrent lattice weights)[[mode]]) (Finsupp.single charge 1))

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
      (((sourceCurrent parameter.lattice parameter.weights)[[-1]])
        (Finsupp.single parameter.charge 1))).coeff parameter.exponent input.2 +
      ((input.1 : ℂ) + 1 / 2) •
      (Ytw parameter.lattice parameter.native
        (((sourceCurrent parameter.lattice parameter.weights)[[0]])
          (Finsupp.single parameter.charge 1))).coeff (parameter.exponent + 2) input.2,
    (∑ᶠ offset : ℕ, leftTerm parameter.lattice parameter.native parameter.weights
      parameter.charge parameter.exponent input.1 input.2 offset) +
    ∑ᶠ offset : ℕ, rightTerm parameter.lattice parameter.native parameter.weights
      parameter.charge parameter.exponent input.1 input.2 offset))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter input,
    (observation.readout () parameter input).1 = (observation.readout () parameter input).2

theorem mixedBridge : (type_of% (@original_mixed_iterate_minus_one)) ↔
    arena.Law mixedReadout := by
  constructor
  · intro source parameter input
    exact source parameter.lattice parameter.native parameter.weights parameter.charge
      parameter.exponent input.1 input.2
  · intro law lattice native weights charge exponent cut vector
    exact law ⟨lattice, native, weights, charge, exponent⟩ ⟨cut, vector⟩

def escapeFrom := @Ytw
def continuation : Contract.Continuation Unit := .unknown
abbrev groundContractObligation := Contract.Registration (@sourceCurrent_ground_modes)
  (type_of% groundReadout) (type_of% (@sourceCurrent)) Unit
abbrev mixedRealizationObligation := Registration arena
  (type_of% (@original_mixed_iterate_minus_one))
abbrev mixedContractObligation := Contract.Registration (@original_mixed_iterate_minus_one)
  (type_of% mixedReadout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalMixedIterate
