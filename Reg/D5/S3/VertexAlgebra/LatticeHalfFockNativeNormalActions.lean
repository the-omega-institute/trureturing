import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockNativeNormalActions

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeNormalActions

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockNativeNormalActions
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  word : List (Index lattice)
  modes : ModeTuple lattice word
  polynomial : Oscillator lattice

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

def positiveReadout : Realization signature :=
  realize signature (fun _ parameter state =>
    (rightAction parameter.lattice parameter.native parameter.word parameter.modes
      (tensorMultiply parameter.lattice parameter.native parameter.polynomial state),
    ((derivativeSplits parameter.lattice
      (positiveDerivatives parameter.lattice parameter.word parameter.modes)).map
        (rightSplitAction parameter.lattice parameter.native parameter.polynomial)).sum state))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter state,
    (observation.readout () parameter state).1 = (observation.readout () parameter state).2

theorem positiveBridge :
    (type_of% (@actual_positive_word_leibniz)) ↔ arena.Law positiveReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.native parameter.word parameter.modes
      parameter.polynomial state
  · intro law lattice native word modes polynomial state
    exact law ⟨lattice, native, word, modes, polynomial⟩ state

def escapeFrom := @rightAction
def continuation : Contract.Continuation Unit := .unknown

abbrev positiveRealizationObligation :=
  Registration arena (type_of% (@actual_positive_word_leibniz))

abbrev positiveContractObligation := Contract.Registration
  (@actual_positive_word_leibniz) (type_of% positiveReadout) (type_of% escapeFrom) Unit

structure WordParameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  charge : Charge lattice
  word : List (Index lattice)
  exponent : ℤ
  polynomial : Oscillator lattice

def wordSignature : Signature where
  Params := WordParameters
  State parameter := ActualTensor parameter.lattice parameter.native
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    (ModeTuple parameter.lattice parameter.word → ActualTensor parameter.lattice parameter.native)
  Anchor := Empty
  finiteAnchor := inferInstance

def wordReadout : Realization wordSignature :=
  realize wordSignature (fun _ parameter state =>
    ((normalWord parameter.lattice parameter.native parameter.charge parameter.word).coeff
      parameter.exponent (tensorMultiply parameter.lattice parameter.native parameter.polynomial state),
    fun modes => normalSplitCoefficient parameter.lattice parameter.native parameter.charge
      parameter.word parameter.exponent parameter.polynomial modes state))
    (fun empty => nomatch empty)

def wordArena : Arena where
  signature := wordSignature
  Law observation := ∀ parameter state,
    ∃ finiteModes : Finset (ModeTuple parameter.lattice parameter.word),
      (∀ modes ∉ finiteModes, (observation.readout () parameter state).2 modes = 0) ∧
      (observation.readout () parameter state).1 =
        ∑ modes ∈ finiteModes, (observation.readout () parameter state).2 modes

theorem wordBridge :
    (type_of% (@actual_normal_word_finite_action)) ↔ wordArena.Law wordReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.native parameter.charge parameter.word
      parameter.exponent parameter.polynomial state
  · intro law lattice native charge word exponent polynomial state
    exact law ⟨lattice, native, charge, word, exponent, polynomial⟩ state

abbrev wordRealizationObligation :=
  Registration wordArena (type_of% (@actual_normal_word_finite_action))

abbrev finiteActionContractObligation := Contract.Registration
  (@actual_normal_word_finite_action) (type_of% wordReadout) (type_of% (@normalWord)) Unit

structure CorrectionParameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  charge : Charge lattice
  source : CorrectionPolynomial lattice
  exponent : ℤ
  polynomial : Oscillator lattice

def correctionSignature : Signature where
  Params := CorrectionParameters
  State parameter := ActualTensor parameter.lattice parameter.native
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    ((shift : ℕ) → (monomial : Index parameter.lattice →₀ ℕ) →
      ModeTuple parameter.lattice
        (_root_.D5.S3.VertexAlgebra.LatticeAllStateField.occurrences parameter.lattice monomial) →
          ActualTensor parameter.lattice parameter.native)
  Anchor := Empty
  finiteAnchor := inferInstance

def correctionReadout : Realization correctionSignature :=
  realize correctionSignature (fun _ parameter state =>
    ((nativeCorrectionEvaluation parameter.lattice parameter.native parameter.charge
      parameter.source).coeff parameter.exponent
        (tensorMultiply parameter.lattice parameter.native parameter.polynomial state),
    fun shift monomial modes => normalSplitCoefficient parameter.lattice parameter.native
      parameter.charge
      (_root_.D5.S3.VertexAlgebra.LatticeAllStateField.occurrences parameter.lattice monomial)
      (parameter.exponent + 2 * shift) parameter.polynomial modes state))
    (fun empty => nomatch empty)

def correctionArena : Arena where
  signature := correctionSignature
  Law observation := ∀ (parameter : CorrectionParameters)
      (state : ActualTensor parameter.lattice parameter.native),
    ∃ finiteModes : (shift : ℕ) → (monomial : Index parameter.lattice →₀ ℕ) →
        Finset (ModeTuple parameter.lattice
          (_root_.D5.S3.VertexAlgebra.LatticeAllStateField.occurrences parameter.lattice monomial)),
      (∀ shift : ℕ, shift ∈ (correctionCoefficients parameter.lattice parameter.source).support →
        ∀ monomial : Index parameter.lattice →₀ ℕ,
          monomial ∈ (correctionCoefficients parameter.lattice parameter.source shift).support →
          ∀ modes ∉ finiteModes shift monomial,
            (observation.readout () parameter state).2 shift monomial modes = 0) ∧
      (observation.readout () parameter state).1 =
        ∑ shift ∈ (correctionCoefficients parameter.lattice parameter.source).support,
          ∑ monomial ∈ (correctionCoefficients parameter.lattice parameter.source shift).support,
            MvPolynomial.coeff monomial
              (correctionCoefficients parameter.lattice parameter.source shift) •
              ∑ modes ∈ finiteModes shift monomial,
                (observation.readout () parameter state).2 shift monomial modes

theorem correctionBridge :
    (type_of% (@actual_native_correction_finite_action)) ↔
      correctionArena.Law correctionReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.native parameter.charge parameter.source
      parameter.exponent parameter.polynomial state
  · intro law lattice native charge source exponent polynomial state
    exact law ⟨lattice, native, charge, source, exponent, polynomial⟩ state

abbrev correctionRealizationObligation :=
  Registration correctionArena (type_of% (@actual_native_correction_finite_action))

abbrev correctionContractObligation := Contract.Registration
  (@actual_native_correction_finite_action) (type_of% correctionReadout)
    (type_of% (@nativeCorrectionEvaluation)) Unit

#print axioms positiveBridge
#print axioms wordBridge
#print axioms correctionBridge

end

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeNormalActions
