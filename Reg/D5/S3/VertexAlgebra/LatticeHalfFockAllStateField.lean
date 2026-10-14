import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockAllStateField

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure NativeParameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  charge : Charge lattice

def nativeSignature : Signature where
  Params := NativeParameters
  State parameter := Σ exponent : Index parameter.lattice →₀ ℕ,
    {word : List (Index parameter.lattice) // word.Perm
      (_root_.D5.S3.VertexAlgebra.LatticeAllStateField.occurrences parameter.lattice exponent)}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := NativeField parameter.lattice parameter.native ×
    NativeField parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def nativeReadout : Realization nativeSignature :=
  realize nativeSignature (fun _ parameter source =>
    (Ytw parameter.lattice parameter.native
      (Finsupp.single parameter.charge (MvPolynomial.monomial source.1 1)),
      correctedWord parameter.lattice parameter.native parameter.charge source.2.val))
    (fun empty => nomatch empty)

def nativeArena : Arena where
  signature := nativeSignature
  Law readout := ∀ parameter source,
    (readout.readout () parameter source).1 = (readout.readout () parameter source).2

theorem nativeBridge : (type_of% (@Ytw_monomial_enumeration)) ↔ nativeArena.Law nativeReadout := by
  constructor
  · intro source parameter monomial
    exact source parameter.lattice parameter.native parameter.charge
      monomial.1 monomial.2.val monomial.2.property
  · intro law lattice native charge exponent word enumeration
    exact law ⟨lattice, native, charge⟩ ⟨exponent, word, enumeration⟩

def nativeEscapeFrom := @Ytw
def nativeContinuation : Contract.Continuation Unit := .unknown
abbrev nativeRealizationObligation := Registration nativeArena (type_of% (@Ytw_monomial_enumeration))
abbrev nativeContractObligation := Contract.Registration (@Ytw_monomial_enumeration)
  (type_of% nativeReadout) (type_of% nativeEscapeFrom) Unit

def chargeReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (charge : Charge lattice) :=
  (Ytw lattice native (Finsupp.single charge 1), chargedField lattice native charge)

def vacuumReadout (lattice : LatticeData) (native : IsUnit lattice.G.det) :=
  (Ytw lattice native (Finsupp.single 0 1),
    _root_.D5.S3.VertexAlgebra.FieldNormalProduct.identityField (V := ActualTensor lattice native))

def insertionReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (index : Index lattice) :=
  (Ytw lattice native (Finsupp.single 0 (MvPolynomial.X index)),
    normalInsertion lattice native index
      _root_.D5.S3.VertexAlgebra.FieldNormalProduct.identityField)

def currentReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (colour : Fin lattice.rank) :=
  (Ytw lattice native (Finsupp.single 0 (MvPolynomial.X (colour, 0))),
    _root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrentField lattice
      (ActualGround lattice native) colour)

abbrev chargeContractObligation := Contract.Registration (@Ytw_charge)
  (type_of% chargeReadout) (type_of% nativeEscapeFrom) Unit
abbrev vacuumContractObligation := Contract.Registration (@Ytw_vacuum)
  (type_of% vacuumReadout) (type_of% nativeEscapeFrom) Unit
abbrev insertionContractObligation := Contract.Registration (@Ytw_current_insertion)
  (type_of% insertionReadout) (type_of% nativeEscapeFrom) Unit
abbrev currentContractObligation := Contract.Registration (@Ytw_current)
  (type_of% currentReadout) (type_of% nativeEscapeFrom) Unit

structure LowerParameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det

def lowerSignature : Signature where
  Params := LowerParameters
  State parameter := Σ state : Carrier parameter.lattice,
    Σ vector : ActualTensor parameter.lattice parameter.native,
      {exponent : ℤ // exponent <
        coefficientOrderMinimum parameter.lattice parameter.native state vector -
          2 * (sourceWeightBound parameter.lattice state : ℤ)}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def lowerReadout : Realization lowerSignature :=
  realize lowerSignature (fun _ parameter input =>
    (Ytw parameter.lattice parameter.native input.1).coeff input.2.2.val input.2.1)
    (fun empty => nomatch empty)

def lowerArena : Arena where
  signature := lowerSignature
  Law readout := ∀ (parameter : LowerParameters) (input : lowerSignature.State parameter),
    readout.readout () parameter input = (0 : ActualTensor parameter.lattice parameter.native)

theorem lowerBridge : (type_of% (@Ytw_source_lower_truncation)) ↔
    lowerArena.Law lowerReadout := by
  constructor
  · intro source parameter input
    exact source parameter.lattice parameter.native input.1 input.2.1
      input.2.2.val input.2.2.property
  · intro law lattice native state vector exponent below
    exact law ⟨lattice, native⟩ ⟨state, vector, exponent, below⟩

abbrev lowerRealizationObligation := Registration lowerArena
  (type_of% (@Ytw_source_lower_truncation))
abbrev lowerContractObligation := Contract.Registration (@Ytw_source_lower_truncation)
  (type_of% lowerReadout) (type_of% nativeEscapeFrom) Unit

def enumeratedExpansionReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (state : Carrier lattice)
    (words : Charge lattice → ℕ → (Index lattice →₀ ℕ) → List (Index lattice)) :=
  (Ytw lattice native state, ∑ charge ∈ state.support,
    ∑ shift ∈ (Corr lattice charge (state charge)).support,
      ∑ exponent ∈ (Corr lattice charge (state charge) shift).support,
        MvPolynomial.coeff exponent (Corr lattice charge (state charge) shift) •
          shiftLinear lattice native shift (normalWord lattice native charge (words charge shift exponent)))

def fockCoefficientReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (state : Carrier lattice) (vector : ActualTensor lattice native) (exponent : ℤ)
    (words : Charge lattice → ℕ → (Index lattice →₀ ℕ) → List (Index lattice)) :=
  ((Ytw lattice native state).coeff exponent vector, ∑ charge ∈ state.support,
    ∑ shift ∈ (Corr lattice charge (state charge)).support,
      ∑ monomial ∈ (Corr lattice charge (state charge) shift).support,
        MvPolynomial.coeff monomial (Corr lattice charge (state charge) shift) •
          ∑ᶠ modes : ModeTuple lattice (words charge shift monomial),
            leftAction lattice native (words charge shift monomial) modes
              (chargedCoefficient lattice native charge
                (exponent + 2 * shift + 2 * modeSum lattice (words charge shift monomial) modes +
                  jetShift lattice (words charge shift monomial))
                (rightAction lattice native (words charge shift monomial) modes vector)))

abbrev enumeratedExpansionContractObligation := Contract.Registration (@Ytw_enumerated_expansion)
  (type_of% enumeratedExpansionReadout) (type_of% nativeEscapeFrom) Unit
abbrev fockCoefficientContractObligation := Contract.Registration (@Ytw_fock_normal_coefficients)
  (type_of% fockCoefficientReadout) (type_of% nativeEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
