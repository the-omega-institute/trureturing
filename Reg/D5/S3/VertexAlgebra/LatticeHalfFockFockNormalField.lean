import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure NormalParameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  index : Index lattice
  field : NativeField lattice native
  exponent : ℤ

def normalSignature : Signature where
  Params := NormalParameters
  State parameter := ActualTensor parameter.lattice parameter.native
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ℕ → ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def negativeReadout : Realization normalSignature :=
  realize normalSignature (fun _ parameter vector =>
    negativeTerm parameter.lattice parameter.native parameter.index parameter.field parameter.exponent vector)
    (fun empty => nomatch empty)

def positiveReadout : Realization normalSignature :=
  realize normalSignature (fun _ parameter vector =>
    positiveTerm parameter.lattice parameter.native parameter.index parameter.field parameter.exponent vector)
    (fun empty => nomatch empty)

def finiteArena : Arena where
  signature := normalSignature
  Law readout := ∀ parameter vector, Function.HasFiniteSupport (readout.readout () parameter vector)

theorem negativeBridge : (type_of% (@negativeTerm_finite)) ↔ finiteArena.Law negativeReadout := by
  constructor
  · intro source parameter vector
    exact source parameter.lattice parameter.native parameter.index parameter.field parameter.exponent vector
  · intro law lattice native index field exponent vector
    exact law ⟨lattice, native, index, field, exponent⟩ vector

theorem positiveBridge : (type_of% (@positiveTerm_finite)) ↔ finiteArena.Law positiveReadout := by
  constructor
  · intro source parameter vector
    exact source parameter.lattice parameter.native parameter.index parameter.field parameter.exponent vector
  · intro law lattice native index field exponent vector
    exact law ⟨lattice, native, index, field, exponent⟩ vector

def nativeEscapeFrom := @ActualTensor
def nativeContinuation : Contract.Continuation Unit := .unknown

abbrev negativeRealizationObligation := Registration finiteArena (type_of% (@negativeTerm_finite))
abbrev positiveRealizationObligation := Registration finiteArena (type_of% (@positiveTerm_finite))
abbrev negativeContractObligation := Contract.Registration (@negativeTerm_finite)
  (type_of% negativeReadout) (type_of% nativeEscapeFrom) Unit
abbrev positiveContractObligation := Contract.Registration (@positiveTerm_finite)
  (type_of% positiveReadout) (type_of% nativeEscapeFrom) Unit

structure TruncationParameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  index : Index lattice
  field : NativeField lattice native

def truncationSignature : Signature where
  Params := TruncationParameters
  State parameter := ActualTensor parameter.lattice parameter.native
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ℤ → ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def truncationReadout : Realization truncationSignature :=
  realize truncationSignature (fun _ parameter vector exponent =>
    normalCoefficient parameter.lattice parameter.native parameter.index parameter.field exponent vector)
    (fun empty => nomatch empty)

def truncationArena : Arena where
  signature := truncationSignature
  Law readout := ∀ parameter vector, ∃ lower : ℤ, ∀ exponent : ℤ,
    exponent < lower → readout.readout () parameter vector exponent = 0

theorem truncationBridge : (type_of% (@normalCoefficient_lower_truncation)) ↔
    truncationArena.Law truncationReadout := by
  constructor
  · intro source parameter vector
    exact source parameter.lattice parameter.native parameter.index parameter.field vector
  · intro law lattice native index field vector
    exact law ⟨lattice, native, index, field⟩ vector

abbrev truncationRealizationObligation := Registration truncationArena
  (type_of% (@normalCoefficient_lower_truncation))
abbrev truncationContractObligation := Contract.Registration (@normalCoefficient_lower_truncation)
  (type_of% truncationReadout) (type_of% nativeEscapeFrom) Unit

def identityReadout (lattice : LatticeData) (native : IsUnit lattice.G.det) :=
  (chargedField lattice native 0,
    _root_.D5.S3.VertexAlgebra.FieldNormalProduct.identityField
      (V := ActualTensor lattice native))

def unitReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (charge : Charge lattice) :=
  (normalPolynomial lattice native charge 1, chargedField lattice native charge)

def variableReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (charge : Charge lattice) (index : Index lattice) :=
  (normalPolynomial lattice native charge (MvPolynomial.X index),
    normalInsertion lattice native index (chargedField lattice native charge))

def shiftReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (field : NativeField lattice native) :=
  (shiftLinear lattice native 0 field, field)

def currentReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (colour : Fin lattice.rank) :=
  (normalInsertion lattice native (colour, 0)
      _root_.D5.S3.VertexAlgebra.FieldNormalProduct.identityField,
    _root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrentField lattice
      (ActualGround lattice native) colour)

abbrev identityContractObligation := Contract.Registration (@charged_zero_identity)
  (type_of% identityReadout) (type_of% nativeEscapeFrom) Unit
abbrev unitContractObligation := Contract.Registration (@normalPolynomial_one)
  (type_of% unitReadout) (type_of% nativeEscapeFrom) Unit
abbrev variableContractObligation := Contract.Registration (@normalPolynomial_X)
  (type_of% variableReadout) (type_of% nativeEscapeFrom) Unit
abbrev shiftContractObligation := Contract.Registration (@shiftLinear_zero)
  (type_of% shiftReadout) (type_of% nativeEscapeFrom) Unit
abbrev currentContractObligation := Contract.Registration (@normalInsertion_identity_current)
  (type_of% currentReadout) (type_of% nativeEscapeFrom) Unit

structure FlatParameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  field : NativeField lattice native
  word : List (Index lattice)
  exponent : ℤ

def flatSignature : Signature where
  Params := FlatParameters
  State parameter := ActualTensor parameter.lattice parameter.native
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ModeTuple parameter.lattice parameter.word →
    ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def flatReadout : Realization flatSignature :=
  realize flatSignature (fun _ parameter vector =>
    flatTerm parameter.lattice parameter.native parameter.field parameter.word
      parameter.exponent vector) (fun empty => nomatch empty)

def flatArena : Arena where
  signature := flatSignature
  Law readout := ∀ parameter vector, Function.HasFiniteSupport (readout.readout () parameter vector)

theorem flatBridge : (type_of% (@flatTerm_finite)) ↔ flatArena.Law flatReadout := by
  constructor
  · intro source parameter vector
    exact source parameter.lattice parameter.native parameter.field parameter.word parameter.exponent vector
  · intro law lattice native field word exponent vector
    exact law ⟨lattice, native, field, word, exponent⟩ vector

def factorizationReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (field : NativeField lattice native) (word : List (Index lattice))
    (modes : ModeTuple lattice word) (exponent : ℤ) :=
  (flatCoefficient lattice native field word modes exponent,
    leftAction lattice native word modes *
      field.coeff (exponent + 2 * modeSum lattice word modes + jetShift lattice word) *
        rightAction lattice native word modes)

def permutationReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (charge : Charge lattice) (first second : List (Index lattice)) :=
  (normalWord lattice native charge first, normalWord lattice native charge second)

def polynomialExpansionReadout (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (charge : Charge lattice) (polynomial : Oscillator lattice)
    (words : (Index lattice →₀ ℕ) → List (Index lattice)) :=
  (normalPolynomial lattice native charge polynomial, ∑ exponent ∈ polynomial.support,
    MvPolynomial.coeff exponent polynomial • normalWord lattice native charge (words exponent))

abbrev flatRealizationObligation := Registration flatArena (type_of% (@flatTerm_finite))
abbrev flatContractObligation := Contract.Registration (@flatTerm_finite)
  (type_of% flatReadout) (type_of% nativeEscapeFrom) Unit
abbrev supportContractObligation := Contract.Registration (@flatTerm_support_bound)
  (type_of% flatReadout) (type_of% nativeEscapeFrom) Unit
abbrev factorizationContractObligation := Contract.Registration (@flatCoefficient_factorization)
  (type_of% factorizationReadout) (type_of% nativeEscapeFrom) Unit
abbrev permutationContractObligation := Contract.Registration (@normalWord_perm)
  (type_of% permutationReadout) (type_of% nativeEscapeFrom) Unit
abbrev polynomialExpansionContractObligation := Contract.Registration (@normalPolynomial_enumerated_expansion)
  (type_of% polynomialExpansionReadout) (type_of% nativeEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
