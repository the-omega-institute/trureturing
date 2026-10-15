import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure InsertionParameters where
  lattice : LatticeData
  charge : Charge lattice
  first : Index lattice
  second : Index lattice

def insertionSignature : Signature where
  Params := InsertionParameters
  State parameter := CorrectionPolynomial parameter.lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := CorrectionPolynomial parameter.lattice × CorrectionPolynomial parameter.lattice
  Anchor := Empty
  finiteAnchor := inferInstance

def insertionReadout : Realization insertionSignature :=
  realize insertionSignature (fun _ parameter polynomial =>
    (insertion parameter.lattice parameter.charge parameter.first
        (insertion parameter.lattice parameter.charge parameter.second polynomial),
      insertion parameter.lattice parameter.charge parameter.second
        (insertion parameter.lattice parameter.charge parameter.first polynomial)))
    (fun empty => nomatch empty)

def insertionArena : Arena where
  signature := insertionSignature
  Law readout := ∀ parameter polynomial,
    (readout.readout () parameter polynomial).1 = (readout.readout () parameter polynomial).2

theorem insertionBridge : (type_of% (@insertion_commute)) ↔ insertionArena.Law insertionReadout := by
  constructor
  · intro source parameter polynomial
    exact source parameter.lattice parameter.charge parameter.first parameter.second polynomial
  · intro law lattice charge first second polynomial
    exact law ⟨lattice, charge, first, second⟩ polynomial

def correctionEscapeFrom := @CorrectionPolynomial
def correctionContinuation : Contract.Continuation Unit := .unknown

abbrev insertionRealizationObligation :=
  Registration insertionArena (type_of% (@insertion_commute))

abbrev insertionContractObligation := Contract.Registration (@insertion_commute)
  (type_of% insertionReadout) (type_of% correctionEscapeFrom) Unit

structure WordParameters where
  lattice : LatticeData
  charge : Charge lattice

def wordSignature : Signature where
  Params := WordParameters
  State parameter := {words : List (Index parameter.lattice) × List (Index parameter.lattice) //
    words.1.Perm words.2}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := CorrectionPolynomial parameter.lattice × CorrectionPolynomial parameter.lattice
  Anchor := Empty
  finiteAnchor := inferInstance

def wordReadout : Realization wordSignature :=
  realize wordSignature (fun _ parameter words =>
    (correctionWord parameter.lattice parameter.charge words.val.1,
      correctionWord parameter.lattice parameter.charge words.val.2)) (fun empty => nomatch empty)

def wordArena : Arena where
  signature := wordSignature
  Law readout := ∀ parameter words,
    (readout.readout () parameter words).1 = (readout.readout () parameter words).2

theorem wordBridge : (type_of% (@correctionWord_permutation)) ↔ wordArena.Law wordReadout := by
  constructor
  · intro source parameter words
    exact source parameter.lattice parameter.charge words.val.1 words.val.2 words.property
  · intro law lattice charge first second permutation
    exact law ⟨lattice, charge⟩ ⟨⟨first, second⟩, permutation⟩

abbrev wordRealizationObligation := Registration wordArena (type_of% (@correctionWord_permutation))
abbrev wordContractObligation := Contract.Registration (@correctionWord_permutation)
  (type_of% wordReadout) (type_of% correctionEscapeFrom) Unit

def enumerationSignature : Signature where
  Params := WordParameters
  State parameter := Σ exponent : Index parameter.lattice →₀ ℕ,
    {word : List (Index parameter.lattice) // word.Perm
      (_root_.D5.S3.VertexAlgebra.LatticeAllStateField.occurrences parameter.lattice exponent)}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := (ℕ →₀ Oscillator parameter.lattice) × (ℕ →₀ Oscillator parameter.lattice)
  Anchor := Empty
  finiteAnchor := inferInstance

def enumerationReadout : Realization enumerationSignature :=
  realize enumerationSignature (fun _ parameter source =>
    (Corr parameter.lattice parameter.charge (MvPolynomial.monomial source.1 1),
      shiftCoefficients parameter.lattice
        (MvPolynomial.optionEquivLeft ℂ (Index parameter.lattice)
          (correctionWord parameter.lattice parameter.charge source.2.val))))
    (fun empty => nomatch empty)

def enumerationArena : Arena where
  signature := enumerationSignature
  Law readout := ∀ parameter source,
    (readout.readout () parameter source).1 = (readout.readout () parameter source).2

theorem enumerationBridge : (type_of% (@Corr_monomial_enumeration)) ↔
    enumerationArena.Law enumerationReadout := by
  constructor
  · intro source parameter monomial
    exact source parameter.lattice parameter.charge monomial.1 monomial.2.val monomial.2.property
  · intro law lattice charge exponent word enumeration
    exact law ⟨lattice, charge⟩ ⟨exponent, word, enumeration⟩

abbrev enumerationRealizationObligation := Registration enumerationArena
  (type_of% (@Corr_monomial_enumeration))
abbrev enumerationContractObligation := Contract.Registration (@Corr_monomial_enumeration)
  (type_of% enumerationReadout) (type_of% correctionEscapeFrom) Unit

structure MatchingParameters where
  lattice : LatticeData
  charge : Charge lattice
  index : Index lattice

def matchingSignature : Signature where
  Params := MatchingParameters
  State parameter := List (Index parameter.lattice)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := CorrectionPolynomial parameter.lattice × CorrectionPolynomial parameter.lattice
  Anchor := Empty
  finiteAnchor := inferInstance

def derivativeReadout : Realization matchingSignature :=
  realize matchingSignature (fun _ parameter word =>
    (pairDerivation parameter.lattice parameter.index
        (correctionWord parameter.lattice parameter.charge word),
      ((labelledRemainders parameter.lattice word).map (fun entry =>
        pairPolynomial parameter.lattice parameter.index entry.1 *
          correctionWord parameter.lattice parameter.charge entry.2)).sum))
    (fun empty => nomatch empty)

def matchingReadout : Realization matchingSignature :=
  realize matchingSignature (fun _ parameter word =>
    (correctionWord parameter.lattice parameter.charge (parameter.index :: word),
      (MvPolynomial.X (some parameter.index) +
        singletonPolynomial parameter.lattice parameter.charge parameter.index) *
          correctionWord parameter.lattice parameter.charge word +
        ((labelledRemainders parameter.lattice word).map (fun entry =>
          pairPolynomial parameter.lattice parameter.index entry.1 *
            correctionWord parameter.lattice parameter.charge entry.2)).sum))
    (fun empty => nomatch empty)

def matchingArena : Arena where
  signature := matchingSignature
  Law readout := ∀ parameter word,
    (readout.readout () parameter word).1 = (readout.readout () parameter word).2

theorem derivativeBridge : (type_of% (@pairDerivation_matching)) ↔
    matchingArena.Law derivativeReadout := by
  constructor
  · intro source parameter word
    exact source parameter.lattice parameter.charge parameter.index word
  · intro law lattice charge index word
    exact law ⟨lattice, charge, index⟩ word

theorem matchingBridge : (type_of% (@correctionWord_matching)) ↔
    matchingArena.Law matchingReadout := by
  constructor
  · intro source parameter word
    exact source parameter.lattice parameter.charge parameter.index word
  · intro law lattice charge index word
    exact law ⟨lattice, charge, index⟩ word

abbrev derivativeRealizationObligation := Registration matchingArena
  (type_of% (@pairDerivation_matching))
abbrev matchingRealizationObligation := Registration matchingArena
  (type_of% (@correctionWord_matching))
abbrev derivativeContractObligation := Contract.Registration (@pairDerivation_matching)
  (type_of% derivativeReadout) (type_of% correctionEscapeFrom) Unit
abbrev matchingContractObligation := Contract.Registration (@correctionWord_matching)
  (type_of% matchingReadout) (type_of% correctionEscapeFrom) Unit

def wordBoundSignature : Signature where
  Params := WordParameters
  State parameter := List (Index parameter.lattice)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ × ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def wordBoundReadout : Realization wordBoundSignature :=
  realize wordBoundSignature (fun _ parameter word =>
    ((MvPolynomial.optionEquivLeft ℂ (Index parameter.lattice)
      (correctionWord parameter.lattice parameter.charge word)).natDegree,
      wordWeight parameter.lattice word)) (fun empty => nomatch empty)

def wordBoundArena : Arena where
  signature := wordBoundSignature
  Law readout := ∀ parameter word,
    (readout.readout () parameter word).1 ≤ (readout.readout () parameter word).2

theorem wordBoundBridge : (type_of% (@correctionWord_shift_bound)) ↔
    wordBoundArena.Law wordBoundReadout := by
  constructor
  · intro source parameter word
    exact source parameter.lattice parameter.charge word
  · intro law lattice charge word
    exact law ⟨lattice, charge⟩ word

abbrev wordBoundRealizationObligation := Registration wordBoundArena
  (type_of% (@correctionWord_shift_bound))
abbrev wordBoundContractObligation := Contract.Registration (@correctionWord_shift_bound)
  (type_of% wordBoundReadout) (type_of% correctionEscapeFrom) Unit

def polynomialBoundSignature : Signature where
  Params := WordParameters
  State parameter := Σ polynomial : Oscillator parameter.lattice,
    {shift : ℕ // shift ∈ (Corr parameter.lattice parameter.charge polynomial).support}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ × ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def polynomialBoundReadout : Realization polynomialBoundSignature :=
  realize polynomialBoundSignature (fun _ parameter input =>
    (input.2.val, MvPolynomial.weightedTotalDegree (sourceWeight parameter.lattice) input.1))
    (fun empty => nomatch empty)

def polynomialBoundArena : Arena where
  signature := polynomialBoundSignature
  Law readout := ∀ parameter input,
    (readout.readout () parameter input).1 ≤ (readout.readout () parameter input).2

theorem polynomialBoundBridge : (type_of% (@Corr_shift_bound)) ↔
    polynomialBoundArena.Law polynomialBoundReadout := by
  constructor
  · intro source parameter input
    exact source parameter.lattice parameter.charge input.1 input.2.val input.2.property
  · intro law lattice charge polynomial shift member
    exact law ⟨lattice, charge⟩ ⟨polynomial, shift, member⟩

abbrev polynomialBoundRealizationObligation := Registration polynomialBoundArena
  (type_of% (@Corr_shift_bound))
abbrev polynomialBoundContractObligation := Contract.Registration (@Corr_shift_bound)
  (type_of% polynomialBoundReadout) (type_of% correctionEscapeFrom) Unit

def unitReadout (lattice : LatticeData) (charge : Charge lattice) :=
  (Corr lattice charge 1, Finsupp.single (0 : ℕ) (1 : Oscillator lattice))

def variableReadout (lattice : LatticeData) (index : Index lattice) :
    (ℕ →₀ Oscillator lattice) × (ℕ →₀ Oscillator lattice) :=
  (Corr lattice 0 (MvPolynomial.X index), Finsupp.single (0 : ℕ) (MvPolynomial.X index))

abbrev unitContractObligation := Contract.Registration (@Corr_one)
  (type_of% unitReadout) (type_of% correctionEscapeFrom) Unit
abbrev variableContractObligation := Contract.Registration (@Corr_X_zero)
  (type_of% variableReadout) (type_of% correctionEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
