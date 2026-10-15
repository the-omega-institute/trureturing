import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

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

namespace HalfSuccessor

abbrev signature : Signature :=
  { Params := Unit
    State := fun _ => ℕ
    Role := Bool
    finiteRole := inferInstance
    nonemptyRole := inferInstance
    Output := fun _ _ => ℂ
    Anchor := Empty
    finiteAnchor := inferInstance }

def actual : Realization signature :=
  realize signature (fun _ _ degree => halfBinomial degree) (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ degree : ℕ,
    readout.readout false () (degree + 1) =
      ((-1 / 2 - (degree : ℂ)) * readout.readout true () degree) / (degree + 1 : ℂ)

theorem source_bridge : (type_of% (@half_successor)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have contradiction := law 0
  norm_num [rejected, realize] at contradiction

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, halfBinomial]

def familyRegistration : Registration arena (type_of% (@half_successor)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp half_successor, rejected, rejected_law⟩
  sensitivity := by
    classical
    constructor
    · intro role
      change Bool at role
      let bad : Realization signature := realize signature
        (fun other _ degree => if other = role then 0 else halfBinomial degree)
        (fun empty => nomatch empty)
      refine ⟨bad, ?_, rfl, ?_⟩
      · intro other different
        funext parameter degree
        dsimp only [actual, bad, realize]
        split_ifs with equal
        · exact (different equal).elim
        · rfl
      · intro law
        have contradiction := law 0
        cases role <;> norm_num [bad, realize, halfBinomial] at contradiction <;> cases contradiction
    · intro empty
      exact nomatch empty
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@half_successor) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.half_successor "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.HalfSuccessor.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "fn", "arg", "fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false },
      { path := #["body", "arg", "fn", "arg", "arg", "fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end HalfSuccessor

namespace PairReflection

abbrev signature : Signature :=
  { Params := Unit
    State := fun _ => ℕ
    Role := Bool
    finiteRole := inferInstance
    nonemptyRole := inferInstance
    Output := fun _ _ => ℕ → ℂ
    Anchor := Empty
    finiteAnchor := inferInstance }

def actual : Realization signature :=
  realize signature (fun _ _ first => pairScalar first) (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ first second : ℕ,
    readout.readout false () (first + 1) (second + 1) =
      ∑ left ∈ Finset.range (first + 1), ∑ right ∈ Finset.range (second + 1),
        (((-1 : ℂ) ^ (first + 1) * ((first + 1).choose (left + 1) : ℂ)) *
          ((-1 : ℂ) ^ (second + 1) * ((second + 1).choose (right + 1) : ℂ))) *
            readout.readout true () (left + 1) (right + 1)

theorem source_bridge : (type_of% (@pairScalar_reflection)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have contradiction := law 1 0
  norm_num [rejected, realize, Finset.sum_range_succ] at contradiction

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro equal
  have contradiction := congrFun equal 1
  norm_num [actual, realize, pairScalar, halfBinomial] at contradiction

def familyRegistration : Registration arena (type_of% (@pairScalar_reflection)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp pairScalar_reflection, rejected, rejected_law⟩
  sensitivity := by
    classical
    constructor
    · intro role
      change Bool at role
      let bad : Realization signature := realize signature
        (fun other _ first second => if other = role then 0 else pairScalar first second)
        (fun empty => nomatch empty)
      refine ⟨bad, ?_, rfl, ?_⟩
      · intro other different
        funext parameter first second
        dsimp only [actual, bad, realize]
        split_ifs with equal
        · exact (different equal).elim
        · rfl
      · intro law
        have contradiction := law 0 0
        cases role <;>
          norm_num [bad, realize, pairScalar, halfBinomial, Finset.sum_range_succ] at contradiction <;>
          cases contradiction
    · intro empty
      exact nomatch empty
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pairScalar_reflection) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.pairScalar_reflection "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.PairReflection.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "fn", "arg", "fn", "fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false },
      { path := #["body", "body", "arg", "arg", "body", "arg", "body", "arg", "fn", "fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end PairReflection

private def probeLattice : LatticeData where
  rank := 1
  G := fun _ _ => 2
  symmetric := by intros; rfl
  even_diagonal := by intro; exact ⟨1, rfl⟩

private def probeIndex : Index probeLattice := (⟨0, by decide⟩, 0)

namespace DerivationReadout

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ lattice : LatticeData, Index lattice)
  (fun parameter => CorrectionPolynomial parameter.1)
  (fun parameter => CorrectionPolynomial parameter.1)

def actual : Realization signature := realize signature
  (fun _ parameter polynomial => pairDerivation parameter.1 parameter.2 polynomial)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => 1)
  (fun empty => nomatch empty)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨probeLattice, probeIndex⟩, 0, MvPolynomial.X (some probeIndex), ?_⟩
  simp only [actual, realize, map_zero]
  rw [show pairDerivation probeLattice probeIndex (MvPolynomial.X (some probeIndex)) =
    pairPolynomial probeLattice probeIndex probeIndex by
      simp [pairDerivation, MvPolynomial.mkDerivation_X]]
  intro equal
  have value := congrArg (MvPolynomial.eval (fun _ : Option (Index probeLattice) => (1 : ℂ))) equal
  norm_num [pairPolynomial, pairScalar, sourceWeight, halfBinomial, probeIndex, probeLattice] at value
  change (2 : ℤ) = 0 at value
  norm_num at value

end DerivationReadout

namespace DerivationShift

abbrev signature := DerivationReadout.signature
abbrev actual := DerivationReadout.actual
abbrev rejected := DerivationReadout.rejected

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (index : Index lattice) (degree : ℕ),
    readout.readout () ⟨lattice, index⟩ (MvPolynomial.X none ^ degree) = 0

theorem source_bridge : (type_of% (@pairDerivation_shift)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have contradiction := law probeLattice probeIndex 0
  simpa [rejected, DerivationReadout.rejected, realize] using contradiction

def familyRegistration : Registration arena (type_of% (@pairDerivation_shift)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp pairDerivation_shift, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := DerivationReadout.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pairDerivation_shift) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.pairDerivation_shift "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.DerivationShift.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
    definition := none
    coordinates := #[0,1]
    readouts := #[
      { path := #["body", "body", "body", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end DerivationShift


namespace DerivationPair

abbrev signature := DerivationReadout.signature
abbrev actual := DerivationReadout.actual
abbrev rejected := DerivationReadout.rejected

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (index first second : Index lattice),
    readout.readout () ⟨lattice, index⟩ (pairPolynomial lattice first second) = 0

theorem source_bridge : (type_of% (@pairDerivation_pair)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have contradiction := law probeLattice probeIndex probeIndex probeIndex
  simpa [rejected, DerivationReadout.rejected, realize] using contradiction

def familyRegistration : Registration arena (type_of% (@pairDerivation_pair)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp pairDerivation_pair, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := DerivationReadout.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pairDerivation_pair) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.pairDerivation_pair "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.DerivationPair.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
    definition := none
    coordinates := #[0,1]
    readouts := #[
      { path := #["body", "body", "body", "body", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end DerivationPair

namespace UnitCorrection

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ lattice : LatticeData, Charge lattice) (fun parameter => Oscillator parameter.1)
  (fun parameter => ℕ →₀ Oscillator parameter.1)

def actual : Realization signature := realize signature
  (fun _ parameter polynomial => Corr parameter.1 parameter.2 polynomial)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun empty => nomatch empty)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨probeLattice, 0⟩, 0, 1, ?_⟩
  intro equal
  have value := congrArg (fun coefficients : ℕ →₀ Oscillator probeLattice => coefficients 0) equal
  have unit_value : (Corr probeLattice 0 1) 0 = 1 := by
    have source := Corr_monomial_enumeration probeLattice 0 0 [] (by
      simp [_root_.D5.S3.VertexAlgebra.LatticeAllStateField.occurrences])
    change Corr probeLattice 0 1 = _ at source
    rw [source, correctionWord, map_one]
    change (1 : Polynomial (Oscillator probeLattice)).toFinsupp.coeff 0 = 1
    simp [Polynomial.toFinsupp_apply]
  simp only [actual, realize] at value
  rw [unit_value] at value
  exact one_ne_zero value.symm

end UnitCorrection

namespace WordReadout

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ lattice : LatticeData, Charge lattice)
  (fun parameter => List (Index parameter.1))
  (fun parameter => CorrectionPolynomial parameter.1)

def actual : Realization signature := realize signature
  (fun _ parameter word => correctionWord parameter.1 parameter.2 word)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun empty => nomatch empty)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨probeLattice, 0⟩, [], [probeIndex], ?_⟩
  intro equal
  have value := congrArg MvPolynomial.constantCoeff equal
  simpa [actual, realize, correctionWord, insertion, singletonPolynomial, bilinear] using value

end WordReadout

namespace WordPermutation

abbrev signature := WordReadout.signature
abbrev actual := WordReadout.actual
abbrev rejected := WordReadout.rejected

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (charge : Charge lattice)
    (first second : List (Index lattice)), first.Perm second →
      readout.readout () ⟨lattice, charge⟩ first = correctionWord lattice charge second

theorem source_bridge : (type_of% (@correctionWord_permutation)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have contradiction := law probeLattice 0 [] [] (List.Perm.refl [])
  simpa [rejected, WordReadout.rejected, realize, correctionWord] using contradiction

def familyRegistration : Registration arena (type_of% (@correctionWord_permutation)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp correctionWord_permutation, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := WordReadout.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@correctionWord_permutation) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.correctionWord_permutation "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.WordPermutation.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
    definition := none
    coordinates := #[0, 1]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "fn", "arg", "fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end WordPermutation


namespace MatchingDerivative

abbrev signature := DerivationReadout.signature
abbrev actual := DerivationReadout.actual
abbrev rejected := DerivationReadout.rejected

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (charge : Charge lattice)
    (index : Index lattice) (word : List (Index lattice)),
    readout.readout () ⟨lattice, index⟩ (correctionWord lattice charge word) =
      ((labelledRemainders lattice word).map (fun entry =>
        pairPolynomial lattice index entry.1 * correctionWord lattice charge entry.2)).sum

theorem source_bridge : (type_of% (@pairDerivation_matching)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have contradiction := law probeLattice 0 probeIndex []
  simpa [rejected, DerivationReadout.rejected, realize, labelledRemainders] using contradiction

def familyRegistration : Registration arena (type_of% (@pairDerivation_matching)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp pairDerivation_matching, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := DerivationReadout.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pairDerivation_matching) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.pairDerivation_matching "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.MatchingDerivative.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
    definition := none
    coordinates := #[0, 2]
    readouts := #[
      { path := #["body", "body", "body", "body", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end MatchingDerivative


namespace WordMatching

abbrev signature := WordReadout.signature
abbrev actual := WordReadout.actual
abbrev rejected := WordReadout.rejected

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (charge : Charge lattice)
    (index : Index lattice) (word : List (Index lattice)),
    readout.readout () ⟨lattice, charge⟩ (index :: word) =
      (MvPolynomial.X (some index) + singletonPolynomial lattice charge index) *
        correctionWord lattice charge word +
      ((labelledRemainders lattice word).map (fun entry =>
        pairPolynomial lattice index entry.1 * correctionWord lattice charge entry.2)).sum

theorem source_bridge : (type_of% (@correctionWord_matching)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have contradiction := law probeLattice 0 probeIndex []
  have value := congrArg
    (MvPolynomial.eval (fun _ : Option (Index probeLattice) => (1 : ℂ))) contradiction
  simpa [rejected, WordReadout.rejected, realize, correctionWord, labelledRemainders,
    singletonPolynomial, bilinear] using value

def familyRegistration : Registration arena (type_of% (@correctionWord_matching)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp correctionWord_matching, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := WordReadout.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@correctionWord_matching) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.correctionWord_matching "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.WordMatching.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
    definition := none
    coordinates := #[0, 1]
    readouts := #[
      { path := #["body", "body", "body", "body", "fn", "arg", "fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end WordMatching


namespace MonomialEnumeration

abbrev signature := UnitCorrection.signature
abbrev actual := UnitCorrection.actual
abbrev rejected := UnitCorrection.rejected

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (charge : Charge lattice)
    (exponent : Index lattice →₀ ℕ) (word : List (Index lattice)),
    word.Perm (_root_.D5.S3.VertexAlgebra.LatticeAllStateField.occurrences lattice exponent) →
      readout.readout () ⟨lattice, charge⟩ (MvPolynomial.monomial exponent 1) =
        shiftCoefficients lattice (MvPolynomial.optionEquivLeft ℂ (Index lattice)
          (correctionWord lattice charge word))

theorem source_bridge : (type_of% (@Corr_monomial_enumeration)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have contradiction := law probeLattice 0 0 [] (by
    simp [_root_.D5.S3.VertexAlgebra.LatticeAllStateField.occurrences])
  have value := congrArg (fun coefficients : ℕ →₀ Oscillator probeLattice => coefficients 0) contradiction
  simp only [rejected, UnitCorrection.rejected, realize, correctionWord, map_one] at value
  change (0 : Oscillator probeLattice) = (1 : Polynomial (Oscillator probeLattice)).coeff 0 at value
  simpa using value

def familyRegistration : Registration arena (type_of% (@Corr_monomial_enumeration)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp Corr_monomial_enumeration, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := UnitCorrection.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Corr_monomial_enumeration) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.Corr_monomial_enumeration "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.MonomialEnumeration.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
    definition := none
    coordinates := #[0, 1]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end MonomialEnumeration


namespace WordBound

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature LatticeData
  (fun lattice => Polynomial (Oscillator lattice)) (fun _ => ℕ)

def actual : Realization signature := realize signature (fun _ _ polynomial => polynomial.natDegree)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => 1)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (charge : Charge lattice) (word : List (Index lattice)),
    readout.readout () lattice (MvPolynomial.optionEquivLeft ℂ (Index lattice)
      (correctionWord lattice charge word)) ≤ wordWeight lattice word

theorem source_bridge : (type_of% (@correctionWord_shift_bound)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have contradiction := law probeLattice 0 []
  simpa [rejected, realize, wordWeight] using contradiction

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨probeLattice, 0, Polynomial.X, ?_⟩
  simp [actual, realize]

def familyRegistration : Registration arena (type_of% (@correctionWord_shift_bound)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp correctionWord_shift_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@correctionWord_shift_bound) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.correctionWord_shift_bound "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.WordBound.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "body", "fn", "arg", "fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end WordBound


namespace PolynomialBound

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature := realize signature (fun _ _ shift => shift)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => 1)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (charge : Charge lattice) (polynomial : Oscillator lattice)
    (shift : ℕ), shift ∈ (Corr lattice charge polynomial).support →
      readout.readout () () shift ≤ MvPolynomial.weightedTotalDegree (sourceWeight lattice) polynomial

theorem source_bridge : (type_of% (@Corr_shift_bound)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have unit_value : (Corr probeLattice 0 1) 0 = 1 := by
    have source := Corr_monomial_enumeration probeLattice 0 0 [] (by
      simp [_root_.D5.S3.VertexAlgebra.LatticeAllStateField.occurrences])
    change Corr probeLattice 0 1 = _ at source
    rw [source, correctionWord, map_one]
    change (1 : Polynomial (Oscillator probeLattice)).toFinsupp.coeff 0 = 1
    simp [Polynomial.toFinsupp_apply]
  have member : 0 ∈ (Corr probeLattice 0 1).support := by
    rw [Finsupp.mem_support_iff]
    rw [unit_value]
    exact one_ne_zero
  have contradiction := law probeLattice 0 1 0 member
  simpa [rejected, realize, MvPolynomial.weightedTotalDegree] using contradiction

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨(), 0, 1, by simp [actual, realize]⟩

def familyRegistration : Registration arena (type_of% (@Corr_shift_bound)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp Corr_shift_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Corr_shift_bound) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.Corr_shift_bound "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.PolynomialBound.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "fn", "arg"]
        stateBinder := 3
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end PolynomialBound


namespace InsertionCommutation

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ lattice : LatticeData, Σ charge : Charge lattice, Σ first : Index lattice, Index lattice)
  (fun parameter => CorrectionPolynomial parameter.1)
  (fun parameter => CorrectionPolynomial parameter.1)

def actual : Realization signature := realize signature
  (fun _ parameter polynomial => insertion parameter.1 parameter.2.1 parameter.2.2.1
    (insertion parameter.1 parameter.2.1 parameter.2.2.2 polynomial))
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => 1)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (charge : Charge lattice) (first second : Index lattice)
    (polynomial : CorrectionPolynomial lattice),
    readout.readout () ⟨lattice, charge, first, second⟩ polynomial =
      insertion lattice charge second (insertion lattice charge first polynomial)

theorem source_bridge : (type_of% (@insertion_commute)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have contradiction := law probeLattice 0 probeIndex probeIndex 0
  simpa [rejected, realize] using contradiction

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨probeLattice, 0, probeIndex, probeIndex⟩, 0, 1, ?_⟩
  intro equal
  have value := congrArg
    (MvPolynomial.eval (fun _ : Option (Index probeLattice) => (1 : ℂ))) equal
  norm_num [actual, realize, insertion, singletonPolynomial, bilinear,
    pairDerivation, MvPolynomial.mkDerivation_X, Derivation.leibniz, smul_eq_mul,
    pairPolynomial, pairScalar, halfBinomial, sourceWeight, probeIndex, probeLattice] at value
  change (0 : ℂ) = 1 + 1 / 8 * 2 at value
  norm_num at value

def familyRegistration : Registration arena (type_of% (@insertion_commute)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp insertion_commute, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@insertion_commute) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.insertion_commute "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.InsertionCommutation.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "fn", "arg"]
        stateBinder := 4
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end InsertionCommutation


#print axioms HalfSuccessor.familyRegistration
#print axioms HalfSuccessor.registration
#print axioms PairReflection.familyRegistration
#print axioms PairReflection.registration

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
