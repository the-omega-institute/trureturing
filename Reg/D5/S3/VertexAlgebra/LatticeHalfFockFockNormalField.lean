/- Dependent-family audit attempts preserve the original determinant witness and actual carrier. -/
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators TensorProduct

noncomputable section

/- Same actual indefinite-lattice probe as the existing charged-tensor owner.
These are certificate witnesses, not replacement production operators. -/
private def hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro first second; fin_cases first <;> fin_cases second <;> rfl
  even_diagonal := by intro axis; fin_cases axis <;> exact ⟨0, rfl⟩

private theorem hyperbolic_unit : IsUnit hyperbolic.G.det := by
  have determinant : hyperbolic.G.det = -1 := by
    change (Matrix.det (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ)) = -1
    norm_num [Matrix.det_fin_two]
  rw [determinant]
  exact isUnit_neg_one

private def probeGround : ActualGround hyperbolic hyperbolic_unit := fun _ => 1

private theorem probeGround_nonzero : probeGround ≠ 0 := by
  intro equality
  have coordinate := congrFun equality (0 : Half (groundRank hyperbolic hyperbolic_unit))
  exact one_ne_zero (show (1 : ℂ) = 0 from coordinate)

private def probeState : ActualTensor hyperbolic hyperbolic_unit :=
  (1 : Oscillator hyperbolic) ⊗ₜ[ℂ] probeGround

private def probeSeed : NativeField hyperbolic hyperbolic_unit :=
  chargedField hyperbolic hyperbolic_unit 0

private theorem probe_leading : probeSeed.coeff 0 probeState ≠ 0 := by
  change chargedCoefficient hyperbolic hyperbolic_unit 0 0
    ((1 : Oscillator hyperbolic) ⊗ₜ[ℂ] probeGround) ≠ 0
  simpa [chargeNorm, bilinear] using
    charged_ground_leading hyperbolic hyperbolic_unit 0 probeGround probeGround_nonzero

private theorem probe_negative (exponent : ℤ) (negative : exponent < 0) :
    probeSeed.coeff exponent probeState = 0 := by
  change chargedCoefficient hyperbolic hyperbolic_unit 0 exponent
    ((1 : Oscillator hyperbolic) ⊗ₜ[ℂ] probeGround) = 0
  apply charged_polynomial_lower_bound
  simpa [chargeNorm, bilinear, nativeOddWeightedDegree,
    MvPolynomial.weightedTotalDegree] using negative

private theorem probeState_nonzero : probeState ≠ 0 := by
  intro zero
  apply probe_leading
  rw [zero, map_zero]

private theorem wordCoefficient_nil (D : LatticeData) (hu : IsUnit D.G.det)
    (seed : NativeField D hu) (exponent : ℤ) (vector : ActualTensor D hu) :
    wordCoefficient D hu seed [] exponent vector = seed.coeff exponent vector := by
  change (∑ᶠ _ : Unit, seed.coeff exponent vector) = _
  exact finsum_unique _

private theorem wordField_nil (D : LatticeData) (hu : IsUnit D.G.det)
    (seed : NativeField D hu) : wordField D hu seed [] = seed := by
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  rw [wordField_coefficient]
  change (∑ᶠ _ : Unit, seed.coeff exponent vector) = _
  exact finsum_unique _

private def probeSource : Carrier hyperbolic := Finsupp.single 0 1

private theorem probe_source_field :
    sourceField hyperbolic hyperbolic_unit probeSource = probeSeed := by
  change Finsupp.lsum ℂ (polynomialField hyperbolic hyperbolic_unit)
    (Finsupp.single 0 1) = _
  rw [Finsupp.lsum_single]
  have basis := (MvPolynomial.basisMonomials (Index hyperbolic) ℂ).constr_basis ℂ
    (fun monomial => chargedWordField hyperbolic hyperbolic_unit 0
      (occurrences hyperbolic monomial)) 0
  have polynomial : polynomialField hyperbolic hyperbolic_unit 0 1 =
      chargedWordField hyperbolic hyperbolic_unit 0 [] := by
    simpa [polynomialField, occurrences] using basis
  rw [polynomial, chargedWordField, wordField_nil]
  rfl

abbrev BoundData := { lattice : LatticeData // IsUnit lattice.G.det }
abbrev WordParameter := Σ data : BoundData,
  NativeField data.val data.property × List (Index data.val)
abbrev TermParameter := WordParameter × ℤ
abbrev WordEvaluation := Σ parameter : WordParameter,
  ActualTensor parameter.1.val parameter.1.property
abbrev SourceEvaluation := Σ data : BoundData,
  Carrier data.val × ActualTensor data.val data.property

namespace TermReadout

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  TermParameter
  (fun p => ActualTensor p.1.1.val p.1.1.property)
  (fun p => ModeTuple p.1.1.val p.1.2.2 → ActualTensor p.1.1.val p.1.1.property)

def actual : Realization signature := realize signature
  (fun _ p vector => flatTerm p.1.1.val p.1.1.property p.1.2.1 p.1.2.2 p.2 vector)
  (fun empty => nomatch empty)

def repeated : Realization signature := realize signature
  (fun _ _ vector _ => vector) (fun empty => nomatch empty)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨⟨⟨hyperbolic, hyperbolic_unit⟩, probeSeed, []⟩, 0⟩, 0, probeState, ?_⟩
  intro equality
  have coordinate := congrFun equality ()
  change probeSeed.coeff 0 0 = probeSeed.coeff 0 probeState at coordinate
  exact probe_leading (by simpa only [map_zero] using coordinate.symm)

private theorem repeated_not_finite :
    ¬ Function.HasFiniteSupport
      (fun _ : ModeTuple hyperbolic [((0 : Fin 2), 0)] => probeState) := by
  intro finite
  have support : Function.support
      (fun _ : ModeTuple hyperbolic [((0 : Fin 2), 0)] => probeState) = Set.univ := by
    ext modes
    simp [Function.mem_support, probeState_nonzero]
  change (Function.support _).Finite at finite
  rw [support] at finite
  change (Set.univ : Set (ℤ × Unit)).Finite at finite
  exact Set.infinite_univ finite

end TermReadout

namespace Factorization

abbrev Parameter := Σ p : WordParameter, ModeTuple p.1.val p.2.2
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun _ => ℤ) (fun p => Module.End ℂ (ActualTensor p.1.1.val p.1.1.property))

def actual : Realization signature := realize signature
  (fun _ p exponent => flatCoefficient p.1.1.val p.1.1.property p.1.2.1 p.1.2.2 p.2 exponent)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (seed : NativeField D hu)
    (word : List (Index D)) (modes : ModeTuple D word) (exponent : ℤ),
    readout.readout () ⟨⟨⟨D, hu⟩, seed, word⟩, modes⟩ exponent =
      leftAction D hu word modes *
        seed.coeff (exponent + 2 * modeSum D word modes + jetShift D word) *
          rightAction D hu word modes

theorem source_bridge : (type_of% (@flatCoefficient_factorization)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law hyperbolic hyperbolic_unit probeSeed [] () 0
  have value := congrArg
    (fun operator : Module.End ℂ (ActualTensor hyperbolic hyperbolic_unit) => operator probeState) bad
  exact probe_leading (by
    simpa [rejected, realize, leftAction, rightAction, modeSum, jetShift] using value.symm)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨⟨⟨hyperbolic, hyperbolic_unit⟩, probeSeed, []⟩, ()⟩, 0, -1, ?_⟩
  intro equality
  have value := congrArg
    (fun operator : Module.End ℂ (ActualTensor hyperbolic hyperbolic_unit) => operator probeState) equality
  change probeSeed.coeff 0 probeState = probeSeed.coeff (-1) probeState at value
  exact probe_leading (value.trans (probe_negative (-1) (by omega)))

def familyRegistration : Registration arena (type_of% (@flatCoefficient_factorization)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp flatCoefficient_factorization, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@flatCoefficient_factorization) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.flatCoefficient_factorization "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.Factorization.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Factorization

namespace PointwiseSupport

abbrev signature := TermReadout.signature
abbrev actual := TermReadout.actual
abbrev rejected := TermReadout.repeated

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (seed : NativeField D hu)
    (word : List (Index D)) (exponent : ℤ) (vector : ActualTensor D hu) (cutoff : ℕ)
    (bound : ∀ colour mode, (cutoff : ℤ) ≤ mode →
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode vector = 0),
    Function.support (readout.readout () ⟨⟨⟨D, hu⟩, seed, word⟩, exponent⟩ vector) ⊆
      modeBox D word
        (min (flatLower D hu seed word vector cutoff - exponent - jetShift D word) 0 -
          (word.length : ℤ) * cutoff) cutoff

theorem source_bridge : (type_of% (@flatTerm_support_bound)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨cutoff, bound⟩ :=
    LatticeHalfFock.tensor_current_truncation hyperbolic (ActualGround hyperbolic hyperbolic_unit) probeState
  have included := law hyperbolic hyperbolic_unit probeSeed [((0 : Fin 2), 0)] 0 probeState cutoff bound
  apply TermReadout.repeated_not_finite
  exact (modeBox hyperbolic [((0 : Fin 2), 0)]
    (min (flatLower hyperbolic hyperbolic_unit probeSeed [((0 : Fin 2), 0)] probeState cutoff -
      0 - jetShift hyperbolic [((0 : Fin 2), 0)]) 0 - cutoff) cutoff).finite_toSet.subset
        (by simpa [rejected, TermReadout.repeated, realize] using included)

def familyRegistration : Registration arena (type_of% (@flatTerm_support_bound)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp flatTerm_support_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := TermReadout.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@flatTerm_support_bound) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.flatTerm_support_bound "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.PointwiseSupport.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end PointwiseSupport

namespace PointwiseFinite

abbrev signature := TermReadout.signature
abbrev actual := TermReadout.actual
abbrev rejected := TermReadout.repeated

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (seed : NativeField D hu)
    (word : List (Index D)) (exponent : ℤ) (vector : ActualTensor D hu),
    Function.HasFiniteSupport (readout.readout () ⟨⟨⟨D, hu⟩, seed, word⟩, exponent⟩ vector)

theorem source_bridge : (type_of% (@flatTerm_finite)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  exact TermReadout.repeated_not_finite
    (law hyperbolic hyperbolic_unit probeSeed [((0 : Fin 2), 0)] 0 probeState)

def familyRegistration : Registration arena (type_of% (@flatTerm_finite)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp flatTerm_finite, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := TermReadout.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@flatTerm_finite) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.flatTerm_finite "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.PointwiseFinite.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end PointwiseFinite

namespace WordReadout

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  WordEvaluation (fun _ => ℤ)
  (fun p => ActualTensor p.1.1.val p.1.1.property)

def actual : Realization signature := realize signature
  (fun _ p exponent => wordCoefficient p.1.1.val p.1.1.property p.1.2.1 p.1.2.2 exponent p.2)
  (fun empty => nomatch empty)

def repeated : Realization signature := realize signature
  (fun _ p _ => p.2) (fun empty => nomatch empty)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨⟨⟨hyperbolic, hyperbolic_unit⟩, probeSeed, []⟩, probeState⟩, 0, -1, ?_⟩
  intro equality
  change wordCoefficient hyperbolic hyperbolic_unit probeSeed [] 0 probeState =
    wordCoefficient hyperbolic hyperbolic_unit probeSeed [] (-1) probeState at equality
  rw [wordCoefficient_nil, wordCoefficient_nil] at equality
  exact probe_leading (equality.trans (probe_negative (-1) (by omega)))

end WordReadout

namespace WordTruncation

abbrev signature := WordReadout.signature
abbrev actual := WordReadout.actual
abbrev rejected := WordReadout.repeated

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (seed : NativeField D hu)
    (word : List (Index D)) (vector : ActualTensor D hu),
    ∃ lower : ℤ, ∀ exponent : ℤ, exponent < lower →
      readout.readout () ⟨⟨⟨D, hu⟩, seed, word⟩, vector⟩ exponent = 0

theorem source_bridge : (type_of% (@wordCoefficient_lower_truncation)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨lower, below⟩ := law hyperbolic hyperbolic_unit probeSeed [] probeState
  exact probeState_nonzero (below (lower - 1) (by omega))

def familyRegistration : Registration arena (type_of% (@wordCoefficient_lower_truncation)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp wordCoefficient_lower_truncation, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := WordReadout.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@wordCoefficient_lower_truncation) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.wordCoefficient_lower_truncation "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.WordTruncation.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end WordTruncation

namespace WordFieldCoefficient

abbrev signature := TermReadout.signature
abbrev actual := TermReadout.actual

def rejected : Realization signature := realize signature
  (fun _ _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (seed : NativeField D hu)
    (word : List (Index D)) (exponent : ℤ) (vector : ActualTensor D hu),
    (wordField D hu seed word).coeff exponent vector =
      ∑ᶠ modes : ModeTuple D word,
        readout.readout () ⟨⟨⟨D, hu⟩, seed, word⟩, exponent⟩ vector modes

theorem source_bridge : (type_of% (@wordField_coefficient)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have zero := law hyperbolic hyperbolic_unit probeSeed [] 0 probeState
  exact probe_leading (by simpa [rejected, realize, wordField_nil] using zero)

def familyRegistration : Registration arena (type_of% (@wordField_coefficient)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp wordField_coefficient, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := TermReadout.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@wordField_coefficient) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.wordField_coefficient "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.WordFieldCoefficient.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "body", "fn"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end WordFieldCoefficient

namespace SourceReadout

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  SourceEvaluation (fun _ => ℤ)
  (fun p => ActualTensor p.1.val p.1.property)

def actual : Realization signature := realize signature
  (fun _ p exponent => (sourceField p.1.val p.1.property p.2.1).coeff exponent p.2.2)
  (fun empty => nomatch empty)

def repeated : Realization signature := realize signature
  (fun _ p _ => p.2.2) (fun empty => nomatch empty)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨⟨hyperbolic, hyperbolic_unit⟩, probeSource, probeState⟩, 0, -1, ?_⟩
  intro equality
  change (sourceField hyperbolic hyperbolic_unit probeSource).coeff 0 probeState =
    (sourceField hyperbolic hyperbolic_unit probeSource).coeff (-1) probeState at equality
  rw [probe_source_field] at equality
  exact probe_leading (equality.trans (probe_negative (-1) (by omega)))

end SourceReadout

namespace SourceCoefficient

abbrev signature := SourceReadout.signature
abbrev actual := SourceReadout.actual

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (source : Carrier D)
    (exponent : ℤ) (vector : ActualTensor D hu),
    readout.readout () ⟨⟨D, hu⟩, source, vector⟩ exponent =
      ∑ charge ∈ source.support,
        ∑ monomial ∈ ((MvPolynomial.basisMonomials (Index D) ℂ).repr (source charge)).support,
          ((MvPolynomial.basisMonomials (Index D) ℂ).repr (source charge) monomial) •
            ∑ᶠ modes : ModeTuple D (occurrences D monomial),
              flatTerm D hu (chargedField D hu charge) (occurrences D monomial)
                exponent vector modes

theorem source_bridge : (type_of% (@sourceField_coefficient)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law hyperbolic hyperbolic_unit probeSource 0 probeState
  have good := sourceField_coefficient hyperbolic hyperbolic_unit probeSource 0 probeState
  have zero : (sourceField hyperbolic hyperbolic_unit probeSource).coeff 0 probeState = 0 :=
    good.trans (by simpa [rejected, realize] using bad.symm)
  rw [probe_source_field] at zero
  exact probe_leading zero

def familyRegistration : Registration arena (type_of% (@sourceField_coefficient)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp sourceField_coefficient, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := SourceReadout.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sourceField_coefficient) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.sourceField_coefficient "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.SourceCoefficient.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
    definition := none
    coordinates := #[0, 1, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end SourceCoefficient

namespace SourceTruncation

abbrev signature := SourceReadout.signature
abbrev actual := SourceReadout.actual
abbrev rejected := SourceReadout.repeated

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (source : Carrier D)
    (vector : ActualTensor D hu),
    ∃ lower : ℤ, ∀ exponent : ℤ, exponent < lower →
      readout.readout () ⟨⟨D, hu⟩, source, vector⟩ exponent = 0

theorem source_bridge : (type_of% (@sourceField_lower_truncation)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨lower, below⟩ := law hyperbolic hyperbolic_unit probeSource probeState
  exact probeState_nonzero (below (lower - 1) (by omega))

def familyRegistration : Registration arena (type_of% (@sourceField_lower_truncation)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp sourceField_lower_truncation, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := SourceReadout.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sourceField_lower_truncation) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.sourceField_lower_truncation "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.SourceTruncation.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end SourceTruncation

namespace PolynomialInsertion

private def probeIndex : Index hyperbolic :=
  (⟨0, by change 0 < 2; decide⟩, 0)

abbrev Parameter := Σ data : BoundData, Charge data.val × Index data.val
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun p => Oscillator p.1.val)
  (fun p => NativeField p.1.val p.1.property)

def actual : Realization signature := realize signature
  (fun _ p polynomial => polynomialField p.1.val p.1.property p.2.1 polynomial)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ p _ => chargedField p.1.val p.1.property p.2.1)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (i : Index D) (p : Oscillator D),
    readout.readout () ⟨⟨D, hu⟩, q, i⟩ (MvPolynomial.X i * p) =
      singletonLinear D hu i (polynomialField D hu q p)

theorem source_bridge : (type_of% (@polynomialField_X_mul)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law hyperbolic hyperbolic_unit 0 probeIndex 0
  have badCoefficient := congrArg
    (fun F : NativeField hyperbolic hyperbolic_unit => F.coeff 0 probeState) bad
  exact probe_leading (by simpa [rejected, realize, probeSeed] using badCoefficient)

private theorem polynomial_one :
    polynomialField hyperbolic hyperbolic_unit 0 1 = probeSeed := by
  simpa only [sourceField, probeSource, Finsupp.lsum_single] using probe_source_field

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨⟨hyperbolic, hyperbolic_unit⟩, 0, probeIndex⟩, 0, 1, ?_⟩
  intro equality
  change polynomialField hyperbolic hyperbolic_unit 0 0 =
    polynomialField hyperbolic hyperbolic_unit 0 1 at equality
  rw [map_zero, polynomial_one] at equality
  exact probe_leading (by rw [← equality]; simp)

def familyRegistration : Registration arena (type_of% (@polynomialField_X_mul)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp polynomialField_X_mul, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@polynomialField_X_mul)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.polynomialField_X_mul "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.PolynomialInsertion.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end PolynomialInsertion

/- Faithful typed audit attempts for the newly exposed consumed APIs.  These
   exact source mirrors are not four-slot registrations; the missing
   realization/readout evidence is reported with this delivery. -/
abbrev sourceScope_singletonLinear_coefficient :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.singletonLinear_coefficient)
theorem source_actual_singletonLinear_coefficient : sourceScope_singletonLinear_coefficient :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.singletonLinear_coefficient

abbrev sourceScope_wordField_cons_singleton :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.wordField_cons_singleton)
theorem source_actual_wordField_cons_singleton : sourceScope_wordField_cons_singleton :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.wordField_cons_singleton

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
