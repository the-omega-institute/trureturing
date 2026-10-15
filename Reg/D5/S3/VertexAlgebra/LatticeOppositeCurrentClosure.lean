import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeOppositeCurrentClosure
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField LatticePositiveEnergy
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents LatticeSugawaraConformal
open LatticeSugawaraVirasoro LatticeSugawaraLocalNilpotence LatticeOppositeCoefficients
open LatticeOppositeCurrentClosure
open scoped VertexOperator

namespace Reg.D5.S3.VertexAlgebra.LatticeOppositeCurrentClosure

noncomputable section

structure Parameters where
  data : LatticeData
  matrix : Matrix (Fin data.rank) (Fin data.rank) ℂ
  leftInverse : matrix * gramComplex data = 1
  rightInverse : gramComplex data * matrix = 1
  current : Fin data.rank
  degree : ℕ
  weight : ℤ
  index : ℤ

abbrev signature : Signature where
  Params := Parameters
  State parameter := Carrier parameter.data × Carrier parameter.data
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Carrier parameter.data
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ parameter states =>
    oppositeCoeff parameter.data parameter.matrix (parameter.weight + parameter.degree + 1)
      (neutralMode parameter.data parameter.current (-(parameter.degree : ℤ) - 1) states.1)
      parameter.index states.2)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ parameter states => actual.readout () parameter states +
    carrierBasis parameter.data (0, 0)) (fun empty => nomatch empty)

def expected (parameter : Parameters) (states : Carrier parameter.data × Carrier parameter.data) :
    Carrier parameter.data :=
  -(∑ᶠ offset : ℕ, reversedFirstTerm parameter.data parameter.matrix parameter.current
      parameter.degree parameter.weight states.1 parameter.index states.2 offset) +
    (-1 : ℂ)^(parameter.degree + 1) •
      ∑ᶠ offset : ℕ, reversedSecondTerm parameter.data parameter.matrix parameter.current
        parameter.degree parameter.weight states.1 parameter.index states.2 offset

abbrev arena : Arena where
  signature := signature
  Law realization := ∀ (parameter : Parameters) (states : Carrier parameter.data × Carrier parameter.data),
    states.1 ∈ grade parameter.data parameter.weight →
      realization.readout () parameter states = expected parameter states

private abbrev rankOne : LatticeData where
  rank := 1
  G := fun _ _ => 2
  symmetric := by intros; rfl
  even_diagonal := by intro index; exact ⟨1, by decide⟩

private def oneParameters : Parameters where
  data := rankOne
  matrix := fun _ _ => (2 : ℂ)⁻¹
  leftInverse := by ext first second; fin_cases first; fin_cases second; norm_num [gramComplex, Matrix.mul_apply, rankOne]
  rightInverse := by ext first second; fin_cases first; fin_cases second; norm_num [gramComplex, Matrix.mul_apply, rankOne]
  current := 0
  degree := 0
  weight := 0
  index := 0

private theorem ground_nonzero (data : LatticeData) : carrierBasis data (0, 0) ≠ 0 := by
  intro equality
  have coefficient := congrArg (fun state : Carrier data => carrierCoeffEquiv data state (0, 0)) equality
  norm_num only [carrierCoeffEquiv_basis, map_zero, Finsupp.single_eq_same, Finsupp.zero_apply] at coefficient

private theorem actualLaw : arena.Law actual := by
  intro parameter states homogeneous
  exact opposite_current_insertion parameter.data parameter.matrix parameter.leftInverse
    parameter.rightInverse parameter.current parameter.degree states.1 states.2
    parameter.weight parameter.index homogeneous

private theorem rejectedFails : ¬ arena.Law rejected := by
  intro law
  have actualZero := actualLaw oneParameters (0, 0) (Submodule.zero_mem _)
  have rejectedZero := law oneParameters (0, 0) (Submodule.zero_mem _)
  change actual.readout () oneParameters (0, 0) + carrierBasis oneParameters.data (0, 0) = _ at rejectedZero
  rw [actualZero, add_eq_left] at rejectedZero
  exact ground_nonzero oneParameters.data rejectedZero

private def tested : Carrier rankOne := Finsupp.single (fun _ => 1) 1

set_option maxHeartbeats 2000000 in
private theorem actualDependence : actual.readout () oneParameters (vacuum rankOne, tested) ≠
    actual.readout () oneParameters (vacuum rankOne, 0) := by
  let insertion := neutralMode rankOne 0 (-1) (vacuum rankOne)
  have basisInsertion : insertion = carrierBasis rankOne (0, Finsupp.single (0, 0) 1) := by
    simp [insertion, neutralMode, neutralPolynomialMode, vacuum, carrierBasis_apply, MvPolynomial.X]
  have bound : oscillatorBound rankOne insertion = 1 := by
    rw [basisInsertion]
    unfold oscillatorBound
    rw [carrierCoeffEquiv_basis]
    simp [oscillatorEnergy, Finsupp.weight_single]
  have lowering : sugawaraMode rankOne oneParameters.matrix 1 insertion = 0 := by
    have commutator := congrArg (fun operator : Module.End ℂ (Carrier rankOne) => operator (vacuum rankOne))
      (sugawaraMode_current_commutator rankOne oneParameters.matrix
        oneParameters.leftInverse oneParameters.rightInverse 0 1 (-1))
    simp only [insertion, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      show sugawaraMode rankOne oneParameters.matrix 1 (vacuum rankOne) = 0 from
        sugawaraMode_ground_positive rankOne oneParameters.matrix 0 1 (by omega),
      map_zero, sub_zero, Int.cast_neg, Int.cast_one, neg_neg, one_smul, add_neg_cancel] at commutator
    rw [vacuum, neutralMode_zero_single] at commutator
    have scalarZero : chargeScalar rankOne 0 0 = 0 := by simp [chargeScalar, bilinear]
    rw [scalarZero, zero_smul] at commutator
    exact commutator
  have modes : ((Y rankOne insertion)[[0]]) = neutralMode rankOne 0 0 := by
    rw [show insertion = ((neutralField rankOne 0)[[-1]]) (vacuum rankOne) by rw [neutralField_ncoeff],
      stateField_current, neutralField_ncoeff]
  have coefficient : oppositeCoeff rankOne oneParameters.matrix 1 insertion 0 = -neutralMode rankOne 0 0 := by
    rw [opposite_cutoff rankOne oneParameters.matrix 1 insertion 0 2 (by rw [bound]; decide)]
    simp [Finset.sum_range_succ, oppositeTerm, lowering, modes, paritySign]
  change oppositeCoeff rankOne oneParameters.matrix 1 insertion 0 tested ≠
    oppositeCoeff rankOne oneParameters.matrix 1 insertion 0 0
  rw [coefficient, map_zero]
  simp only [LinearMap.neg_apply]
  rw [tested, neutralMode_zero_single]
  have testedNonzero : tested ≠ 0 := by
    intro equality
    have impossible := congrArg (fun state : Carrier rankOne => state (fun _ => 1)) equality
    norm_num [tested] at impossible
  simpa [chargeScalar, bilinear, rankOne, unitCharge] using testedNonzero

abbrev SourceStatement := ∀ (data : LatticeData)
    (matrix : Matrix (Fin data.rank) (Fin data.rank) ℂ)
    (leftInverse : matrix * gramComplex data = 1) (rightInverse : gramComplex data * matrix = 1)
    (current : Fin data.rank) (degree : ℕ) (state tested : Carrier data)
    (weight index : ℤ), state ∈ grade data weight →
      oppositeCoeff data matrix (weight + degree + 1)
        (neutralMode data current (-(degree : ℤ) - 1) state) index tested =
        -(∑ᶠ offset : ℕ, reversedFirstTerm data matrix current degree weight state index tested offset) +
          (-1 : ℂ)^(degree + 1) •
            ∑ᶠ offset : ℕ, reversedSecondTerm data matrix current degree weight state index tested offset

private theorem sourceBridge : SourceStatement ↔ arena.Law actual := by
  constructor
  · intro source parameter states homogeneous
    exact source parameter.data parameter.matrix parameter.leftInverse parameter.rightInverse
      parameter.current parameter.degree states.1 states.2 parameter.weight parameter.index homogeneous
  · intro law data matrix leftInverse rightInverse current degree state tested weight index homogeneous
    exact law ⟨data, matrix, leftInverse, rightInverse, current, degree, weight, index⟩
      (state, tested) homogeneous

def sourceWitness : Registration arena SourceStatement where
  actual := actual
  bridge := sourceBridge
  variation := ⟨actualLaw, rejected, rejectedFails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejectedFails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    exact ⟨oneParameters, (vacuum rankOne, tested), (vacuum rankOne, 0), actualDependence⟩

def opposite_current_insertion_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.LatticeOppositeCurrentClosure.opposite_current_insertion)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeOppositeCurrentClosure.opposite_current_insertion.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeOppositeCurrentClosure.sourceWitness
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceWitness⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ parameter states =>
      oppositeCoeff parameter.data parameter.matrix (parameter.weight + parameter.degree + 1)
        (neutralMode parameter.data parameter.current (-(parameter.degree : ℤ) - 1) states.1)
        parameter.index states.2)
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeOppositeCurrentClosure
    definition := none
    coordinates := #[0, 1, 4, 5, 8, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[
    { name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }]

end
end Reg.D5.S3.VertexAlgebra.LatticeOppositeCurrentClosure
