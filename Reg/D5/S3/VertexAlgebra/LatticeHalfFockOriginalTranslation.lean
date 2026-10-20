import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation

/-! Faithful dependent-family audit retaining the actual determinant witness and carrier. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
open LatticeHalfFockCorrectedField LatticeHalfFockFiniteCorrection
open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators TensorProduct

noncomputable section

def hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro first second; fin_cases first <;> fin_cases second <;> rfl
  even_diagonal := by intro axis; fin_cases axis <;> exact ⟨0, rfl⟩

theorem hyperbolic_unit : IsUnit hyperbolic.G.det := by
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

def probeState : ActualTensor hyperbolic hyperbolic_unit :=
  (1 : Oscillator hyperbolic) ⊗ₜ[ℂ] probeGround

theorem probe_leading :
    chargedCoefficient hyperbolic hyperbolic_unit 0 0 probeState ≠ 0 := by
  simpa [probeState, chargeNorm, bilinear] using
    charged_ground_leading hyperbolic hyperbolic_unit 0 probeGround probeGround_nonzero

private theorem probeState_nonzero : probeState ≠ 0 := by
  intro zero
  apply probe_leading
  rw [zero, map_zero]


def probeSource : Carrier hyperbolic := Finsupp.single 0 1

theorem probe_polynomial_one :
    polynomialField hyperbolic hyperbolic_unit 0 1 =
      chargedField hyperbolic hyperbolic_unit 0 := by
  have basis := (MvPolynomial.basisMonomials (Index hyperbolic) ℂ).constr_basis ℂ
    (fun d => chargedWordField hyperbolic hyperbolic_unit 0 (occurrences hyperbolic d)) 0
  have evaluated : polynomialField hyperbolic hyperbolic_unit 0 1 =
      wordField hyperbolic hyperbolic_unit (chargedField hyperbolic hyperbolic_unit 0) [] := by
    simpa [polynomialField, occurrences, chargedWordField] using basis
  rw [evaluated]
  apply HVertexOperator.coeff_inj
  funext e
  apply LinearMap.ext
  intro v
  rw [wordField_coefficient]
  exact finsum_unique _

theorem probe_source_field :
    correctedField hyperbolic hyperbolic_unit probeSource =
      chargedField hyperbolic hyperbolic_unit 0 := by
  have corr : Corr hyperbolic 0 1 = Finsupp.single 0 1 := by
    have h := Corr_monomial_enumeration hyperbolic 0 0 []
      (by simp [LatticeAllStateField.occurrences])
    have h' : Corr hyperbolic 0 1 =
        shiftCoefficients hyperbolic (1 : Polynomial (Oscillator hyperbolic)) := by
      simpa [correctionWord] using h
    rw [h']
    apply Finsupp.ext
    intro n
    change (1 : Polynomial (Oscillator hyperbolic)).coeff n = (Finsupp.single 0 1) n
    simp [Polynomial.coeff_one, Finsupp.single_apply, eq_comm]
  simp only [correctedField, probeSource, Finsupp.lsum_single,
    correctedPolynomial, LinearMap.comp_apply]
  change (Finsupp.lsum ℂ (fun s : ℕ =>
    (shiftField hyperbolic hyperbolic_unit s).comp
      (polynomialField hyperbolic hyperbolic_unit 0))) (Corr hyperbolic 0 1) = _
  rw [corr, Finsupp.lsum_single]
  change shiftField hyperbolic hyperbolic_unit 0
    (polynomialField hyperbolic hyperbolic_unit 0 1) = _
  rw [probe_polynomial_one]
  apply LinearMap.ext
  intro v
  change (HahnSeries.single (-2 * (0 : ℤ)) (1 : ℂ)) •
    (chargedField hyperbolic hyperbolic_unit 0 v) = _
  simp

abbrev BoundData := { lattice : LatticeData // IsUnit lattice.G.det }
abbrev Parameter := Σ data : BoundData, Carrier data.val × ℤ
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun p => ActualTensor p.1.val p.1.property)
  (fun p => ActualTensor p.1.val p.1.property)

def actual : Realization signature := realize signature
  (fun _ p v => (correctedField p.1.val p.1.property p.2.1).coeff (p.2.2 + 2) v)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ _ v => v) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (source : Carrier D) (e : ℤ) (v : ActualTensor D hu),
    (correctedField D hu (LatticeSugawaraConformal.translation D source)).coeff e v =
      (((e + 2 : ℤ) : ℂ) / 2) • readout.readout () ⟨⟨D, hu⟩, source, e⟩ v

theorem source_bridge :
    (type_of% (@correctedField_translation_physical)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law hyperbolic hyperbolic_unit 0 0 probeState
  exact probeState_nonzero (by simpa [rejected, realize] using bad.symm)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨⟨hyperbolic, hyperbolic_unit⟩, probeSource, -2⟩, 0, probeState, ?_⟩
  intro equality
  change (correctedField hyperbolic hyperbolic_unit probeSource).coeff 0 0 =
    (correctedField hyperbolic hyperbolic_unit probeSource).coeff 0 probeState at equality
  rw [probe_source_field] at equality
  exact probe_leading (by simpa only [map_zero, chargedField, HVertexOperator.coeff_of_coeff] using equality.symm)

def familyRegistration : Registration arena (type_of% (@correctedField_translation_physical)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp correctedField_translation_physical, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@correctedField_translation_physical) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.correctedField_translation_physical "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

namespace ShiftCoefficient
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  ℕ (fun _ => ℤ) (fun _ => ℤ)
def actual : Realization signature := realize signature
  (fun _ s e => e + 2 * (s : ℤ)) (fun empty => nomatch empty)
def rejected : Realization signature := realize signature
  (fun _ _ e => e) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℕ) (A : NativeField D hu) (e : ℤ),
    (shiftField D hu s A).coeff e = A.coeff (readout.readout () s e)
theorem source_bridge : (type_of% (@shiftField_coefficient_public)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law hyperbolic hyperbolic_unit 1
    (chargedField hyperbolic hyperbolic_unit 0) (-2)
  rw [shiftField_coefficient_public] at bad
  have value := LinearMap.congr_fun bad probeState
  have zero : chargedCoefficient hyperbolic hyperbolic_unit 0 (-2) probeState = 0 := by
    apply charged_polynomial_lower_bound
    norm_num [chargeNorm, bilinear, nativeOddWeightedDegree, MvPolynomial.weightedTotalDegree]
  have reduced : chargedCoefficient hyperbolic hyperbolic_unit 0 0 probeState =
      chargedCoefficient hyperbolic hyperbolic_unit 0 (-2) probeState := by
    simpa only [rejected, realize, HVertexOperator.coeff_of_coeff, chargedField,
      Int.natCast_one, mul_one, neg_add_cancel] using value
  exact probe_leading (reduced.trans zero)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨0, 0, 1, ?_⟩
  norm_num [actual, realize]

def familyRegistration : Registration arena (type_of% (@shiftField_coefficient_public)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp shiftField_coefficient_public, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@shiftField_coefficient_public) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField.shiftField_coefficient_public "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.ShiftCoefficient.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end ShiftCoefficient

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
