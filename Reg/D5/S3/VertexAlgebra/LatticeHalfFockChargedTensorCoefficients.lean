import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators TensorProduct

noncomputable section

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

private def probeVector : ActualGround hyperbolic hyperbolic_unit := fun _ => 1

private theorem probe_vector_nonzero : probeVector ≠ 0 := by
  intro equality
  have coordinate := congrFun equality (0 : Half (groundRank hyperbolic hyperbolic_unit))
  exact one_ne_zero (show (1 : ℂ) = 0 from coordinate)

private theorem probe_leading :
    chargedCoefficient hyperbolic hyperbolic_unit 0 0
      ((1 : Oscillator hyperbolic) ⊗ₜ[ℂ] probeVector) ≠ 0 := by
  simpa [chargeNorm, bilinear] using
    charged_ground_leading hyperbolic hyperbolic_unit 0 probeVector probe_vector_nonzero

namespace TermReadout

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ lattice : LatticeData, Σ _ : Charge lattice, ℤ)
  (fun parameter => Oscillator parameter.1)
  (fun parameter => ℕ → Oscillator parameter.1)

def actual : Realization signature := realize signature
  (fun _ parameter polynomial =>
    oscillatorTerm parameter.1 parameter.2.1 parameter.2.2 polynomial)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ _ _ _ => 1) (fun empty => nomatch empty)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨hyperbolic, 0, 0⟩, 0, 1, ?_⟩
  intro equality
  have coordinate := congrFun equality 0
  have impossible : (0 : Oscillator hyperbolic) = 1 := by
    simpa [actual, realize, oscillatorTerm, halfTranslatedPolynomial,
      chargeNorm, bilinear, halfCreationCoeff, exponential_constant] using coordinate
  exact zero_ne_one impossible

end TermReadout

namespace NormReadout

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  LatticeData Charge (fun _ => ℤ)

def actual : Realization signature := realize signature
  (fun _ lattice charge => chargeNorm lattice charge) (fun empty => nomatch empty)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨hyperbolic, 0, 1, ?_⟩
  change chargeNorm hyperbolic 0 ≠ chargeNorm hyperbolic 1
  norm_num [chargeNorm, bilinear, hyperbolic, Fin.sum_univ_two]
  change (0 : ℤ) ≠ ∑ first : Fin 2, ∑ second : Fin 2,
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) first second
  norm_num [Fin.sum_univ_two]

end NormReadout

namespace TermSupport

abbrev signature := TermReadout.signature
abbrev actual := TermReadout.actual
abbrev rejected := TermReadout.rejected

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (charge : Charge lattice) (exponent : ℤ)
    (polynomial : Oscillator lattice),
    Function.support (readout.readout () ⟨lattice, charge, exponent⟩ polynomial) ⊆
      (halfTranslatedPolynomial lattice charge polynomial).support

theorem source_bridge : (type_of% (@term_support)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have included := law hyperbolic 0 0 0
  have member : (0 : ℕ) ∈ Function.support
      (rejected.readout () ⟨hyperbolic, 0, 0⟩ 0) := by
    simp [rejected, TermReadout.rejected, realize]
  have impossible := included member
  simpa [halfTranslatedPolynomial] using impossible

def familyRegistration : Registration arena (type_of% (@term_support)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp term_support, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := TermReadout.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@term_support) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients.term_support "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients.TermSupport.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end TermSupport

namespace TermFiniteSupport

abbrev signature := TermReadout.signature
abbrev actual := TermReadout.actual
abbrev rejected := TermReadout.rejected

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (charge : Charge lattice) (exponent : ℤ)
    (polynomial : Oscillator lattice),
    Function.HasFiniteSupport (readout.readout () ⟨lattice, charge, exponent⟩ polynomial)

theorem source_bridge : (type_of% (@charged_term_finite_support)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have finite := law hyperbolic 0 0 0
  have support : Function.support (fun _ : ℕ => (1 : Oscillator hyperbolic)) = Set.univ := by
    ext degree
    simp
  change (Function.support (fun _ : ℕ => (1 : Oscillator hyperbolic))).Finite at finite
  rw [support] at finite
  exact Set.infinite_univ finite

def familyRegistration : Registration arena (type_of% (@charged_term_finite_support)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp charged_term_finite_support, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := TermReadout.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@charged_term_finite_support) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients.charged_term_finite_support "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients.TermFiniteSupport.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end TermFiniteSupport

namespace PolynomialLowerBound

abbrev signature := NormReadout.signature
abbrev actual := NormReadout.actual

def rejected : Realization signature := realize signature
  (fun _ _ _ => -1) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (hu : IsUnit lattice.G.det)
    (charge : Charge lattice) (polynomial : Oscillator lattice) (vector : ActualGround lattice hu)
    (exponent : ℤ)
    (lower : exponent < -readout.readout () lattice charge - nativeOddWeightedDegree lattice polynomial),
    chargedCoefficient lattice hu charge exponent (polynomial ⊗ₜ[ℂ] vector) = 0

theorem source_bridge : (type_of% (@charged_polynomial_lower_bound)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have lower : (0 : ℤ) < -rejected.readout () hyperbolic 0 -
      nativeOddWeightedDegree hyperbolic (1 : Oscillator hyperbolic) := by
    norm_num [rejected, realize, nativeOddWeightedDegree, MvPolynomial.weightedTotalDegree]
  exact probe_leading (law hyperbolic hyperbolic_unit 0 1 probeVector 0 lower)

def familyRegistration : Registration arena (type_of% (@charged_polynomial_lower_bound)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp charged_polynomial_lower_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := NormReadout.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@charged_polynomial_lower_bound) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients.charged_polynomial_lower_bound "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients.PolynomialLowerBound.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "arg", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end PolynomialLowerBound

namespace VacuumCoefficient

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  LatticeData Charge (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ lattice charge => chargeScalar lattice charge) (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (hu : IsUnit lattice.G.det)
    (charge : Charge lattice) (exponent : ℤ) (vector : ActualGround lattice hu),
    chargedCoefficient lattice hu charge exponent ((1 : Oscillator lattice) ⊗ₜ[ℂ] vector) =
      readout.readout () lattice charge •
        (halfCreationCoeff lattice charge (exponent + chargeNorm lattice charge) ⊗ₜ[ℂ]
          groundAction lattice hu charge vector)

theorem source_bridge : (type_of% (@charged_vacuum_coefficient)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  apply probe_leading
  simpa [rejected, realize] using law hyperbolic hyperbolic_unit 0 0 probeVector

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨hyperbolic, 0, 1, ?_⟩
  change chargeScalar hyperbolic 0 ≠ chargeScalar hyperbolic 1
  norm_num [chargeScalar, chargeNorm, bilinear, hyperbolic, Fin.sum_univ_two]
  change (2 : ℂ) ^ (∑ first : Fin 2, ∑ second : Fin 2,
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) first second) ≠ 1
  norm_num [Fin.sum_univ_two]

def familyRegistration : Registration arena (type_of% (@charged_vacuum_coefficient)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp charged_vacuum_coefficient, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@charged_vacuum_coefficient) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients.charged_vacuum_coefficient "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients.VacuumCoefficient.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end VacuumCoefficient

namespace GroundLeading

abbrev signature := NormReadout.signature
abbrev actual := NormReadout.actual

def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (hu : IsUnit lattice.G.det)
    (charge : Charge lattice) (vector : ActualGround lattice hu) (nonzero : vector ≠ 0),
    chargedCoefficient lattice hu charge (-readout.readout () lattice charge)
      ((1 : Oscillator lattice) ⊗ₜ[ℂ] vector) ≠ 0

theorem source_bridge : (type_of% (@charged_ground_leading)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have nonzero := law hyperbolic hyperbolic_unit 0 probeVector probe_vector_nonzero
  change chargedCoefficient hyperbolic hyperbolic_unit 0 (-1)
    ((1 : Oscillator hyperbolic) ⊗ₜ[ℂ] probeVector) ≠ 0 at nonzero
  have lower : (-1 : ℤ) < -chargeNorm hyperbolic 0 -
      nativeOddWeightedDegree hyperbolic (1 : Oscillator hyperbolic) := by
    norm_num [chargeNorm, bilinear, nativeOddWeightedDegree, MvPolynomial.weightedTotalDegree]
  exact nonzero (charged_polynomial_lower_bound hyperbolic hyperbolic_unit
    0 1 probeVector (-1) lower)

def familyRegistration : Registration arena (type_of% (@charged_ground_leading)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp charged_ground_leading, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := NormReadout.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@charged_ground_leading) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients.charged_ground_leading "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients.GroundLeading.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end GroundLeading

namespace TensorCurrentWard

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ lattice : LatticeData, Fin lattice.rank)
  (fun parameter => Charge parameter.1) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ parameter charge => (bilinear parameter.1 (unitCharge parameter.1 parameter.2) charge : ℂ))
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (hu : IsUnit lattice.G.det)
    (colour : Fin lattice.rank) (charge : Charge lattice) (mode exponent : ℤ),
    _root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent
        lattice (ActualGround lattice hu) colour mode * chargedCoefficient lattice hu charge exponent -
      chargedCoefficient lattice hu charge exponent *
        _root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent
          lattice (ActualGround lattice hu) colour mode =
      readout.readout () ⟨lattice, colour⟩ charge •
        chargedCoefficient lattice hu charge (exponent - (2 * mode + 1))

theorem source_bridge : (type_of% (@charged_tensor_current_ward)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law hyperbolic hyperbolic_unit (0 : Fin 2) 0 0 1
  have good := charged_tensor_current_ward hyperbolic hyperbolic_unit (0 : Fin 2) 0 0 1
  have zero :
      _root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent
          hyperbolic (ActualGround hyperbolic hyperbolic_unit) (0 : Fin 2) 0 *
          chargedCoefficient hyperbolic hyperbolic_unit 0 1 -
        chargedCoefficient hyperbolic hyperbolic_unit 0 1 *
          _root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent
            hyperbolic (ActualGround hyperbolic hyperbolic_unit) (0 : Fin 2) 0 = 0 := by
    simpa [bilinear] using good
  rw [zero] at bad
  have coefficient_zero : chargedCoefficient hyperbolic hyperbolic_unit 0 0 = 0 := by
    simpa [rejected, realize] using bad.symm
  have value := congrArg (fun operator : Module.End ℂ (ActualTensor hyperbolic hyperbolic_unit) =>
    operator ((1 : Oscillator hyperbolic) ⊗ₜ[ℂ] probeVector)) coefficient_zero
  exact probe_leading (by simpa using value)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨hyperbolic, (0 : Fin 2)⟩, 0, unitCharge hyperbolic (1 : Fin 2), ?_⟩
  change (bilinear hyperbolic (unitCharge hyperbolic (0 : Fin 2)) 0 : ℂ) ≠
    (bilinear hyperbolic (unitCharge hyperbolic (0 : Fin 2))
      (unitCharge hyperbolic (1 : Fin 2)) : ℂ)
  norm_num [bilinear, unitCharge, hyperbolic, Fin.sum_univ_two]
  change (0 : ℂ) ≠ ∑ first : Fin 2, ∑ second : Fin 2,
    if second = 1 then
      if first = 0 then
        ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) first second : ℂ)
      else 0
    else 0
  norm_num [Fin.sum_univ_two]

def familyRegistration : Registration arena (type_of% (@charged_tensor_current_ward)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp charged_tensor_current_ward, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@charged_tensor_current_ward) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients.charged_tensor_current_ward "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients.TensorCurrentWard.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end TensorCurrentWard

end

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients

/- Exact source-type evidence; the four-slot audit is unfinished. -/
abbrev sourceScope_oscillator_coefficient_X_mul :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients.oscillator_coefficient_X_mul)
theorem source_actual_oscillator_coefficient_X_mul : sourceScope_oscillator_coefficient_X_mul :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients.oscillator_coefficient_X_mul

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
