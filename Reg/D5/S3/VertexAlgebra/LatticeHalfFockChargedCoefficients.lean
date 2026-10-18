import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

private def probeLattice : LatticeData where
  rank := 1
  G := fun _ _ => 2
  symmetric := by intros; rfl
  even_diagonal := by intro; exact ⟨1, rfl⟩

private def probeColour : Fin probeLattice.rank := ⟨0, by decide⟩

namespace ExponentialDerivative

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature LatticeData
  (fun lattice => PowerSeries (Oscillator lattice))
  (fun lattice => PowerSeries (Oscillator lattice))

def actual : Realization signature := realize signature
  (fun _ lattice series => PowerSeries.derivative series)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ lattice series => PowerSeries.derivative series + 1)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (charge : Charge lattice),
    readout.readout () lattice (halfCreationExponential lattice charge) =
      halfCreationExponential lattice charge *
        PowerSeries.derivative (halfCreationSeries lattice charge)

theorem source_bridge : (type_of% (@exponential_derivative)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have contradiction := law probeLattice 0
  change PowerSeries.derivative (halfCreationExponential probeLattice 0) + 1 =
    halfCreationExponential probeLattice 0 *
      PowerSeries.derivative (halfCreationSeries probeLattice 0) at contradiction
  rw [exponential_derivative] at contradiction
  have impossible : (1 : PowerSeries (Oscillator probeLattice)) = 0 := by
    simpa only [add_eq_left] using contradiction
  exact one_ne_zero impossible

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨probeLattice, 0, PowerSeries.X, by simp [actual, realize]⟩

def familyRegistration : Registration arena (type_of% (@exponential_derivative)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp exponential_derivative, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exponential_derivative) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients.exponential_derivative "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients.ExponentialDerivative.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end ExponentialDerivative

namespace ExponentialConstant

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature LatticeData
  (fun lattice => PowerSeries (Oscillator lattice)) (fun lattice => Oscillator lattice)

def actual : Realization signature := realize signature
  (fun _ _ series => PowerSeries.coeff 0 series) (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (charge : Charge lattice),
    readout.readout () lattice (halfCreationExponential lattice charge) = 1

theorem source_bridge : (type_of% (@exponential_constant)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have contradiction := law probeLattice 0
  exact zero_ne_one (show (0 : Oscillator probeLattice) = 1 from contradiction)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨probeLattice, 0, 1, by simp [actual, realize]⟩

def familyRegistration : Registration arena (type_of% (@exponential_constant)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp exponential_constant, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exponential_constant) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients.exponential_constant "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients.ExponentialConstant.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end ExponentialConstant

namespace SeriesDerivativeCoefficient

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ lattice : LatticeData, ℕ)
  (fun parameter => PowerSeries (Oscillator parameter.1))
  (fun parameter => Oscillator parameter.1)

def actual : Realization signature := realize signature
  (fun _ parameter series => PowerSeries.coeff parameter.2 series)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ parameter series => PowerSeries.coeff parameter.2 series + 1)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (charge : Charge lattice) (degree : ℕ),
    readout.readout () ⟨lattice, degree⟩
        (PowerSeries.derivative (halfCreationSeries lattice charge)) =
      if degree % 2 = 0 then
        (2 : ℂ) • ∑ colour : Fin lattice.rank,
          (charge colour : ℂ) • (MvPolynomial.X (colour, degree / 2) : Oscillator lattice)
      else 0

theorem source_bridge : (type_of% (@series_derivative_coeff)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have contradiction := law probeLattice 0 0
  change PowerSeries.coeff 0
      (PowerSeries.derivative (halfCreationSeries probeLattice 0)) + 1 =
    (if (0 : ℕ) % 2 = 0 then
      (2 : ℂ) • ∑ colour : Fin probeLattice.rank,
        ((0 : Charge probeLattice) colour : ℂ) •
          (MvPolynomial.X (colour, 0 / 2) : Oscillator probeLattice)
    else 0) at contradiction
  rw [series_derivative_coeff] at contradiction
  have impossible : (1 : Oscillator probeLattice) = 0 := by
    simpa only [add_eq_left] using contradiction
  exact one_ne_zero impossible

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨⟨probeLattice, 0⟩, 0, 1, by simp [actual, realize]⟩

def familyRegistration : Registration arena (type_of% (@series_derivative_coeff)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp series_derivative_coeff, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@series_derivative_coeff) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients.series_derivative_coeff "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients.SeriesDerivativeCoefficient.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end SeriesDerivativeCoefficient

namespace CreationGrading

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ lattice : LatticeData, Charge lattice)
  (fun _ => ℤ) (fun parameter => Oscillator parameter.1)

def actual : Realization signature := realize signature
  (fun _ parameter degree => halfCreationCoeff parameter.1 parameter.2 degree)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => 1)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (charge : Charge lattice) (degree : ℤ),
    MvPolynomial.IsWeightedHomogeneous (omega lattice)
      (readout.readout () ⟨lattice, charge⟩ degree) degree.toNat

theorem source_bridge : (type_of% (@half_creation_coefficient_grading)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have homogeneous := law probeLattice 0 1
  change MvPolynomial.IsWeightedHomogeneous (omega probeLattice)
    (1 : Oscillator probeLattice) (1 : ℕ) at homogeneous
  exact Nat.one_ne_zero (MvPolynomial.IsWeightedHomogeneous.inj_right
    (one_ne_zero : (1 : Oscillator probeLattice) ≠ 0) homogeneous
    (MvPolynomial.isWeightedHomogeneous_one ℂ (omega probeLattice)))

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨probeLattice, 0⟩, -1, 0, ?_⟩
  simp [actual, realize, halfCreationCoeff, exponential_constant]

def familyRegistration : Registration arena (type_of% (@half_creation_coefficient_grading)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp half_creation_coefficient_grading, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@half_creation_coefficient_grading) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients.half_creation_coefficient_grading "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients.CreationGrading.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end CreationGrading

namespace CreationTransport

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ lattice : LatticeData, ℕ)
  (fun parameter => Polynomial (Oscillator parameter.1))
  (fun parameter => Oscillator parameter.1)

def actual : Realization signature := realize signature
  (fun _ parameter polynomial => polynomial.coeff parameter.2)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (left right : Charge lattice)
    (degree : ℤ) (translatedDegree : ℕ),
    readout.readout () ⟨lattice, translatedDegree⟩
        (halfTranslatedPolynomial lattice left (halfCreationCoeff lattice right degree)) =
      (PowerSeries.coeff translatedDegree (halfContraction lattice left right)) •
        halfCreationCoeff lattice right (degree - translatedDegree)

theorem source_bridge : (type_of% (@half_creation_coefficient_transport)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have contradiction := law probeLattice 0 0 0 0
  have constant : PowerSeries.coeff 0 (halfContraction probeLattice 0 0) = 1 := by
    simp [halfContraction, PowerSeries.coeff_mul, PowerSeries.coeff_rescale,
      PowerSeries.binomialSeries_coeff]
  change (0 : Oscillator probeLattice) =
    (PowerSeries.coeff 0 (halfContraction probeLattice 0 0)) •
      halfCreationCoeff probeLattice 0 (0 - (0 : ℕ)) at contradiction
  rw [constant] at contradiction
  simpa [halfCreationCoeff, exponential_constant] using contradiction

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨⟨probeLattice, 0⟩, 0, 1, by simp [actual, realize]⟩

def familyRegistration : Registration arena (type_of% (@half_creation_coefficient_transport)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp half_creation_coefficient_transport, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@half_creation_coefficient_transport) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients.half_creation_coefficient_transport "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients.CreationTransport.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end CreationTransport

namespace AnnihilationCreation

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ lattice : LatticeData, Σ _ : Fin lattice.rank, ℕ)
  (fun parameter => Oscillator parameter.1) (fun parameter => Oscillator parameter.1)

def actual : Realization signature := realize signature
  (fun _ parameter polynomial =>
    _root_.D5.S3.VertexAlgebra.LatticeActualAnnihilation.annihilate
      parameter.1 parameter.2.1 parameter.2.2 polynomial)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => 1)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (colour : Fin lattice.rank)
    (mode : ℕ) (charge : Charge lattice) (degree : ℤ),
    readout.readout () ⟨lattice, colour, mode⟩ (halfCreationCoeff lattice charge degree) =
      ((2 / (2 * mode + 1 : ℂ)) * (bilinear lattice (unitCharge lattice colour) charge : ℂ)) •
        halfCreationCoeff lattice charge (degree - (2 * mode + 1 : ℕ))

theorem source_bridge : (type_of% (@half_annihilation_creation)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have contradiction := law probeLattice probeColour 0 0 (-1)
  norm_num [rejected, realize, halfCreationCoeff] at contradiction

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨probeLattice, probeColour, 0⟩, 0, MvPolynomial.X (probeColour, 0), ?_⟩
  change _root_.D5.S3.VertexAlgebra.LatticeActualAnnihilation.annihilate
      probeLattice probeColour 0 0 ≠
    _root_.D5.S3.VertexAlgebra.LatticeActualAnnihilation.annihilate
      probeLattice probeColour 0 (MvPolynomial.X (probeColour, 0))
  rw [map_zero, _root_.D5.S3.VertexAlgebra.LatticeActualAnnihilation.annihilate_X]
  norm_num [probeLattice, Algebra.smul_def]
  change (0 : Oscillator probeLattice) ≠ 2
  norm_num

def familyRegistration : Registration arena (type_of% (@half_annihilation_creation)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp half_annihilation_creation, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@half_annihilation_creation) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients.half_annihilation_creation "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients.AnnihilationCreation.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end AnnihilationCreation

namespace TranslatedDerivation

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ lattice : LatticeData, Charge lattice)
  (fun parameter => Oscillator parameter.1)
  (fun parameter => Polynomial (Oscillator parameter.1))

def actual : Realization signature := realize signature
  (fun _ parameter polynomial => halfTranslatedPolynomial parameter.1 parameter.2 polynomial)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => 1)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (colour : Fin lattice.rank)
    (mode : ℕ) (charge : Charge lattice) (polynomial : Oscillator lattice),
    readout.readout () ⟨lattice, charge⟩
        (_root_.D5.S3.VertexAlgebra.LatticeActualAnnihilation.annihilate lattice colour mode polynomial) =
      _root_.D5.S3.VertexAlgebra.LatticeActualAnnihilation.polynomialDerivation lattice colour mode
        (halfTranslatedPolynomial lattice charge polynomial)

theorem source_bridge : (type_of% (@half_translated_derivation)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have contradiction := law probeLattice probeColour 0 0 0
  simp [rejected, realize, halfTranslatedPolynomial] at contradiction

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨⟨probeLattice, 0⟩, 0, 1, by simp [actual, realize, halfTranslatedPolynomial]⟩

def familyRegistration : Registration arena (type_of% (@half_translated_derivation)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp half_translated_derivation, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@half_translated_derivation) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients.half_translated_derivation "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients.TranslatedDerivation.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end TranslatedDerivation

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
