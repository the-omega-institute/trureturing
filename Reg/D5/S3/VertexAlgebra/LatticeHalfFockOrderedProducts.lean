import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
import D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts

set_option autoImplicit false
namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
private def probeLattice : LatticeData where
  rank := 1
  G := fun _ _ => 2
  symmetric := by intros; rfl
  even_diagonal := by intro _; exact ⟨1, rfl⟩

private theorem creation_zero (D : LatticeData) (charge : Charge D) :
    halfCreationCoeff D charge 0 = 1 := by
  simp [halfCreationCoeff, exponential_constant]

namespace TranslationComposition
abbrev signature := LatticeHalfFockChargedTensorCoefficients.TranslationReadout.signature
abbrev actual := LatticeHalfFockChargedTensorCoefficients.TranslationReadout.actual
abbrev rejected := LatticeHalfFockChargedTensorCoefficients.TranslationReadout.rejected
abbrev dependence := LatticeHalfFockChargedTensorCoefficients.TranslationReadout.dependence
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (left right : Charge D) (polynomial : Oscillator D),
    secondTranslationLift D left (readout.readout () ⟨D, right⟩ polynomial) =
      pairTranslation D left right polynomial
theorem source_bridge : (type_of% (@pair_translation_composition)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law probeLattice 0 0 1
  have impossible : (0 : PairPolynomial probeLattice) = 1 := by
    simpa [rejected, LatticeHalfFockChargedTensorCoefficients.TranslationReadout.rejected,
      realize] using bad
  exact zero_ne_one impossible

def familyRegistration : Registration arena (type_of% (@pair_translation_composition)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp pair_translation_composition, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pair_translation_composition) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.pair_translation_composition "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.TranslationComposition.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end TranslationComposition

namespace KernelConstant
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ lattice : LatticeData, Charge lattice) (fun _ => ℤ)
  (fun parameter => Oscillator parameter.1)
def actual : Realization signature := realize signature
  (fun _ parameter degree => halfCreationCoeff parameter.1 parameter.2 degree)
  (fun empty => nomatch empty)
def rejected : Realization signature := realize signature
  (fun _ parameter degree => halfCreationCoeff parameter.1 parameter.2 degree + 1)
  (fun empty => nomatch empty)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨probeLattice, 0⟩, 0, -1, ?_⟩
  simp [actual, realize, halfCreationCoeff, exponential_constant]
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (left right : Charge D) (first second : ℤ) (scalar : ℂ),
    commonKernel D left right first second (MvPolynomial.C scalar) =
      MvPolynomial.C scalar * (readout.readout () ⟨D, left⟩ first *
        halfCreationCoeff D right second)
theorem source_bridge : (type_of% (@kernel_constant)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law probeLattice 0 0 0 0 1
  rw [kernel_constant] at bad
  have impossible : (0 : Oscillator probeLattice) = 1 := by
    simpa [rejected, realize, creation_zero] using bad
  exact zero_ne_one impossible

def familyRegistration : Registration arena (type_of% (@kernel_constant)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp kernel_constant, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kernel_constant) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.kernel_constant "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.KernelConstant.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end KernelConstant

namespace KernelCreator
abbrev signature := LatticeHalfFockChargedTensorCoefficients.CreatorReadout.signature
abbrev actual := LatticeHalfFockChargedTensorCoefficients.CreatorReadout.actual
abbrev rejected := LatticeHalfFockChargedTensorCoefficients.CreatorReadout.rejected
abbrev dependence := LatticeHalfFockChargedTensorCoefficients.CreatorReadout.dependence
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (left right : Charge D) (first second : ℤ)
    (polynomial : Oscillator D) (index : Index D),
    commonKernel D left right first second (MvPolynomial.X index * polynomial) =
      readout.readout () D index * commonKernel D left right first second polynomial -
        (bilinear D left (unitCharge D index.1) : ℂ) •
          commonKernel D left right (first + omega D index) second polynomial -
        (bilinear D right (unitCharge D index.1) : ℂ) •
          commonKernel D left right first (second + omega D index) polynomial
theorem source_bridge : (type_of% (@kernel_creator)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law probeLattice 0 0 0 0 1 ((0 : Fin 1), 0)
  rw [kernel_creator] at bad
  have unit : commonKernel probeLattice 0 0 0 0 1 = 1 := by
    simpa [creation_zero] using kernel_constant probeLattice 0 0 0 0 1
  rw [unit] at bad
  have impossible : (0 : Oscillator probeLattice) = 1 := by
    simpa [rejected, LatticeHalfFockChargedTensorCoefficients.CreatorReadout.rejected,
      realize, bilinear] using bad
  exact zero_ne_one impossible

def familyRegistration : Registration arena (type_of% (@kernel_creator)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp kernel_creator, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kernel_creator) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.kernel_creator "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.KernelCreator.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end KernelCreator

namespace RectangularSupport
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ lattice : LatticeData, Σ _ : Charge lattice, Σ _ : Charge lattice, Σ _ : ℤ, ℤ)
  (fun parameter => Oscillator parameter.1) (fun parameter => Oscillator parameter.1)
def actual : Realization signature := realize signature
  (fun _ parameter polynomial => commonKernel parameter.1 parameter.2.1 parameter.2.2.1
    parameter.2.2.2.1 parameter.2.2.2.2 polynomial) (fun empty => nomatch empty)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun empty => nomatch empty)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨probeLattice, 0, 0, 0, 0⟩, 0, 1, ?_⟩
  have unit : commonKernel probeLattice 0 0 0 0 1 = 1 := by
    simpa [creation_zero] using kernel_constant probeLattice 0 0 0 0 1
  simpa [actual, realize, unit] using (zero_ne_one : (0 : Oscillator probeLattice) ≠ 1)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (left right : Charge D) (polynomial : Oscillator D),
    ∃ firstBound secondBound : ℤ, ∀ first second : ℤ,
      first < firstBound ∨ second < secondBound →
        readout.readout () ⟨D, left, right, first, second⟩ polynomial = 0
theorem source_bridge : (type_of% (@common_kernel_rectangular_support)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨firstBound, secondBound, bound⟩ := law probeLattice 0 0 0
  have bad := bound (firstBound - 1) secondBound (Or.inl (by omega))
  exact one_ne_zero (show (1 : Oscillator probeLattice) = 0 from bad)

def familyRegistration : Registration arena (type_of% (@common_kernel_rectangular_support)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp common_kernel_rectangular_support, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@common_kernel_rectangular_support) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.common_kernel_rectangular_support "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.RectangularSupport.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
    definition := none
    coordinates := #[0, 1, 2, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end RectangularSupport

namespace OrderedSupport
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ lattice : LatticeData, Σ _ : Charge lattice, Σ _ : Charge lattice, Σ _ : ℤ, Σ _ : ℤ, ℕ)
  (fun parameter => Oscillator parameter.1) (fun parameter => Oscillator parameter.1)
def actual : Realization signature := realize signature
  (fun _ parameter polynomial => commonKernel parameter.1 parameter.2.1 parameter.2.2.1
    (parameter.2.2.2.1 + parameter.2.2.2.2.2)
    (parameter.2.2.2.2.1 - parameter.2.2.2.2.2) polynomial) (fun empty => nomatch empty)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun empty => nomatch empty)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨probeLattice, 0, 0, 0, 0, 0⟩, 0, 1, ?_⟩
  have unit : commonKernel probeLattice 0 0 0 0 1 = 1 := by
    simpa [creation_zero] using kernel_constant probeLattice 0 0 0 0 1
  simpa [actual, realize, unit] using (zero_ne_one : (0 : Oscillator probeLattice) ≠ 1)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (left right : Charge D) (first second : ℤ)
    (polynomial : Oscillator D),
    Function.HasFiniteSupport (fun degree : ℕ =>
      (show Oscillator D from
        readout.readout () ⟨D, left, right, first, second, degree⟩ polynomial)) ∧
    Function.HasFiniteSupport (fun degree : ℕ =>
      commonKernel D left right (first - degree) (second + degree) polynomial)
theorem source_bridge : (type_of% (@common_kernel_ordered_finite_support)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have finite := (law probeLattice 0 0 0 0 0).1
  have support : Function.support (fun _ : ℕ => (1 : Oscillator probeLattice)) = Set.univ := by
    ext degree
    simp
  change (Function.support (fun _ : ℕ => (1 : Oscillator probeLattice))).Finite at finite
  rw [support] at finite
  exact Set.infinite_univ finite

def familyRegistration : Registration arena (type_of% (@common_kernel_ordered_finite_support)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp common_kernel_ordered_finite_support, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@common_kernel_ordered_finite_support) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.common_kernel_ordered_finite_support "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.OrderedSupport.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end OrderedSupport

namespace NativeOrderedProduct
abbrev signature := LatticeHalfFockChargedTensorCoefficients.NormReadout.signature
abbrev actual := LatticeHalfFockChargedTensorCoefficients.NormReadout.actual
def rejected : Realization signature := realize signature
  (fun _ D charge => chargeNorm D charge + 1) (fun empty => nomatch empty)
private theorem dependence : ObservationalDependence signature actual :=
  LatticeHalfFockChargedTensorCoefficients.PolynomialLowerBound.familyRegistration.dependence
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (left right : Charge D) (first second : ℤ)
    (polynomial : Oscillator D),
    oscillatorCoefficient D left (first - readout.readout () D left)
      (oscillatorCoefficient D right (second - chargeNorm D right) polynomial) =
        ∑ᶠ degree : ℕ, (PowerSeries.coeff degree (halfContraction D left right)) •
          commonKernel D left right (first + degree) (second - degree) polynomial
theorem source_bridge : (type_of% (@native_ordered_product)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law probeLattice 0 0 0 0 1
  have good := native_ordered_product probeLattice 0 0 0 0 1
  have unit : oscillatorCoefficient probeLattice 0 0 (1 : Oscillator probeLattice) = 1 := by
    exact LatticeHalfFockChargedTensorCoefficients.coefficient_unit probeLattice
  have negative : oscillatorCoefficient probeLattice 0 (-1) (1 : Oscillator probeLattice) = 0 := by
    rw [oscillatorCoefficient_as_sum]
    have constant : halfTranslatedPolynomial probeLattice 0 (1 : Oscillator probeLattice) =
        Polynomial.C 1 := by simp [halfTranslatedPolynomial]
    rw [constant]
    change Polynomial.sum (Polynomial.C (1 : Oscillator probeLattice))
      (fun degree coefficient => coefficient *
        halfCreationCoeff probeLattice 0 (-1 + chargeNorm probeLattice 0 + degree)) = 0
    rw [Polynomial.sum_C_index (by simp)]
    simp [chargeNorm, bilinear, halfCreationCoeff]
  have impossible : (0 : Oscillator probeLattice) = 1 := by
    simpa [rejected, realize, chargeNorm, bilinear, unit, negative] using bad.trans good.symm
  exact zero_ne_one impossible

def familyRegistration : Registration arena (type_of% (@native_ordered_product)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp native_ordered_product, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_ordered_product) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.native_ordered_product "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.NativeOrderedProduct.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end NativeOrderedProduct

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
