import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Subentropy.GaussianQuadratic
import Reg.Support.SingleDependentReadout

noncomputable section
set_option autoImplicit false
open Matrix
open scoped BigOperators ComplexOrder
open _root_.D5.S3.Quantum.Subentropy.GaussianQuadratic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Quantum.Subentropy.GaussianQuadratic
universe u
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ q r => q ≤ r) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (z : EuclideanSpace ℂ ι),
    R.readout () () 0 (gaussianQuadratic A z)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := @h (ULift.{u} Unit) inferInstance inferInstance 0
    Matrix.PosSemidef.zero 0
  exact hb
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have ht := congrFun he 0
  norm_num [actual, realize] at ht
def family : Registration arena.{u} (type_of% @quadratic_nonnegative.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quadratic_nonnegative, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@quadratic_nonnegative.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.GaussianQuadratic.quadratic_nonnegative.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.GaussianQuadratic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q r => q ≤ r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.GaussianQuadratic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


namespace Coordinates
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ q r => q = r) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ q r => q + 1 = r) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι],
    (MeasureTheory.Measure.pi (fun _ : ι × Fin 2 => ProbabilityTheory.gaussianReal 0 1)).map
      complexGaussianCoordinates = ProbabilityTheory.stdGaussian (EuclideanSpace ℂ ι) ∧
    ∀ (z : (ι × Fin 2) → ℝ) (i : ι),
      R.readout () () (Complex.normSq (complexGaussianCoordinates z i))
        (z (i, 0)^2 + z (i, 1)^2)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := @h (ULift.{u} Unit) inferInstance inferInstance
  have hzero := he.2 (fun _ => 0) ⟨()⟩
  norm_num [rejected, realize, complexGaussianCoordinates, Complex.normSq_apply] at hzero
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have ht := congrFun he 0
  norm_num [actual, realize] at ht
def family : Registration arena.{u} (type_of% @complex_coordinate_transport.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@complex_coordinate_transport, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complex_coordinate_transport.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.GaussianQuadratic.complex_coordinate_transport.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.GaussianQuadratic.Coordinates.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q r => q = r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.GaussianQuadratic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Coordinates

namespace Spectral
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ q r => q = r) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ q r => q + 1 = r) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian),
    (∀ w : EuclideanSpace ℂ ι,
      R.readout () () (gaussianQuadratic A (hA.eigenvectorBasis.repr.symm w))
        ((∑ i, hA.eigenvalues i * Complex.normSq (w i)) / 2)) ∧
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℂ ι)).map hA.eigenvectorBasis.repr.symm =
      ProbabilityTheory.stdGaussian (EuclideanSpace ℂ ι)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := @h (ULift.{u} Unit) inferInstance inferInstance 0 Matrix.isHermitian_zero
  have hzero := he.1 0
  norm_num [rejected, realize, gaussianQuadratic] at hzero
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have ht := congrFun he 0
  norm_num [actual, realize] at ht
def family : Registration arena.{u} (type_of% @spectral_transport.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@spectral_transport, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@spectral_transport.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.GaussianQuadratic.spectral_transport.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.GaussianQuadratic.Spectral.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q r => q = r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.GaussianQuadratic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Spectral

end Reg.D5.S3.Quantum.Subentropy.GaussianQuadratic
