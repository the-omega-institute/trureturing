import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
import Reg.Support.SingleDependentReadout

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped ComplexOrder
open _root_.D5.S3.Quantum.Matrix.LinGProperty
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {A X B : Matrix (Fin n) (Fin n) ℂ},
    (fromBlocks A X Xᴴ B).PosSemidef → A.trace = 1 → B.trace = 1 →
    ∀ (hAp : A.PosSemidef) (hBp : B.PosSemidef) (j : Fin (Fintype.card (Fin n))),
    R.readout () () (2 * singularValuesSorted X j)
      ((hAp.1.add hBp.1).eigenvalues₀ j + 1 - ‖X.trace‖)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hw : (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0
      (1 : Matrix (Fin 1) (Fin 1) ℂ)).PosSemidef := by
    rw [Matrix.fromBlocks_one]
    exact Matrix.PosSemidef.one
  exact @h 1 1 0 1 (by simpa using hw) (by simp [Matrix.trace])
    (by simp [Matrix.trace]) Matrix.PosSemidef.one Matrix.PosSemidef.one ⟨0, by simp⟩
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have ht := congrFun he 0
  norm_num [actual, realize] at ht
def family : Registration arena (type_of% @normalized_arithmetic_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalized_arithmetic_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@normalized_arithmetic_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.normalized_arithmetic_bound.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound

namespace Reg.D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
universe u

namespace CharacteristicPolynomial
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A.charpoly = B.charpoly) (j : Fin (Fintype.card ι)),
    R.readout () () (hA.eigenvalues₀ j) (hB.eigenvalues₀ j)
private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance 0 0
    Matrix.isHermitian_zero Matrix.isHermitian_zero rfl ⟨0, by simp⟩
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh
def family : Registration arena.{u} (type_of% @eigenvalues_zero_eq_of_charpoly.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eigenvalues_zero_eq_of_charpoly.{u}, rejected, rejectedLaw.{u}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejectedLaw.{u}
  dependence := dependence
def audit.{ut} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eigenvalues_zero_eq_of_charpoly.{ut}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.eigenvalues_zero_eq_of_charpoly.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound.CharacteristicPolynomial.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{ut}⟩
  objectArena := .source ⟨arena.{ut}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{ut} ⟨family.{ut}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end CharacteristicPolynomial

namespace RectangularGram
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ {n : ℕ}
    (T : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ)
    (j : Fin (Fintype.card (Fin n))),
    R.readout () () ((isHermitian_conjTranspose_mul_self T).eigenvalues₀
      ⟨j.val, by simp only [Fintype.card_sum, Fintype.card_fin]; have hj := j.isLt; simp only [Fintype.card_fin] at hj; omega⟩) ((isHermitian_mul_conjTranspose_self T).eigenvalues₀ j)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact @h 1 0 ⟨0, by simp⟩
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% @rectangular_gram_eigenvalues) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rectangular_gram_eigenvalues, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rectangular_gram_eigenvalues) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.rectangular_gram_eigenvalues.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound.RectangularGram.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end RectangularGram

namespace EigenvalueOrder
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : (B - A).PosSemidef) (j : Fin (Fintype.card ι)),
    R.readout () () (hA.eigenvalues₀ j) (hB.eigenvalues₀ j)
private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance 0 0
    Matrix.isHermitian_zero Matrix.isHermitian_zero
    (by simpa using (Matrix.PosSemidef.zero : (0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ).PosSemidef))
    ⟨0, by simp⟩
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh
def family : Registration arena.{u} (type_of% @eigenvalues_zero_mono_finite.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eigenvalues_zero_mono_finite.{u}, rejected, rejectedLaw.{u}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejectedLaw.{u}
  dependence := dependence
def audit.{ut} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eigenvalues_zero_mono_finite.{ut}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.eigenvalues_zero_mono_finite.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound.EigenvalueOrder.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{ut}⟩
  objectArena := .source ⟨arena.{ut}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{ut} ⟨family.{ut}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end EigenvalueOrder

namespace EigenvalueScale
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (r : ℝ) (hr : 0 ≤ r)
    (hB : ((r : ℂ) • A).IsHermitian) (j : Fin (Fintype.card ι)),
    R.readout () () (hB.eigenvalues₀ j) (r * hA.eigenvalues₀ j)
private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance 0 Matrix.isHermitian_zero
    0 (by norm_num) (by simp) ⟨0, by simp⟩
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh
def family : Registration arena.{u} (type_of% @eigenvalues_zero_smul_finite.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eigenvalues_zero_smul_finite.{u}, rejected, rejectedLaw.{u}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejectedLaw.{u}
  dependence := dependence
def audit.{ut} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eigenvalues_zero_smul_finite.{ut}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.eigenvalues_zero_smul_finite.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound.EigenvalueScale.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{ut}⟩
  objectArena := .source ⟨arena.{ut}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{ut} ⟨family.{ut}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end EigenvalueScale

namespace EigenvalueShift
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (r : ℝ)
    (hB : (A + (r : ℂ) • 1).IsHermitian) (j : Fin (Fintype.card ι)),
    R.readout () () (hB.eigenvalues₀ j) (hA.eigenvalues₀ j + r)
private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance 0 Matrix.isHermitian_zero
    0 (by simp) ⟨0, by simp⟩
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh
def family : Registration arena.{u} (type_of% @eigenvalues_zero_add_scalar_finite.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eigenvalues_zero_add_scalar_finite.{u}, rejected, rejectedLaw.{u}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejectedLaw.{u}
  dependence := dependence
def audit.{ut} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eigenvalues_zero_add_scalar_finite.{ut}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.eigenvalues_zero_add_scalar_finite.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound.EigenvalueShift.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{ut}⟩
  objectArena := .source ⟨arena.{ut}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{ut} ⟨family.{ut}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end EigenvalueShift

namespace Dilation
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ)
    (hD : (fromBlocks 0 X Xᴴ (0 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian)
    (j : Fin (Fintype.card (Fin n))),
    R.readout () () (hD.eigenvalues₀ ⟨j.val, by simp only [Fintype.card_sum, Fintype.card_fin]; have hj := j.isLt; simp only [Fintype.card_fin] at hj; omega⟩) (singularValuesSorted X j)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact @h 1 0 (by simp) ⟨0, by simp⟩
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% @dilation_eigenvalues) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@dilation_eigenvalues, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@dilation_eigenvalues) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.dilation_eigenvalues.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound.Dilation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Dilation
end Reg.D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
