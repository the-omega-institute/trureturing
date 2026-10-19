import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.LinGProperty.Normalization
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for the matrix comparison prerequisites. -/

noncomputable section
set_option autoImplicit false
open Matrix
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Matrix.LinGProperty
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Quantum.Matrix.LinGProperty.Normalization
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev Block (n : ℕ) := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ
namespace ZeroBlock
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun n => Mat n) (fun n => Mat n → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {A X B : Mat n}, (fromBlocks A X Xᴴ B).PosSemidef →
    A = 0 ∨ B = 0 → R.readout () n X 0
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  apply h (n := 1) (A := 0) (X := 0) (B := 0) _ (Or.inl rfl)
  simpa using (Matrix.PosSemidef.zero : (0 : Block 1).PosSemidef)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro he
  change (fun y : Mat 1 => (0 : Mat 1) = y) = (fun y : Mat 1 => (1 : Mat 1) = y) at he
  have h10 : (1 : Mat 1) = 0 := by rw [← congrFun he 0]
  exact one_ne_zero h10
def family : Registration arena (type_of% (@offDiagonal_eq_zero)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@offDiagonal_eq_zero, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@offDiagonal_eq_zero) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.offDiagonal_eq_zero.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.Normalization.ZeroBlock.family
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
    owner := `D5.S3.Quantum.Matrix.LinGProperty.Normalization
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ZeroBlock

namespace PositiveTrace
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x < y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {A : Mat n}, A.PosSemidef → A ≠ 0 → R.readout () () 0 A.trace.re
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (n := 1) (A := 1) Matrix.PosSemidef.one one_ne_zero
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he (1/2)
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% (@positive_trace)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@positive_trace, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_trace) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.positive_trace.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.Normalization.PositiveTrace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.LinGProperty.Normalization
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
end PositiveTrace

namespace PositiveAugmentation
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun n => Mat n) (fun _ => Bool)
def actual : Realization signature := realize signature (fun _ (n : ℕ) (X : Mat n) =>
    @decide X.PosDef (Classical.propDecidable _)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {A : Mat n}, A.PosSemidef → A ≠ 0 →
    ∀ {c : ℝ}, 1 ≤ c → R.readout () n (phi c A) = true
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact Bool.false_ne_true
    (h (n := 1) (A := 1) Matrix.PosSemidef.one one_ne_zero (c := 1) le_rfl)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  have hzero : ¬ (0 : Mat 1).PosDef := by
    intro h
    exact not_isUnit_zero h.isUnit
  simp [actual, realize, hzero, Matrix.PosDef.one]
def family : Registration arena (type_of% (@phi_posDef)) where
  actual := actual
  bridge := by simp [arena, actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using @phi_posDef, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@phi_posDef) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.phi_posDef.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.Normalization.PositiveAugmentation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ (n : ℕ) (X : Mat n) =>
    @decide X.PosDef (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.LinGProperty.Normalization
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end PositiveAugmentation

namespace AugmentationScale
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun n => Mat n) (fun n => Mat n → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (c r : ℝ) (T : Mat n), R.readout () n (phi c (r • T)) (r • phi c T)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (n := 1) 0 0 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro he
  change (fun y : Mat 1 => (0 : Mat 1) = y) = (fun y : Mat 1 => (1 : Mat 1) = y) at he
  have h10 : (1 : Mat 1) = 0 := by rw [← congrFun he 0]
  exact one_ne_zero h10
def family : Registration arena (type_of% (@phi_smul)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@phi_smul, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@phi_smul) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.phi_smul.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.Normalization.AugmentationScale.family
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
    owner := `D5.S3.Quantum.Matrix.LinGProperty.Normalization
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AugmentationScale

namespace BlockScale
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun n => Block n) (fun _ => Bool)
def actual : Realization signature := realize signature (fun _ (n : ℕ) (W : Block n) =>
    @decide W.PosSemidef (Classical.propDecidable _)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {A X B : Mat n}, (fromBlocks A X Xᴴ B).PosSemidef →
    ∀ r s : ℝ, R.readout () n (fromBlocks ((r*r) • A) ((r*s) • X)
      ((r*s) • X)ᴴ ((s*s) • B)) = true
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  apply Bool.false_ne_true
  apply h (n := 1) (A := 0) (X := 0) (B := 0) _ 0 0
  simpa using (Matrix.PosSemidef.zero : (0 : Block 1).PosSemidef)
private theorem dependence : ObservationalDependence signature actual := by
  classical
  intro i
  refine ⟨1, 0, -1, ?_⟩
  intro he
  change @decide ((0 : Block 1).PosSemidef) (Classical.propDecidable _) =
    @decide ((-1 : Block 1).PosSemidef) (Classical.propDecidable _) at he
  have htrue : @decide ((-1 : Block 1).PosSemidef) (Classical.propDecidable _) = true := by
    rw [← he]
    exact decide_eq_true Matrix.PosSemidef.zero
  have hn : (-1 : Block 1).PosSemidef := of_decide_eq_true htrue
  have hd := hn.diag_nonneg (i := Sum.inl 0)
  norm_num at hd
def family : Registration arena (type_of% (@block_scale_posSemidef)) where
  actual := actual
  bridge := by simp [arena, actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using @block_scale_posSemidef, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@block_scale_posSemidef) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.block_scale_posSemidef.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.Normalization.BlockScale.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ (n : ℕ) (W : Block n) =>
    @decide W.PosSemidef (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.LinGProperty.Normalization
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end BlockScale

end Reg.D5.S3.Quantum.Matrix.LinGProperty.Normalization
