import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for quantitative matrix geometric mean estimates. -/

noncomputable section
set_option autoImplicit false
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open _root_.D5.S3.Quantum.Matrix.LinGProperty
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun n => Mat n) (fun n => Mat n → Prop)
def orderActual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def equalityActual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem orderDependence : ObservationalDependence signature orderActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro he
  change (fun y : Mat 1 => (0 : Mat 1) ≤ y) = (fun y : Mat 1 => (1 : Mat 1) ≤ y) at he
  have h10 : (1 : Mat 1) ≤ 0 := by
    rw [← congrFun he 0]
  have hd := (Matrix.le_iff.mp h10).diag_nonneg (i := 0)
  norm_num at hd
private theorem equalityDependence : ObservationalDependence signature equalityActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro he
  change (fun y : Mat 1 => (0 : Mat 1) = y) = (fun y : Mat 1 => (1 : Mat 1) = y) at he
  have h10 : (1 : Mat 1) = 0 := by
    rw [← congrFun he 0]
  exact one_ne_zero h10

namespace Riccati
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {P Q : Mat n}, P.PosDef → Q.PosDef →
    (geometricMean P Q).PosDef ∧
      R.readout () n (geometricMean P Q * P⁻¹ * geometricMean P Q) Q
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact (h (n := 1) (P := 1) (Q := 1) Matrix.PosDef.one Matrix.PosDef.one).2
def family : Registration arena (type_of% (@geometricMean_riccati)) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@geometricMean_riccati, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law equalityActual rejected rejectedLaw
  dependence := equalityDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@geometricMean_riccati) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.geometricMean_riccati.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound.Riccati.family
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
    owner := `D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Riccati

namespace Harmonic
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {P Q : Mat n}, P.PosDef → Q.PosDef →
    R.readout () n (((1/2 : ℝ) • (P⁻¹ + Q⁻¹))⁻¹) (geometricMean P Q)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (n := 1) (P := 1) (Q := 1) Matrix.PosDef.one Matrix.PosDef.one
def family : Registration arena (type_of% (@harmonic_le_geometricMean)) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@harmonic_le_geometricMean, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law orderActual rejected rejectedLaw
  dependence := orderDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@harmonic_le_geometricMean) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.harmonic_le_geometricMean.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound.Harmonic.family
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
    owner := `D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Harmonic

namespace Correction
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {P Q : Mat n}, P.PosDef → Q.PosDef →
    R.readout () n (((1/2 : ℝ) • (P⁻¹ + Q⁻¹))⁻¹)
      ((1/2 : ℝ) • (P+Q) - ((1/2 : ℝ) • (P-Q)) * ((1/2 : ℝ) • (P+Q))⁻¹ * ((1/2 : ℝ) • (P-Q)))
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (n := 1) (P := 1) (Q := 1) Matrix.PosDef.one Matrix.PosDef.one
def family : Registration arena (type_of% (@harmonic_eq_arithmetic_correction)) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@harmonic_eq_arithmetic_correction, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law equalityActual rejected rejectedLaw
  dependence := equalityDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@harmonic_eq_arithmetic_correction) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.harmonic_eq_arithmetic_correction.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound.Correction.family
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
    owner := `D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Correction

namespace Quantitative
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {P Q : Mat n}, P.PosDef → Q.PosDef →
    ∀ {c d : ℝ}, 0 < c → c • (1 : Mat n) ≤ (1/2 : ℝ) • (P+Q) →
    ((1/2 : ℝ) • (P-Q)) * ((1/2 : ℝ) • (P-Q)) ≤ d • (1 : Mat n) →
    R.readout () n ((1/2 : ℝ) • (P+Q) - (d/c) • (1 : Mat n)) (geometricMean P Q)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  apply h (n := 1) (P := 1) (Q := 1) Matrix.PosDef.one Matrix.PosDef.one
    (c := 1) (d := 0) (by norm_num)
  · have he : (1 / 2 : ℝ) • ((1 : Mat 1) + 1) = 1 := by module
    simpa only [he, one_smul] using (le_rfl : (1 : Mat 1) ≤ 1)
  · simp
def family : Registration arena (type_of% (@arithmetic_sub_le_geometricMean)) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@arithmetic_sub_le_geometricMean, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law orderActual rejected rejectedLaw
  dependence := orderDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@arithmetic_sub_le_geometricMean) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.arithmetic_sub_le_geometricMean.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound.Quantitative.family
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
    owner := `D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Quantitative

namespace Homogeneity
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {P Q : Mat n}, P.PosDef → Q.PosDef →
    ∀ {r s : ℝ}, 0 < r → 0 < s →
    R.readout () n (geometricMean (r • P) (s • Q))
      (Real.sqrt (r*s) • geometricMean P Q)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (n := 1) (P := 1) (Q := 1) Matrix.PosDef.one Matrix.PosDef.one
    (r := 1) (s := 1) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@geometricMean_smul)) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@geometricMean_smul, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law equalityActual rejected rejectedLaw
  dependence := equalityDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@geometricMean_smul) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.geometricMean_smul.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound.Homogeneity.family
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
    owner := `D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Homogeneity

namespace ZeroRight
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (P : Mat n), R.readout () n (geometricMean P 0) 0
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (n := 1) 0
def family : Registration arena (type_of% (@geometricMean_zero_right)) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@geometricMean_zero_right, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law equalityActual rejected rejectedLaw
  dependence := equalityDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@geometricMean_zero_right) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.geometricMean_zero_right.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound.ZeroRight.family
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
    owner := `D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ZeroRight

namespace ZeroLeft
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (Q : Mat n), R.readout () n (geometricMean 0 Q) 0
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (n := 1) 0
def family : Registration arena (type_of% (@geometricMean_zero_left)) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@geometricMean_zero_left, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law equalityActual rejected rejectedLaw
  dependence := equalityDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@geometricMean_zero_left) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.geometricMean_zero_left.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound.ZeroLeft.family
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
    owner := `D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ZeroLeft

end Reg.D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound
