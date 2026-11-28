import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy

/-! Source-bound readouts for the Wu translation energy and variance. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix LeanInformationAudit
open scoped BigOperators ComplexConjugate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuCubicOperatorBridge (D Mat Occupation generator)
open _root_.D5.S3.Quantum.Semigroups.WuCubicThermalBasis (Index charge coefficient degree direction)
open _root_.D5.S3.Quantum.Semigroups.WuCubicThermalOrthogonality (directionNormSq)
open _root_.D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy
open private direction_zero from D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy

namespace Reg.D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy

private abbrev readoutSignature (State Output : Type) : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => State) (fun _ => Output)

private def falseRelation (T : Type) : Realization (readoutSignature T (T → Prop)) :=
  realize (readoutSignature T (T → Prop)) (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem relationDependence {T : Type} [Zero T] [One T] (rel : T → T → Prop)
    (hzero : rel 0 0) (hone : ¬ rel 1 0) :
    ObservationalDependence (readoutSignature T (T → Prop))
      (realize (readoutSignature T (T → Prop)) (fun _ _ x y => rel x y) (fun e => nomatch e)) := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact hone (Eq.mp (congrFun h 0) hzero)

private abbrev derivativeSignature : Signature :=
  readoutSignature (ℝ → ℝ) (ℝ → ℝ → Prop)

private def falseDerivative : Realization derivativeSignature :=
  realize derivativeSignature (fun _ _ _ _ _ => False) (fun e => nomatch e)

private theorem derivativeDependence :
    ObservationalDependence derivativeSignature
      (realize derivativeSignature (fun _ _ f => HasDerivAt f) (fun e => nomatch e)) := by
  intro role
  refine ⟨(), (fun _ : ℝ => 0), id, ?_⟩
  intro h
  have hzero : HasDerivAt (id : ℝ → ℝ) 0 0 :=
    Eq.mp (congrFun (congrFun h 0) 0) (hasDerivAt_const 0 (0 : ℝ))
  exact one_ne_zero ((hasDerivAt_id 0).unique hzero)

private theorem zero_centered (r : ℝ) : (D r * (0 : Mat)).trace = 0 := by simp

namespace Stationary

private abbrev signature : Signature := readoutSignature ℂ (ℂ → Prop)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ}, 1 ≤ r → ∀ A : Mat,
    R.readout () () (D r * generator r A).trace 0

private theorem rejected_law : ¬ arena.Law (falseRelation ℂ) := by
  intro h
  exact h (r := 1) le_rfl 0

def family : Registration arena (type_of% @stationary) where
  actual := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@stationary, (falseRelation ℂ), rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ (falseRelation ℂ) rejected_law
  dependence := relationDependence (· = ·) rfl one_ne_zero

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@stationary) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.stationary.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.Stationary.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy
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

end Stationary

namespace AffineTranslation

private abbrev signature : Signature := readoutSignature ℝ (ℝ → Prop)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ}, 1 ≤ r → ∀ (A : Mat) (t : ℝ),
    R.readout () () (cubicEnergy r (translate A t))
      (t * ((9 / 8 : ℝ) * ((base r * sandwich r A + sandwich r A * base r) *
          sandwich r (generator r A)).trace.re) + cubicEnergy r A)

private theorem rejected_law : ¬ arena.Law (falseRelation ℝ) := by
  intro h
  exact h (r := 1) le_rfl 0 0

def family : Registration arena (type_of% @cubicEnergy_translate) where
  actual := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@cubicEnergy_translate, (falseRelation ℝ), rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ (falseRelation ℝ) rejected_law
  dependence := relationDependence (· = ·) rfl one_ne_zero

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cubicEnergy_translate) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.cubicEnergy_translate.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.AffineTranslation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy
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

end AffineTranslation

namespace TraceDerivative

private abbrev signature : Signature := derivativeSignature

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ}, 1 ≤ r → ∀ (A : Mat) (t : ℝ),
    R.readout () () (fun s : ℝ => cubicEnergy r (translate A s))
      ((9 / 8 : ℝ) * ((base r * sandwich r A + sandwich r A * base r) *
          sandwich r (generator r A)).trace.re) t

private theorem rejected_law : ¬ arena.Law falseDerivative := by
  intro h
  exact h (r := 1) le_rfl 0 0

def family : Registration arena (type_of% @cubicEnergy_hasDerivAt_trace) where
  actual := realize signature (fun _ _ f => HasDerivAt f) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@cubicEnergy_hasDerivAt_trace, falseDerivative, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ falseDerivative rejected_law
  dependence := derivativeDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cubicEnergy_hasDerivAt_trace) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.cubicEnergy_hasDerivAt_trace.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.TraceDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => HasDerivAt f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TraceDerivative

namespace ChargeMultiplier

private abbrev signature : Signature := readoutSignature ℝ (ℝ → Prop)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ}, 1 ≤ r → ∀ (k : Index) (i j : Occupation),
    direction r k i j ≠ 0 →
      R.readout () () (entryMultiplier r i j) (chargeMultiplier r (charge k))

private theorem rejected_law : ¬ arena.Law (falseRelation ℝ) := by
  intro h
  let i : Occupation := (0, 0)
  have hentry : direction 1 (0, 0) i i ≠ 0 := by
    rw [direction_zero, Matrix.one_apply_eq]
    exact one_ne_zero
  exact h (r := 1) le_rfl (0, 0) i i hentry

def family : Registration arena (type_of% @entryMultiplier_of_direction) where
  actual := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@entryMultiplier_of_direction, (falseRelation ℝ), rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ (falseRelation ℝ) rejected_law
  dependence := relationDependence (· = ·) rfl one_ne_zero

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@entryMultiplier_of_direction) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.entryMultiplier_of_direction.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.ChargeMultiplier.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy
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

end ChargeMultiplier

namespace VariancePairing

private abbrev signature : Signature := readoutSignature ℂ (ℂ → Prop)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ}, 1 ≤ r → ∀ X Y : Mat,
    R.readout () () (vPairing r X Y)
      (∑ k : Index, conj (coefficient r X k) * coefficient r Y k *
        ((chargeMultiplier r (charge k) * directionNormSq r k : ℝ) : ℂ))

private theorem rejected_law : ¬ arena.Law (falseRelation ℂ) := by
  intro h
  exact h (r := 1) le_rfl 0 0

def family : Registration arena (type_of% @vPairing_expansion) where
  actual := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@vPairing_expansion, (falseRelation ℂ), rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ (falseRelation ℂ) rejected_law
  dependence := relationDependence (· = ·) rfl one_ne_zero

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@vPairing_expansion) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.vPairing_expansion.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.VariancePairing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy
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

end VariancePairing

namespace VarianceEntries

private abbrev signature : Signature := readoutSignature ℝ (ℝ → Prop)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r : ℝ) (A : Mat), A.IsHermitian →
    R.readout () () (V r A) (∑ i : Occupation, ∑ j : Occupation,
        pairWeight r i j * Complex.normSq (A i j))

private theorem rejected_law : ¬ arena.Law (falseRelation ℝ) := by
  intro h
  exact h 1 0 Matrix.isHermitian_zero

def family : Registration arena (type_of% @V_eq_entries) where
  actual := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@V_eq_entries, (falseRelation ℝ), rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ (falseRelation ℝ) rejected_law
  dependence := relationDependence (· = ·) rfl one_ne_zero

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@V_eq_entries) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.V_eq_entries.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.VarianceEntries.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy
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

end VarianceEntries

namespace ComponentWeight

private abbrev signature : Signature := readoutSignature ℝ (ℝ → Prop)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ}, 1 ≤ r → ∀ (A : Mat) (k : Index),
    let Z := coefficient r A k • direction r k
    R.readout () () (vWeight r A k) (∑ i : Occupation, ∑ j : Occupation,
        pairWeight r i j * Complex.normSq (Z i j))

private theorem rejected_law : ¬ arena.Law (falseRelation ℝ) := by
  intro h
  exact h (r := 1) le_rfl 0 (0, 0)

def family : Registration arena (type_of% @vWeight_eq_component) where
  actual := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@vWeight_eq_component, (falseRelation ℝ), rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ (falseRelation ℝ) rejected_law
  dependence := relationDependence (· = ·) rfl one_ne_zero

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@vWeight_eq_component) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.vWeight_eq_component.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.ComponentWeight.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ComponentWeight

namespace VarianceSum

private abbrev signature : Signature := readoutSignature ℝ (ℝ → Prop)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ}, 1 ≤ r → ∀ A : Mat, A.IsHermitian →
    R.readout () () (V r A) (∑ k : Index, vWeight r A k)

private theorem rejected_law : ¬ arena.Law (falseRelation ℝ) := by
  intro h
  exact h (r := 1) le_rfl 0 Matrix.isHermitian_zero

def family : Registration arena (type_of% @V_eq_sum) where
  actual := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@V_eq_sum, (falseRelation ℝ), rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ (falseRelation ℝ) rejected_law
  dependence := relationDependence (· = ·) rfl one_ne_zero

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@V_eq_sum) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.V_eq_sum.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.VarianceSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy
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

end VarianceSum

namespace DegreeDerivative

private abbrev signature : Signature := derivativeSignature

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ}, 1 ≤ r → ∀ A : Mat, A.IsHermitian → ∀ t : ℝ,
    R.readout () () (fun s : ℝ => cubicEnergy r (translate A s))
      ((9 / 4 : ℝ) * ∑ k : Index, (degree k : ℝ) * vWeight r A k) t

private theorem rejected_law : ¬ arena.Law falseDerivative := by
  intro h
  exact h (r := 1) le_rfl 0 Matrix.isHermitian_zero 0

def family : Registration arena (type_of% @cubicEnergy_hasDerivAt_degree) where
  actual := realize signature (fun _ _ f => HasDerivAt f) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@cubicEnergy_hasDerivAt_degree, falseDerivative, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ falseDerivative rejected_law
  dependence := derivativeDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cubicEnergy_hasDerivAt_degree) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.cubicEnergy_hasDerivAt_degree.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.DegreeDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => HasDerivAt f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DegreeDerivative

namespace DegreeGap

private abbrev signature : Signature := readoutSignature ℝ (ℝ → Prop)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ}, 1 ≤ r → ∀ A : Mat, A.IsHermitian →
    (D r * A).trace = 0 →
      R.readout () () (2 * V r A - V₁ r A) (∑ k : Index, (degree k : ℝ) * vWeight r A k)

private theorem rejected_law : ¬ arena.Law (falseRelation ℝ) := by
  intro h
  exact h (r := 1) le_rfl 0 Matrix.isHermitian_zero (zero_centered 1)

def family : Registration arena (type_of% @degree_sum_ge) where
  actual := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@degree_sum_ge, (falseRelation ℝ), rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ (falseRelation ℝ) rejected_law
  dependence := relationDependence (· ≤ ·) le_rfl (not_le_of_gt zero_lt_one)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@degree_sum_ge) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.degree_sum_ge.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.DegreeGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DegreeGap

namespace DerivativeBound

private abbrev signature : Signature := readoutSignature ℝ (ℝ → Prop)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ}, 1 ≤ r → ∀ A : Mat, A.IsHermitian →
    (D r * A).trace = 0 → ∀ t : ℝ,
      R.readout () () ((9 / 4 : ℝ) * (2 * V r A - V₁ r A))
        (deriv (fun s : ℝ => cubicEnergy r (translate A s)) t)

private theorem rejected_law : ¬ arena.Law (falseRelation ℝ) := by
  intro h
  exact h (r := 1) le_rfl 0 Matrix.isHermitian_zero (zero_centered 1) 0

def family : Registration arena (type_of% @cubicEnergy_deriv_ge) where
  actual := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@cubicEnergy_deriv_ge, (falseRelation ℝ), rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ (falseRelation ℝ) rejected_law
  dependence := relationDependence (· ≤ ·) le_rfl (not_le_of_gt zero_lt_one)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cubicEnergy_deriv_ge) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.cubicEnergy_deriv_ge.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy.DerivativeBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy
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

end DerivativeBound

end Reg.D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy
