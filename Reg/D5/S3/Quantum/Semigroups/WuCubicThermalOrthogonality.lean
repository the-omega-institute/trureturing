import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuCubicThermalOrthogonality

/-! Source-bound readouts of the Gibbs pairing and its diagonal thermal basis. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix LeanInformationAudit
open scoped BigOperators ComplexConjugate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuCubicOperatorBridge (G Mat)
open _root_.D5.S3.Quantum.Semigroups.WuCubicThermalBasis (Index direction coefficient)
open _root_.D5.S3.Quantum.Semigroups.WuCubicThermalOrthogonality

namespace Reg.D5.S3.Quantum.Semigroups.WuCubicThermalOrthogonality

private abbrev equalitySignature (T : Type) : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => T) (fun _ => T → Prop)

private def equalityReadout (T : Type) : Realization (equalitySignature T) :=
  realize (equalitySignature T) (fun _ _ x y => x = y) (fun e => nomatch e)

private def falseReadout (T : Type) : Realization (equalitySignature T) :=
  realize (equalitySignature T) (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem equalityDependence {T : Type} [Zero T] [One T]
    (hne : (1 : T) ≠ 0) : ObservationalDependence (equalitySignature T) (equalityReadout T) := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro he
  exact hne (Eq.mp (congrFun he 0) rfl)

namespace TraceG

private abbrev signature : Signature := equalitySignature ℂ

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ}, 1 ≤ r → ∀ X Y : Mat,
    W.readout () () (gibbsPairing r X Y)
      ((G r ^ 3 * Xᴴ * G r ^ 3 * Y).trace)

private theorem rejected_law : ¬ arena.Law (falseReadout ℂ) := by
  intro h
  exact h (r := 1) le_rfl 0 0

def family : Registration arena (type_of% @gibbsPairing_eq_trace_G) where
  actual := equalityReadout ℂ
  bridge := Iff.rfl
  variation := ⟨@gibbsPairing_eq_trace_G, falseReadout ℂ, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law (equalityReadout ℂ) (falseReadout ℂ) rejected_law
  dependence := equalityDependence one_ne_zero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gibbsPairing_eq_trace_G) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicThermalOrthogonality.gibbsPairing_eq_trace_G.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicThermalOrthogonality.TraceG.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicThermalOrthogonality
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

end TraceG

namespace Direction

private abbrev signature : Signature := equalitySignature ℂ

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ}, 0 ≤ r → ∀ k l : Index,
    W.readout () ()
      (gibbsPairing r (direction r k) (direction r l))
      (if k = l then (directionNormSq r k : ℂ) else 0)

private theorem rejected_law : ¬ arena.Law (falseReadout ℂ) := by
  intro h
  exact h (r := 1) zero_le_one (0, 0) (0, 0)

def family : Registration arena (type_of% @gibbsPairing_direction) where
  actual := equalityReadout ℂ
  bridge := Iff.rfl
  variation := ⟨@gibbsPairing_direction, falseReadout ℂ, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law (equalityReadout ℂ) (falseReadout ℂ) rejected_law
  dependence := equalityDependence one_ne_zero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gibbsPairing_direction) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicThermalOrthogonality.gibbsPairing_direction.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicThermalOrthogonality.Direction.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicThermalOrthogonality
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

end Direction

namespace Expansion

private abbrev signature : Signature := equalitySignature ℂ

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ}, 0 ≤ r → ∀ X Y : Mat,
    W.readout () () (gibbsPairing r X Y)
      (∑ k : Index,
        conj (coefficient r X k) * coefficient r Y k * (directionNormSq r k : ℂ))

private theorem rejected_law : ¬ arena.Law (falseReadout ℂ) := by
  intro h
  exact h (r := 1) zero_le_one 0 0

def family : Registration arena (type_of% @gibbsPairing_expansion) where
  actual := equalityReadout ℂ
  bridge := Iff.rfl
  variation := ⟨@gibbsPairing_expansion, falseReadout ℂ, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law (equalityReadout ℂ) (falseReadout ℂ) rejected_law
  dependence := equalityDependence one_ne_zero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gibbsPairing_expansion) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicThermalOrthogonality.gibbsPairing_expansion.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicThermalOrthogonality.Expansion.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicThermalOrthogonality
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

end Expansion

end Reg.D5.S3.Quantum.Semigroups.WuCubicThermalOrthogonality
