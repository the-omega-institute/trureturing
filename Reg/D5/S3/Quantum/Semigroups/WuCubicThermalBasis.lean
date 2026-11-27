import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuCubicThermalBasis

/-! Source-bound readouts of the common thermal eigenbasis. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix LeanInformationAudit
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuCubicOperatorBridge (Mat D generator)
open _root_.D5.S3.Quantum.Semigroups.WuCubicThermalBasis

namespace Reg.D5.S3.Quantum.Semigroups.WuCubicThermalBasis

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

namespace Rates

private abbrev signature : Signature := equalitySignature ℝ

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ}, 0 ≤ r →
    W.readout () () (a r + b r) 1

private theorem rejected_law : ¬ arena.Law (falseReadout ℝ) := by
  intro h
  exact h (r := 1) zero_le_one

def family : Registration arena (type_of% @a_add_b) where
  actual := equalityReadout ℝ
  bridge := Iff.rfl
  variation := ⟨@a_add_b, falseReadout ℝ, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law (equalityReadout ℝ) (falseReadout ℝ) rejected_law
  dependence := equalityDependence one_ne_zero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@a_add_b) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis.a_add_b.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicThermalBasis.Rates.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Rates

namespace Generator

private abbrev signature : Signature := equalitySignature Mat

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ}, 0 ≤ r → ∀ k : Index,
    W.readout () () (generator r (direction r k)) ((degree k : ℂ) • direction r k)

private theorem rejected_law : ¬ arena.Law (falseReadout Mat) := by
  intro h
  exact h (r := 1) zero_le_one (0, 0)

def family : Registration arena (type_of% @generator_direction) where
  actual := equalityReadout Mat
  bridge := Iff.rfl
  variation := ⟨@generator_direction, falseReadout Mat, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law (equalityReadout Mat) (falseReadout Mat) rejected_law
  dependence := equalityDependence one_ne_zero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@generator_direction) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis.generator_direction.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicThermalBasis.Generator.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis
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

end Generator

namespace GeneratorLinear

private abbrev signature : Signature := equalitySignature Mat

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ (r : ℝ) (X : Mat), W.readout () () (generatorLinear r X) (generator r X)

private theorem rejected_law : ¬ arena.Law (falseReadout Mat) := by
  intro h
  exact h 1 0

def family : Registration arena (type_of% @generatorLinear_apply) where
  actual := equalityReadout Mat
  bridge := Iff.rfl
  variation := ⟨@generatorLinear_apply, falseReadout Mat, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law (equalityReadout Mat) (falseReadout Mat) rejected_law
  dependence := equalityDependence one_ne_zero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@generatorLinear_apply) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis.generatorLinear_apply.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicThermalBasis.GeneratorLinear.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end GeneratorLinear

namespace Modular

private abbrev signature : Signature := equalitySignature Mat

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ}, r ≠ 0 → ∀ k : Index,
    W.readout () () (D r * direction r k)
      (modularEigenvalue r (charge k) • (direction r k * D r))

private theorem rejected_law : ¬ arena.Law (falseReadout Mat) := by
  intro h
  exact h (r := 1) one_ne_zero (0, 0)

def family : Registration arena (type_of% @modular_direction) where
  actual := equalityReadout Mat
  bridge := Iff.rfl
  variation := ⟨@modular_direction, falseReadout Mat, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law (equalityReadout Mat) (falseReadout Mat) rejected_law
  dependence := equalityDependence one_ne_zero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@modular_direction) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis.modular_direction.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicThermalBasis.Modular.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis
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

end Modular

namespace ModularLinear

private abbrev signature : Signature := equalitySignature Mat

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ}, 0 < r → ∀ k : Index,
    W.readout () () (modularLinear r (direction r k))
      (modularEigenvalue r (charge k) • direction r k)

private theorem rejected_law : ¬ arena.Law (falseReadout Mat) := by
  intro h
  exact h (r := 1) zero_lt_one (0, 0)

def family : Registration arena (type_of% @modularLinear_direction) where
  actual := equalityReadout Mat
  bridge := Iff.rfl
  variation := ⟨@modularLinear_direction, falseReadout Mat, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law (equalityReadout Mat) (falseReadout Mat) rejected_law
  dependence := equalityDependence one_ne_zero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@modularLinear_direction) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis.modularLinear_direction.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicThermalBasis.ModularLinear.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis
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

end ModularLinear

namespace Expansion

private abbrev signature : Signature := equalitySignature Mat

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ}, 0 ≤ r → ∀ X : Mat,
    W.readout () () (∑ k : Index, coefficient r X k • direction r k) X

private theorem rejected_law : ¬ arena.Law (falseReadout Mat) := by
  intro h
  exact h (r := 1) zero_le_one 0

def family : Registration arena (type_of% @expansion) where
  actual := equalityReadout Mat
  bridge := Iff.rfl
  variation := ⟨@expansion, falseReadout Mat, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law (equalityReadout Mat) (falseReadout Mat) rejected_law
  dependence := equalityDependence one_ne_zero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@expansion) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis.expansion.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicThermalBasis.Expansion.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis
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

end Expansion

namespace BasisApply

private abbrev signature : Signature := equalitySignature Mat

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ} (hr : 0 ≤ r) (k : Index),
    W.readout () () (basis r hr k) (direction r k)

private theorem rejected_law : ¬ arena.Law (falseReadout Mat) := by
  intro h
  exact h (r := 1) zero_le_one (0, 0)

def family : Registration arena (type_of% @basis_apply) where
  actual := equalityReadout Mat
  bridge := Iff.rfl
  variation := ⟨@basis_apply, falseReadout Mat, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law (equalityReadout Mat) (falseReadout Mat) rejected_law
  dependence := equalityDependence one_ne_zero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@basis_apply) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis.basis_apply.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicThermalBasis.BasisApply.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis
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

end BasisApply

namespace BasisCoordinates

private abbrev signature : Signature := equalitySignature ℂ

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ} (hr : 0 ≤ r) (X : Mat) (k : Index),
    W.readout () () ((basis r hr).repr X k) (coefficient r X k)

private theorem rejected_law : ¬ arena.Law (falseReadout ℂ) := by
  intro h
  exact h (r := 1) zero_le_one 0 (0, 0)

def family : Registration arena (type_of% @basis_repr) where
  actual := equalityReadout ℂ
  bridge := Iff.rfl
  variation := ⟨@basis_repr, falseReadout ℂ, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law (equalityReadout ℂ) (falseReadout ℂ) rejected_law
  dependence := equalityDependence one_ne_zero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@basis_repr) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis.basis_repr.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicThermalBasis.BasisCoordinates.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis
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

end BasisCoordinates

namespace GeneratorExpansion

private abbrev signature : Signature := equalitySignature Mat

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ}, 0 ≤ r → ∀ X : Mat,
    W.readout () () (generator r X)
      (∑ k : Index, ((degree k : ℂ) * coefficient r X k) • direction r k)

private theorem rejected_law : ¬ arena.Law (falseReadout Mat) := by
  intro h
  exact h (r := 1) zero_le_one 0

def family : Registration arena (type_of% @generator_expansion) where
  actual := equalityReadout Mat
  bridge := Iff.rfl
  variation := ⟨@generator_expansion, falseReadout Mat, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law (equalityReadout Mat) (falseReadout Mat) rejected_law
  dependence := equalityDependence one_ne_zero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@generator_expansion) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis.generator_expansion.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicThermalBasis.GeneratorExpansion.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis
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

end GeneratorExpansion

namespace HighChargeEntries

private abbrev signature : Signature := equalitySignature Mat

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ r : ℝ, W.readout () () (highChargeHermitian r)
    (single (0,0) (1,1) 1 + single (1,1) (0,0) 1)

private theorem rejected_law : ¬ arena.Law (falseReadout Mat) := by
  intro h
  exact h 1

def family : Registration arena (type_of% @highChargeHermitian_eq) where
  actual := equalityReadout Mat
  bridge := Iff.rfl
  variation := ⟨@highChargeHermitian_eq, falseReadout Mat, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law (equalityReadout Mat) (falseReadout Mat) rejected_law
  dependence := equalityDependence one_ne_zero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@highChargeHermitian_eq) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis.highChargeHermitian_eq.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicThermalBasis.HighChargeEntries.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end HighChargeEntries

namespace HighChargeGenerator

private abbrev signature : Signature := equalitySignature Mat

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {r : ℝ}, 0 ≤ r →
    W.readout () () (generator r (highChargeHermitian r)) ((2 : ℂ) • highChargeHermitian r)

private theorem rejected_law : ¬ arena.Law (falseReadout Mat) := by
  intro h
  exact h (r := 1) zero_le_one

def family : Registration arena (type_of% @generator_highChargeHermitian) where
  actual := equalityReadout Mat
  bridge := Iff.rfl
  variation := ⟨@generator_highChargeHermitian, falseReadout Mat, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law (equalityReadout Mat) (falseReadout Mat) rejected_law
  dependence := equalityDependence one_ne_zero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@generator_highChargeHermitian) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis.generator_highChargeHermitian.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicThermalBasis.HighChargeGenerator.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end HighChargeGenerator

namespace ChargeBound

private abbrev signature : Signature := equalitySignature ℤ

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ k : Index, W.readout () () |charge k| (degree k : ℤ)

private theorem rejected_law : ¬ arena.Law (falseReadout ℤ) := by
  intro h
  exact h (0, 0)

def family : Registration arena (type_of% @abs_charge_le_degree) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@abs_charge_le_degree, falseReadout ℤ, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual (falseReadout ℤ) rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have hn : (1 : ℤ) ≤ 0 := Eq.mp (congrFun h 0) le_rfl
    omega

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@abs_charge_le_degree) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis.abs_charge_le_degree.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicThermalBasis.ChargeBound.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ChargeBound

namespace HighChargeNonzero

private abbrev signature : Signature := equalitySignature Mat

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≠ y) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ r : ℝ, W.readout () () (highChargeHermitian r) 0

private theorem rejected_law : ¬ arena.Law (falseReadout Mat) := by
  intro h
  exact h 1

def family : Registration arena (type_of% @highChargeHermitian_ne_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@highChargeHermitian_ne_zero, falseReadout Mat, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual (falseReadout Mat) rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    exact (Eq.mpr (congrFun h 0) (one_ne_zero : (1 : Mat) ≠ 0)) rfl

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@highChargeHermitian_ne_zero) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis.highChargeHermitian_ne_zero.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicThermalBasis.HighChargeNonzero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≠ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end HighChargeNonzero

namespace HighChargeHermitian

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Star ℂ) (fun _ => Mat → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ conjugation => @Matrix.IsHermitian ℂ (Fin 2 × Fin 2) conjugation) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ r : ℝ, W.readout () () (inferInstance : Star ℂ) (highChargeHermitian r)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1

def family : Registration arena (type_of% @highChargeHermitian_isHermitian) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@highChargeHermitian_isHermitian, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    let X : Mat := fun _ _ => Complex.I
    have hnot : ¬ X.IsHermitian := by
      intro h
      have he := congrArg (fun M : Mat => M (0,0) (0,0)) h.eq
      change star Complex.I = Complex.I at he
      have him := congrArg Complex.im he
      norm_num [Complex.star_def] at him
    have hyes : @Matrix.IsHermitian ℂ (Fin 2 × Fin 2) ⟨id⟩ X := rfl
    refine ⟨(), (inferInstance : Star ℂ), ⟨id⟩, ?_⟩
    intro h
    have he := congrFun h X
    change X.IsHermitian = @Matrix.IsHermitian ℂ (Fin 2 × Fin 2) ⟨id⟩ X at he
    exact hnot (Eq.mpr he hyes)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@highChargeHermitian_isHermitian) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis.highChargeHermitian_isHermitian.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicThermalBasis.HighChargeHermitian.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ conjugation => @Matrix.IsHermitian ℂ (Fin 2 × Fin 2) conjugation) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicThermalBasis
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end HighChargeHermitian

end Reg.D5.S3.Quantum.Semigroups.WuCubicThermalBasis
