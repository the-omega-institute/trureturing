import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuCubicCoupledCuts

/-! Source-bound audits of the coupled CAR cut identities and estimates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
  (Mat frameVector frameWeight oddProbability emptyProbability fullProbability)
open _root_.D5.S3.Quantum.Semigroups.WuCubicOccupationEnvelope (sym)
open _root_.D5.S3.Quantum.Semigroups.WuCubicRankTwoCut
open _root_.D5.S3.Quantum.Semigroups.WuCubicCoupledCuts

namespace Reg.D5.S3.Quantum.Semigroups.WuCubicCoupledCuts

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def le : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def reverseStrict : Realization signature :=
  realize signature (fun _ _ x y => y < x) (fun e => nomatch e)

private def equal : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def unequal : Realization signature :=
  realize signature (fun _ _ x y => x ≠ y) (fun e => nomatch e)

private theorem le_dependence : ObservationalDependence signature le := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (not_le_of_gt zero_lt_one) (Eq.mp (congrFun h 0) (le_rfl : (0 : ℝ) ≤ 0))

private theorem equal_dependence : ObservationalDependence signature equal := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact one_ne_zero (show (1 : ℝ) = 0 from Eq.mp (congrFun h 0) rfl)

namespace AdjacentIdentity

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ U : unitary Mat,
    let f := fun i => oddProbability (frameVector U i) * (1 - oddProbability (frameVector U i))
    R.readout () () (lowerAdjacentCutWeight U)
      ((forwardCutWeight U + reverseCutWeight U) / 2 + f 1 - f 0) ∧
    upperAdjacentCutWeight U = (forwardCutWeight U + reverseCutWeight U) / 2 + f 2 - f 3

private theorem rejected_law : ¬ arena.Law unequal := by
  intro h
  exact (h 1).1 (adjacentCutWeight_eq 1).1

def family : Registration arena (type_of% @adjacentCutWeight_eq) where
  actual := equal
  bridge := Iff.rfl
  variation := ⟨@adjacentCutWeight_eq, unequal, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law equal unequal rejected_law
  dependence := equal_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@adjacentCutWeight_eq) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicCoupledCuts.adjacentCutWeight_eq.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicCoupledCuts.AdjacentIdentity.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicCoupledCuts
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end AdjacentIdentity

namespace OffsetFeasibility

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ U : unitary Mat, R.readout () () (|cutEvenOffset U| + |cutImbalance U|) 1

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  exact (not_lt_of_ge (abs_cutEvenOffset_add_abs_cutImbalance_le_one 1)) (h 1)

def family : Registration arena (type_of% @abs_cutEvenOffset_add_abs_cutImbalance_le_one) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@abs_cutEvenOffset_add_abs_cutImbalance_le_one, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@abs_cutEvenOffset_add_abs_cutImbalance_le_one) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicCoupledCuts.abs_cutEvenOffset_add_abs_cutImbalance_le_one.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicCoupledCuts.OffsetFeasibility.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicCoupledCuts
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

end OffsetFeasibility

namespace MiddleSurplus

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : unitary Mat) {lo : ℝ}, 0 ≤ lo → lo < 1 → lo ≤ |cutImbalance U| →
    let u := cutEvenOffset U
    let v := |cutImbalance U|
    R.readout () () (1 + v ^ 2 + 3 * u ^ 2 + (2 * lo ^ 2 / (1 - lo ^ 2)) * u ^ 2)
      (forwardCutWeight U + reverseCutWeight U)

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  have hle := abs_nonneg (cutImbalance 1)
  exact (not_lt_of_ge (middleCutWeight_ge_sqrt_surplus 1 le_rfl zero_lt_one hle))
    (h 1 le_rfl zero_lt_one hle)

def family : Registration arena (type_of% @middleCutWeight_ge_sqrt_surplus) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@middleCutWeight_ge_sqrt_surplus, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@middleCutWeight_ge_sqrt_surplus) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicCoupledCuts.middleCutWeight_ge_sqrt_surplus.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicCoupledCuts.MiddleSurplus.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicCoupledCuts
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MiddleSurplus

namespace AdjacentSurplus

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : unitary Mat) {lo : ℝ}, 0 ≤ lo → lo < 1 → lo ≤ |cutImbalance U| →
    let u := cutEvenOffset U
    let v := |cutImbalance U|
    let f := fun i => oddProbability (frameVector U i) * (1 - oddProbability (frameVector U i))
    let halfCut := (1 + v ^ 2 + 3 * u ^ 2 + (2 * lo ^ 2 / (1 - lo ^ 2)) * u ^ 2) / 2
    R.readout () () (halfCut + f 1 - f 0) (lowerAdjacentCutWeight U) ∧
    halfCut + f 2 - f 3 ≤ upperAdjacentCutWeight U

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  have hle := abs_nonneg (cutImbalance 1)
  exact (not_lt_of_ge (adjacentCutWeight_ge_sqrt_surplus 1 le_rfl zero_lt_one hle).1)
    (h 1 le_rfl zero_lt_one hle).1

def family : Registration arena (type_of% @adjacentCutWeight_ge_sqrt_surplus) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@adjacentCutWeight_ge_sqrt_surplus, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@adjacentCutWeight_ge_sqrt_surplus) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicCoupledCuts.adjacentCutWeight_ge_sqrt_surplus.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicCoupledCuts.AdjacentSurplus.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicCoupledCuts
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end AdjacentSurplus

namespace SignedAdjacentBound

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ U : unitary Mat,
    let t := fun i => oddProbability (frameVector U i)
    let u := -cutEvenOffset U
    let v := |cutImbalance U|
    1 + v ^ 2 + 3 * u ^ 2 ≤ forwardCutWeight U + reverseCutWeight U ∧
    R.readout () () ((1 + v ^ 2) / 2 + (2 * t 0 - 1) * u + u ^ 2 / 2) (lowerAdjacentCutWeight U) ∧
    (1 + v ^ 2) / 2 - (2 * t 3 - 1) * u + u ^ 2 / 2 ≤ upperAdjacentCutWeight U

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  exact (not_lt_of_ge (adjacentCutWeight_ge_signed 1).2.1) (h 1).2.1

def family : Registration arena (type_of% @adjacentCutWeight_ge_signed) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@adjacentCutWeight_ge_signed, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@adjacentCutWeight_ge_signed) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicCoupledCuts.adjacentCutWeight_ge_signed.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicCoupledCuts.SignedAdjacentBound.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicCoupledCuts
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SignedAdjacentBound

namespace MaximumAdjacentBound

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ U : unitary Mat,
    let t := fun i => oddProbability (frameVector U i)
    let q := fun i => max (t i) (1 - t i)
    let v := |cutImbalance U|
    R.readout () () (max (1 - 2 * t 0 * (1 - t 0)) ((1 + v ^ 2) / 2 - (2 * q 0 - 1) * (1 - v)))
      (lowerAdjacentCutWeight U) ∧
    max (1 - 2 * t 3 * (1 - t 3)) ((1 + v ^ 2) / 2 - (2 * q 3 - 1) * (1 - v)) ≤
      upperAdjacentCutWeight U

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  exact (not_lt_of_ge (adjacentCutWeight_ge_max 1).1) (h 1).1

def family : Registration arena (type_of% @adjacentCutWeight_ge_max) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@adjacentCutWeight_ge_max, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@adjacentCutWeight_ge_max) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicCoupledCuts.adjacentCutWeight_ge_max.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicCoupledCuts.MaximumAdjacentBound.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicCoupledCuts
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MaximumAdjacentBound

namespace QuadraticAdjacentBound

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ U : unitary Mat,
    let y := fun i => 1 - 2 * oddProbability (frameVector U i)
    let u := -cutEvenOffset U
    let v := |cutImbalance U|
    R.readout () () (1 / 2 + v ^ 2 / 4 + (y 0 - u) ^ 2 / 4) (lowerAdjacentCutWeight U) ∧
    1 / 2 + v ^ 2 / 4 + (y 3 + u) ^ 2 / 4 ≤ upperAdjacentCutWeight U

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  exact (not_lt_of_ge (adjacentCutWeight_ge_quadratic 1).1) (h 1).1

def family : Registration arena (type_of% @adjacentCutWeight_ge_quadratic) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@adjacentCutWeight_ge_quadratic, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@adjacentCutWeight_ge_quadratic) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicCoupledCuts.adjacentCutWeight_ge_quadratic.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicCoupledCuts.QuadraticAdjacentBound.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicCoupledCuts
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end QuadraticAdjacentBound

namespace EndChargeBound

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ U : unitary Mat,
    let t := fun i => oddProbability (frameVector U i)
    let y := fun i => 1 - 2 * t i
    let u := -cutEvenOffset U
    let v := |cutImbalance U|
    let charge := fun i =>
      emptyProbability (frameVector U i) - fullProbability (frameVector U i)
    R.readout () () (|-charge 0|) (min ((1 + y 0) / 2) (v + (1 - y 0) / 2 - u)) ∧
    |charge 3| ≤ min ((1 + y 3) / 2) (v + (1 - y 3) / 2 + u)

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  exact (not_lt_of_ge (endCutCharge_abs_le 1).1) (h 1).1

def family : Registration arena (type_of% @endCutCharge_abs_le) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@endCutCharge_abs_le, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@endCutCharge_abs_le) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicCoupledCuts.endCutCharge_abs_le.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicCoupledCuts.EndChargeBound.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicCoupledCuts
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end EndChargeBound

namespace RetainedCost

private abbrev arena : Arena where
  signature := signature
  Law realization := ∀ (U : unitary Mat) (A B : Fin 3 → ℝ) (Z₀ Z₂ : ℝ),
    (∀ i, 0 ≤ A i) → (∀ i, 0 ≤ B i) → 0 ≤ Z₀ → 0 ≤ Z₂ →
    let y := fun i => 1 - 2 * oddProbability (frameVector U i)
    let u := -cutEvenOffset U
    let v := |cutImbalance U|
    let L := Z₀ / 2
    let R := Z₂ / 2
    let S := (L + R) / 2
    let W := sym (frameWeight U)
    let charge := fun i =>
      emptyProbability (frameVector U i) - fullProbability (frameVector U i)
    realization.readout () ()
      (A 1 + (Z₀ + Z₂) / 2 + (3 * A 0 + 3 * A 2 - B 0 - B 2) / 2 +
        (A 1 + S) * v ^ 2 - B 1 * v + (3 * A 1 + S) * u ^ 2 -
        (L * y 0 - R * y 3) * u +
        (A 0 + L) * y 0 ^ 2 / 2 + (A 2 + R) * y 3 ^ 2 / 2 -
        (B 0 * y 0 + B 2 * y 3) / 2)
      (A 0 * (W 0 1 + W 0 2 + W 0 3) +
        A 1 * (forwardCutWeight U + reverseCutWeight U) +
        A 2 * (W 0 3 + W 1 3 + W 2 3) +
        B 0 * (-charge 0) + B 1 * (-cutImbalance U) + B 2 * charge 3 +
        Z₀ * lowerAdjacentCutWeight U + Z₂ * upperAdjacentCutWeight U)

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  have hOne : ∀ i : Fin 3, (0 : ℝ) ≤ (fun _ : Fin 3 => 1) i := fun _ => zero_le_one
  exact (not_lt_of_ge (retainedCutCost_ge_quadratic 1 (fun _ => 1) (fun _ => 1) 1 1
    hOne hOne zero_le_one zero_le_one))
    (h 1 (fun _ => 1) (fun _ => 1) 1 1 hOne hOne zero_le_one zero_le_one)

def family : Registration arena (type_of% @retainedCutCost_ge_quadratic) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@retainedCutCost_ge_quadratic, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@retainedCutCost_ge_quadratic) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicCoupledCuts.retainedCutCost_ge_quadratic.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicCoupledCuts.RetainedCost.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicCoupledCuts
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RetainedCost

end Reg.D5.S3.Quantum.Semigroups.WuCubicCoupledCuts
