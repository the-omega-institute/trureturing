import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing

/-! Source-bound audits of the singleton-pair bounds and their physical attainment. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
  (Mat frameVector frameWeight oddProbability)
open _root_.D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing

namespace Reg.D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def le : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def ge : Realization signature :=
  realize signature (fun _ _ x y => x ≥ y) (fun e => nomatch e)

private def equal : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def less : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

private def reverseStrict : Realization signature :=
  realize signature (fun _ _ x y => y < x) (fun e => nomatch e)

private theorem le_dependence : ObservationalDependence signature le := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (not_le_of_gt zero_lt_one) (Eq.mp (congrFun h 0) (le_rfl : (0 : ℝ) ≤ 0))

private theorem ge_dependence : ObservationalDependence signature ge := by
  intro role
  refine ⟨(), 1, 0, ?_⟩
  intro h
  exact (not_le_of_gt zero_lt_one) (Eq.mp (congrFun h 1) (le_rfl : (1 : ℝ) ≤ 1))

private theorem equal_dependence : ObservationalDependence signature equal := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact one_ne_zero (show (1 : ℝ) = 0 from Eq.mp (congrFun h 0) rfl)

namespace RadicalBound

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : unitary Mat) (i j : Fin 4),
    let t := oddProbability (frameVector U i)
    let s := oddProbability (frameVector U j)
    let P := Real.sqrt ((1 - t) * s)
    let Q := Real.sqrt (t * (1 - s))
    R.readout () () ((P - Q) ^ 2) (frameWeight U i j + frameWeight U j i)

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  exact (not_lt_of_ge (singletonPairWeight_ge_radical 1 0 1)) (h 1 0 1)

def family : Registration arena (type_of% @singletonPairWeight_ge_radical) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@singletonPairWeight_ge_radical, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@singletonPairWeight_ge_radical) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing.singletonPairWeight_ge_radical.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing.RadicalBound.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing
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

end RadicalBound

namespace ProductBound

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : unitary Mat) (i j : Fin 4),
    let t := oddProbability (frameVector U i)
    let s := oddProbability (frameVector U j)
    R.readout () () (2 * (t + s) * (frameWeight U i j + frameWeight U j i)) ((t - s) ^ 2)

private theorem rejected_law : ¬ arena.Law less := by
  intro h
  exact (not_lt_of_ge (singletonPairWeight_ge_product 1 0 1)) (h 1 0 1)

def family : Registration arena (type_of% @singletonPairWeight_ge_product) where
  actual := ge
  bridge := Iff.rfl
  variation := ⟨@singletonPairWeight_ge_product, less, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law ge less rejected_law
  dependence := ge_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@singletonPairWeight_ge_product) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing.singletonPairWeight_ge_product.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing.ProductBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≥ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing
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

end ProductBound

namespace Attainment

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {t s : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
    ∃ U : unitary Mat,
      oddProbability (frameVector U 0) = t ∧
      oddProbability (frameVector U 1) = s ∧
      R.readout () () (frameWeight U 0 1 + frameWeight U 1 0)
        ((Real.sqrt ((1 - t) * s) - Real.sqrt (t * (1 - s))) ^ 2)

private theorem rejected_law : ¬ arena.Law less := by
  intro h
  have ht : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hs : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨U, h₀, h₁, hpayoff⟩ := h ht hs
  have hlower := singletonPairWeight_ge_radical U 0 1
  dsimp only at hlower
  rw [h₀, h₁] at hlower
  exact (not_lt_of_ge hlower) hpayoff

def family : Registration arena (type_of% @singletonPairWeight_radical_attained) where
  actual := equal
  bridge := Iff.rfl
  variation := ⟨@singletonPairWeight_radical_attained, less, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law equal less rejected_law
  dependence := equal_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@singletonPairWeight_radical_attained) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing.singletonPairWeight_radical_attained.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing.Attainment.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Attainment

end Reg.D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing
