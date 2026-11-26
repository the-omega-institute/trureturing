import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuCubicRankTwoCut

/-! Source-bound audits of the directed cut estimates and their attainment. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap (Mat frameWeight)
open _root_.D5.S3.Quantum.Semigroups.WuCubicOccupationEnvelope (edgeSum)
open _root_.D5.S3.Quantum.Semigroups.WuCubicRankTwoCut

namespace Reg.D5.S3.Quantum.Semigroups.WuCubicRankTwoCut

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def le : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def reverseStrict : Realization signature :=
  realize signature (fun _ _ x y => y < x) (fun e => nomatch e)

private def equal : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def falseEquality : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem le_dependence : ObservationalDependence signature le := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (not_le_of_gt zero_lt_one) (Eq.mp (congrFun h 0) (le_rfl : (0 : ℝ) ≤ 0))

private theorem equality_dependence : ObservationalDependence signature equal := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact one_ne_zero (show (1 : ℝ) = 0 from Eq.mp (congrFun h 0) rfl)

namespace CutBound

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ U : unitary Mat,
    let a := cutEmpty U
    let b := cutFull U
    let t := cutEvenOffset U
    let g := cutImbalance U
    R.readout () () (1 + t ^ 2 - g - 2 * Real.sqrt (a * b * ((1 - a) * (1 - b))))
      (reverseCutWeight U) ∧
    1 + t ^ 2 + g - 2 * Real.sqrt (a * b * ((1 - a) * (1 - b))) ≤ forwardCutWeight U

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  exact (not_lt_of_ge (cutWeight_ge_sqrt 1).1) (h 1).1

def family : Registration arena (type_of% @cutWeight_ge_sqrt) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@cutWeight_ge_sqrt, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cutWeight_ge_sqrt) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicRankTwoCut.cutWeight_ge_sqrt.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicRankTwoCut.CutBound.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicRankTwoCut
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CutBound

namespace Attainment

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b : ℝ}, a ∈ Set.Icc 0 1 → b ∈ Set.Icc 0 1 →
    ∃ U : unitary Mat, R.readout () () (cutEmpty U) a ∧ cutFull U = b ∧
      reverseCutWeight U =
        1 + (a + b - 1) ^ 2 - (a - b) - 2 * Real.sqrt (a * b * ((1 - a) * (1 - b))) ∧
      forwardCutWeight U =
        1 + (a + b - 1) ^ 2 + (a - b) - 2 * Real.sqrt (a * b * ((1 - a) * (1 - b)))

private theorem rejected_law : ¬ arena.Law falseEquality := by
  intro h
  have hzero : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨_, hfalse, _⟩ := h hzero hzero
  exact hfalse

def family : Registration arena (type_of% @cutWeight_sqrt_attained) where
  actual := equal
  bridge := Iff.rfl
  variation := ⟨@cutWeight_sqrt_attained, falseEquality, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law equal falseEquality rejected_law
  dependence := equality_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cutWeight_sqrt_attained) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicRankTwoCut.cutWeight_sqrt_attained.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicRankTwoCut.Attainment.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicRankTwoCut
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "fn", "arg",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Attainment

namespace ReversePenalty

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : unitary Mat) {u : Fin 4 → ℝ}, Monotone u →
    let a := cutEmpty U
    let b := cutFull U
    R.readout () () ((u 2 - u 1) ^ 3 *
      (1 + cutEvenOffset U ^ 2 - cutImbalance U -
        2 * Real.sqrt (a * b * ((1 - a) * (1 - b)))))
      (edgeSum (fun i j => frameWeight U j i * (u j - u i) ^ 3))

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  have hu : Monotone (fun _ : Fin 4 => (0 : ℝ)) := monotone_const
  exact (not_lt_of_ge (reverseCubicPenalty_ge_sqrt 1 hu)) (h 1 hu)

def family : Registration arena (type_of% @reverseCubicPenalty_ge_sqrt) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@reverseCubicPenalty_ge_sqrt, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@reverseCubicPenalty_ge_sqrt) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicRankTwoCut.reverseCubicPenalty_ge_sqrt.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicRankTwoCut.ReversePenalty.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicRankTwoCut
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

end ReversePenalty

end Reg.D5.S3.Quantum.Semigroups.WuCubicRankTwoCut
