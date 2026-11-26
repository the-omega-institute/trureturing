import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap

/-! Source-bound audits of the occupation cap, its frame identities, and the physical gap. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap

namespace Reg.D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def le : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def less : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

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

private theorem less_dependence : ObservationalDependence signature less := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (lt_irrefl (1 : ℝ)) (Eq.mp (congrFun h 1) (zero_lt_one : (0 : ℝ) < 1))

private theorem equality_dependence : ObservationalDependence signature equal := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact one_ne_zero (show (1 : ℝ) = 0 from Eq.mp (congrFun h 0) rfl)

private abbrev WeightTable := Fin 4 → Fin 4 → ℝ

private abbrev weightSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => WeightTable) (fun _ => WeightTable → Prop)

private def weightEqual : Realization weightSignature :=
  realize weightSignature (fun _ _ x y => x = y) (fun e => nomatch e)

private def trueEquality : Realization weightSignature :=
  realize weightSignature (fun _ _ _ _ => True) (fun e => nomatch e)

private theorem weight_equality_dependence : ObservationalDependence weightSignature weightEqual := by
  intro role
  let zero : WeightTable := fun _ _ => 0
  let one : WeightTable := fun _ _ => 1
  refine ⟨(), zero, one, ?_⟩
  intro h
  have hbad : one = zero := Eq.mp (congrFun h zero) rfl
  exact one_ne_zero (show (1 : ℝ) = 0 from congrFun (congrFun hbad 0) 0)

private def balancedMatrix : Mat :=
  let r := (Real.sqrt (1 / 2 : ℝ) : ℂ)
  !![r, r, 0, 0; r, -r, 0, 0; 0, 0, r, r; 0, 0, r, -r]

private def balancedFrame : unitary Mat := by
  refine ⟨balancedMatrix, Unitary.mem_iff.mpr ⟨?_, ?_⟩⟩
  all_goals
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [balancedMatrix, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply,
        Fin.sum_univ_four, Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.add_re,
        Complex.add_im, Complex.neg_re, Complex.neg_im] <;>
      nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private theorem balancedFrame_even (i : Fin 4) :
    evenProbability (frameVector balancedFrame i) = 1 / 2 := by
  fin_cases i <;>
    norm_num [evenProbability, emptyProbability, fullProbability, frameVector,
      balancedFrame, balancedMatrix, Complex.normSq_neg, Complex.normSq_ofReal, ← pow_two,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]

namespace JumpCap

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x y : Fin 4 → ℂ) {t : ℝ}, 0 < t →
    R.readout () () (jumpWeight x y)
      ((1 + t) * emptyProbability x * oddProbability y +
        (1 + 1 / t) * oddProbability x * fullProbability y)

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  let x : Fin 4 → ℂ := fun _ => 0
  have ht : (0 : ℝ) < 1 := zero_lt_one
  exact (not_lt_of_ge (jumpWeight_le x x ht)) (h x x ht)

def family : Registration arena (type_of% @jumpWeight_le) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@jumpWeight_le, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@jumpWeight_le) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap.jumpWeight_le.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap.JumpCap.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
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

end JumpCap

namespace FrameWeight

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : unitary Mat) (i j : Fin 4),
    R.readout () () (frameWeight U i j) (jumpWeight (frameVector U i) (frameVector U j))

private theorem rejected_law : ¬ arena.Law unequal := by
  intro h
  exact h 1 0 0 (frameWeight_eq_jumpWeight 1 0 0)

def family : Registration arena (type_of% @frameWeight_eq_jumpWeight) where
  actual := equal
  bridge := Iff.rfl
  variation := ⟨@frameWeight_eq_jumpWeight, unequal, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law equal unequal rejected_law
  dependence := equality_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@frameWeight_eq_jumpWeight) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap.frameWeight_eq_jumpWeight.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap.FrameWeight.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
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

end FrameWeight

namespace RowImbalance

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : unitary Mat) (i : Fin 4),
    R.readout () () (rowImbalance (frameWeight U) i)
      (2 * (emptyProbability (frameVector U i) - fullProbability (frameVector U i)))

private theorem rejected_law : ¬ arena.Law unequal := by
  intro h
  exact h 1 0 (frameWeight_rowImbalance 1 0)

def family : Registration arena (type_of% @frameWeight_rowImbalance) where
  actual := equal
  bridge := Iff.rfl
  variation := ⟨@frameWeight_rowImbalance, unequal, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law equal unequal rejected_law
  dependence := equality_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@frameWeight_rowImbalance) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap.frameWeight_rowImbalance.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap.RowImbalance.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
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

end RowImbalance

namespace ImbalanceBound

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : unitary Mat) (i : Fin 4),
    R.readout () () (|rowImbalance (frameWeight U) i|) (2 * evenProbability (frameVector U i))

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  exact (not_lt_of_ge (frameWeight_abs_rowImbalance_le 1 0)) (h 1 0)

def family : Registration arena (type_of% @frameWeight_abs_rowImbalance_le) where
  actual := le
  bridge := Iff.rfl
  variation := ⟨@frameWeight_abs_rowImbalance_le, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law le reverseStrict rejected_law
  dependence := le_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@frameWeight_abs_rowImbalance_le) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap.frameWeight_abs_rowImbalance_le.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap.ImbalanceBound.family
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
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

end ImbalanceBound

namespace UnrealizableTable

private abbrev arena : Arena where
  signature := weightSignature
  Law R := ¬ ∃ U : unitary Mat, R.readout () () (frameWeight U) table ∧
    ∀ i, evenProbability (frameVector U i) = tableOccupation i

private theorem rejected_law : ¬ arena.Law trueEquality := by
  intro h
  exact h ⟨balancedFrame, trivial, balancedFrame_even⟩

def family : Registration arena (type_of% @table_no_unitary_realization) where
  actual := weightEqual
  bridge := Iff.rfl
  variation := ⟨@table_no_unitary_realization, trueEquality, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law weightEqual trueEquality rejected_law
  dependence := weight_equality_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@table_no_unitary_realization) (Realization weightSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap.table_no_unitary_realization.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap.UnrealizableTable.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end UnrealizableTable

namespace PhysicalGap

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : unitary Mat), (∀ i, evenProbability (frameVector U i) = 1 / 2) →
    R.readout () () (1 / 500) (normalizedCubicDeficit (frameWeight U) (frameMoment U))

private theorem rejected_law : ¬ arena.Law reverseStrict := by
  intro h
  exact (lt_asymm (balancedFrame_normalizedCubicDeficit_gt balancedFrame balancedFrame_even))
    (h balancedFrame balancedFrame_even)

def family : Registration arena (type_of% @balancedFrame_normalizedCubicDeficit_gt) where
  actual := less
  bridge := Iff.rfl
  variation := ⟨@balancedFrame_normalizedCubicDeficit_gt, reverseStrict, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law less reverseStrict rejected_law
  dependence := less_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@balancedFrame_normalizedCubicDeficit_gt) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap.balancedFrame_normalizedCubicDeficit_gt.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap.PhysicalGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
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

end PhysicalGap

end Reg.D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
