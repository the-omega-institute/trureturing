import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.ExceptionCount.Counting
import Reg.Support.SingleDependentReadout

/-! Source families for distinct-prime counting transfers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail
open _root_.D5.S3.Arith.Robin.Analytic.ExceptionCount.Counting

namespace Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.Counting

namespace RelaxedTail

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {epsilon : ℝ}, 0 < epsilon →
    ∃ eta : ℝ, 0 < eta ∧ ∀ᶠ x : ℝ in atTop,
      R.readout () () (tailCount (-eta) x : ℝ) (exp ((C0 + epsilon) * scale x))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨eta, heta, hfalse⟩ := h (epsilon := 1) (by norm_num)
  obtain ⟨x, hx⟩ := hfalse.exists
  exact hx

def family : Registration arena (type_of% @relaxed_tail_upper) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@relaxed_tail_upper, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@relaxed_tail_upper) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.ExceptionCount.Counting.relaxed_tail_upper.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.Counting.RelaxedTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.ExceptionCount.Counting
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RelaxedTail

namespace DyadicCover

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (E : ℕ → Prop) [DecidablePred E] (N J : ℕ) (lambda : ℝ),
    (∀ j : ℕ, J < j → j ≤ Nat.clog 2 N →
      ∀ n : ℕ, (2 : ℝ) ^ j / 2 < n → (n : ℝ) ≤ (2 : ℝ) ^ j → E n →
        threshold lambda ((2 : ℝ) ^ j) <
          (ArithmeticFunction.cardDistinctFactors n : ℝ)) →
    R.readout () () ((Icc 1 N).filter E).card
      (2 ^ J + ∑ j ∈ Icc (J + 1) (Nat.clog 2 N), tailCount lambda ((2 : ℝ) ^ j))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (fun _ => False) 1 1 0 (by intros; contradiction)

def family : Registration arena (type_of% @dyadic_cover_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@dyadic_cover_count, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), 1, ?_⟩
    intro he
    have hh : (1 : ℕ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@dyadic_cover_count) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.ExceptionCount.Counting.dyadic_cover_count.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.Counting.DyadicCover.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.ExceptionCount.Counting
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

end DyadicCover

end Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.Counting
