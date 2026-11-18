import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
universe u

private def emptySystem (J : Type u) : ExchangeSystem J where
  base := ∅
  neg := fun _ => ∅
  pos := fun _ => ∅
  base_prime := by simp
  neg_subset := by simp
  pos_prime := by simp
  pos_base := by simp
  neg_disjoint := by intro i j hij; simp
  pos_disjoint := by intro i j hij; simp

private def emptyChoices (J : Type u) [Fintype J] [DecidableEq J] :
    Choices (emptySystem J) (fun _ => 0) :=
  ⟨fun _ => ⟨∅, by simp [emptySystem]⟩, fun _ => ⟨∅, by simp [emptySystem]⟩⟩

namespace Injection

abbrev signature : Signature where
  Params := Type u
  State A := A → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f => Function.Injective f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (E : ExchangeSystem J) (h : J → ℕ),
    R.readout () (Choices E h) (value E h)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (J := PUnit) (emptySystem PUnit) (fun _ => 0)

def family : Registration arena (type_of% @exchange_value_injective.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exchange_value_injective, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{u} ℕ, (fun a => a.down), (fun _ => 0), ?_⟩
    intro he
    have hi : Function.Injective (fun a : ULift.{u} ℕ => a.down) :=
      fun _ _ hh => ULift.ext hh
    have hc : Function.Injective (fun _ : ULift.{u} ℕ => (0 : ℕ)) := Eq.mp he hi
    have hh : (0 : ℕ) = 1 := congrArg ULift.down (@hc ⟨0⟩ ⟨1⟩ rfl)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,u+1,u,0,0,0,0}
    (@exchange_value_injective.{u}) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange.exchange_value_injective.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange.Injection.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Injection

namespace Omega

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (E : ExchangeSystem J) (h : J → ℕ) (z : Choices E h),
    R.readout () () (ArithmeticFunction.cardDistinctFactors (value E h z)) E.base.card

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (J := PUnit) (emptySystem PUnit) (fun _ => 0) (emptyChoices PUnit)

def family : Registration arena (type_of% @omega_exchange_value.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@omega_exchange_value, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), 1, ?_⟩
    intro he
    have hh : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@omega_exchange_value.{u}) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange.omega_exchange_value.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange.Omega.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
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

end Omega

namespace Card

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (E : ExchangeSystem J) (h : J → ℕ),
    R.readout () () (Fintype.card (Choices E h))
      (∏ i, (E.neg i).card.choose (h i) * (E.pos i).card.choose (h i))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (J := PUnit) (emptySystem PUnit) (fun _ => 0)

def family : Registration arena (type_of% @card_exchange_choices.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@card_exchange_choices, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), 1, ?_⟩
    intro he
    have hh : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@card_exchange_choices.{u}) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange.card_exchange_choices.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange.Card.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
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

end Card

namespace LogCost

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (E : ExchangeSystem J) (h : J → ℕ) (P D s : ℝ) (t : J → ℝ)
    (hbase : ∑ p ∈ E.base, log (p : ℝ) ≤ P - D)
    (hneg : ∀ i p, p ∈ E.neg i → log P - t i / s ≤ log (p : ℝ))
    (hpos : ∀ i p, p ∈ E.pos i → log (p : ℝ) ≤ log P + t i / s)
    (z : Choices E h), R.readout () () (log (value E h z : ℝ))
      (P - D + (2 / s) * ∑ i, t i * (h i : ℝ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (J := PUnit) (emptySystem PUnit) (fun _ => 0) 0 0 1 (fun _ => 0)
    (by simp [emptySystem]) (by simp [emptySystem]) (by simp [emptySystem])
    (emptyChoices PUnit)

def family : Registration arena (type_of% @log_exchange_value_le.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@log_exchange_value_le, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@log_exchange_value_le.{u}) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange.log_exchange_value_le.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange.LogCost.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LogCost

namespace TailBound

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (E : ExchangeSystem J) (h : J → ℕ) (P D s : ℝ) (t : J → ℝ) (lambda x : ℝ)
    (hbase : ∑ p ∈ E.base, log (p : ℝ) ≤ P - D)
    (hneg : ∀ i p, p ∈ E.neg i → log P - t i / s ≤ log (p : ℝ))
    (hpos : ∀ i p, p ∈ E.pos i → log (p : ℝ) ≤ log P + t i / s)
    (hbudget : (2 / s) * ∑ i, t i * (h i : ℝ) ≤ D)
    (hthreshold : threshold lambda x < (E.base.card : ℝ))
    (hP : P ≤ log x) (hx : 0 < x),
    R.readout () () (∏ i, (E.neg i).card.choose (h i) * (E.pos i).card.choose (h i))
      (tailCount lambda x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (J := PUnit) (emptySystem PUnit) (fun _ => 0) 0 0 1 (fun _ => 0)
    (-2) (exp (exp 1)) (by simp [emptySystem]) (by simp [emptySystem])
    (by simp [emptySystem]) (by simp)
    (by simp only [emptySystem, card_empty, Nat.cast_zero, threshold, scale, log_exp, div_one]
        have := exp_pos (1 : ℝ)
        linarith)
    (by simpa only [log_exp] using (exp_pos (1 : ℝ)).le) (exp_pos _)

def family : Registration arena (type_of% @balanced_exchange_bound.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@balanced_exchange_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), 1, ?_⟩
    intro he
    have hh : (1 : ℕ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@balanced_exchange_bound.{u}) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange.balanced_exchange_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange.TailBound.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TailBound

end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
