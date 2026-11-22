import D5.S3.Arith.Robin.PriceRecord.FixedBIntegerClock
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source registration for the target price in the exact integer clock. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.FixedBIntegerClock

open Filter Real LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedBIntegerClock
  (price targetPrice inverseClock reference exists_fixedB_integerClock)

abbrev signature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ e => targetPrice e) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ε : ℝ}, 0 < ε →
    ∃ clock : ℝ → ℤ → ℝ, clock 0 = reference ∧
      ∀ B : ℝ, Tendsto (clock B) atTop atTop ∧ ∃ S : ℝ, 0 < S ∧
        ∀ᶠ e : ℤ in atTop,
          S ≤ clock B e ∧ price ε B (clock B e) = R.readout () () e ∧
          inverseClock ε B (clock B e) = (e : ℝ) ∧ |clock B e - clock 0 e| ≤ 1 ∧
            ∀ x : ℝ, S ≤ x → price ε B x = targetPrice e → x = clock B e

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨clock, _, hclock⟩ := h (ε := 1) zero_lt_one
  obtain ⟨_, S, hS, hlate⟩ := hclock 0
  obtain ⟨e, he⟩ := hlate.exists
  have hL : 0 < clock 0 e := hS.trans_le he.1
  have hp : 0 < price 1 0 (clock 0 e) := by
    unfold price
    simp only [zero_mul, sub_zero]
    exact div_pos (mul_pos (log_pos (by norm_num)) (exp_pos _)) hL
  have hEq := he.2.1
  change price 1 0 (clock 0 e) = -1 at hEq
  linarith only [hp, hEq]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change targetPrice 0 ≠ targetPrice 1
  have hz : targetPrice 0 = log (3 / 2) := by norm_num [targetPrice]
  have ho : targetPrice 1 = log (7 / 6) := by norm_num [targetPrice]
  rw [hz, ho]
  exact ne_of_gt (log_lt_log (by norm_num) (by norm_num))

def family : Registration arena (type_of% (@exists_fixedB_integerClock)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_fixedB_integerClock, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_fixedB_integerClock) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.FixedBIntegerClock.exists_fixedB_integerClock.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FixedBIntegerClock.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ e => targetPrice e) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.FixedBIntegerClock
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "arg", "arg", "body",
        "arg", "fn", "arg", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.PriceRecord.FixedBIntegerClock
