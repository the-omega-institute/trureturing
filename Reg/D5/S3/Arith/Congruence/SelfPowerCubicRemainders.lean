import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Congruence.SelfPowerCubicRemainders
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Arith.Congruence.SelfPowerQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.Congruence.SelfPowerCubicRemainders
open _root_.D5.S3.Arith.Congruence.SelfPowerCubicRemainders
namespace Blocks

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ) (fun _ => ℤ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ p y => tail (6*p.1+p.2) y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (h t : ℕ) (y : ℤ),
    (y^3+1) ∣ R.readout () ⟨h,t⟩ y - (3*(h : ℤ)*(1+y+y^2)+tail t y)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h 0 0 1
  norm_num [rejected, realize, tail] at bad

def registration : Registration arena (type_of% @tail_blocks) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tail_blocks, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨0,3⟩, 0, 1, ?_⟩
    norm_num [actual, realize, tail, Finset.sum_range_succ]

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Congruence.SelfPowerCubicRemainders.tail_blocks) (Realization signature) Unit Unit where
  unitName := `SelfPowerCubicRemainders.tail_blocks.audit
  realizationName := `Reg.D5.S3.Arith.Congruence.SelfPowerCubicRemainders.Blocks.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p y => tail (6*p.1+p.2) y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Congruence.SelfPowerCubicRemainders
    definition := none
    coordinates := #[0,1]
    readouts := #[{ path := #["body","body","body","arg","fn","arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Blocks

namespace Full

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)
def rejectLeft : Realization signature :=
  realize signature (fun role _ n => if role then a n else 0) (fun e => nomatch e)
def rejectRight : Realization signature :=
  realize signature (fun role _ n => if role then 0 else a n) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 2 < n →
    ((n : ℤ)+1)^2*R.readout false () n = numerator n ∧
    2*(R.readout true () n % ((n : ℤ)^3-1)) = twiceR n
private theorem left_fails : ¬ arena.Law rejectLeft := by
  intro h
  have bad := (h 3 (by decide)).1
  norm_num [rejectLeft, realize, numerator] at bad
private theorem right_fails : ¬ arena.Law rejectRight := by
  intro h
  have bad := (h 3 (by decide)).2
  norm_num [rejectRight, realize, twiceR] at bad

def registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejectLeft, left_fails⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      · refine ⟨rejectLeft, ?_, rfl, left_fails⟩
        intro j hj
        cases j
        · exact (hj rfl).elim
        · rfl
      · refine ⟨rejectRight, ?_, rfl, right_fails⟩
        intro j hj
        cases j
        · rfl
        · exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 3, 4, ?_⟩
    change a 3 ≠ a 4
    norm_num [a, numerator]

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Congruence.SelfPowerCubicRemainders.result) (Realization signature) Unit Unit where
  unitName := `SelfPowerCubicRemainders.result.audit
  realizationName := `Reg.D5.S3.Arith.Congruence.SelfPowerCubicRemainders.Full.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Congruence.SelfPowerCubicRemainders
    definition := some { owner := `D5.S3.Arith.Congruence.SelfPowerCubicRemainders, name := `D5.S3.Arith.Congruence.SelfPowerCubicRemainders.claim, path := #[] }
    coordinates := #[]
    readouts := #[{ path := #["body","body","fn","arg","fn","arg","arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body","body","arg","fn","arg","arg","fn","arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Full
end Reg.D5.S3.Arith.Congruence.SelfPowerCubicRemainders
end
