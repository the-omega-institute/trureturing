import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Congruence.SelfPowerQuotient
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Arith.Congruence.SelfPowerQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.Congruence.SelfPowerQuotient

namespace Tail
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () n = (-1 : ℤ)^n*(1-tail (n+1) (-(n : ℤ)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h 0
  norm_num [rejected, realize, tail, numerator] at bad

def registration : Registration arena (type_of% @_root_.D5.S3.Arith.Congruence.SelfPowerQuotient.quotient_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.Congruence.SelfPowerQuotient.quotient_tail, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    norm_num [a, numerator]

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Congruence.SelfPowerQuotient.quotient_tail) (Realization signature) Unit Unit where
  unitName := `SelfPowerQuotient.quotient_tail.audit
  realizationName := `Reg.D5.S3.Arith.Congruence.SelfPowerQuotient.Tail.registration
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
    owner := `D5.S3.Arith.Congruence.SelfPowerQuotient
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body","fn","arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Tail

namespace Exact
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, ((n : ℤ)+1)^2 * R.readout () () n = numerator n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h 0
  norm_num [rejected, realize, tail, numerator] at bad

def registration : Registration arena (type_of% @_root_.D5.S3.Arith.Congruence.SelfPowerQuotient.exact_quotient) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.Congruence.SelfPowerQuotient.exact_quotient, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    norm_num [a, numerator]

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Congruence.SelfPowerQuotient.exact_quotient) (Realization signature) Unit Unit where
  unitName := `SelfPowerQuotient.exact_quotient.audit
  realizationName := `Reg.D5.S3.Arith.Congruence.SelfPowerQuotient.Exact.registration
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
    owner := `D5.S3.Arith.Congruence.SelfPowerQuotient
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body","fn","arg","arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Exact
end Reg.D5.S3.Arith.Congruence.SelfPowerQuotient
end
