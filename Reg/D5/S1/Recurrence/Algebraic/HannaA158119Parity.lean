import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Algebraic.HannaA158119Parity
import Reg.Support.SingleDependentReadout

/-! # Source-bound readouts for the original reversion quotient and parity law -/

namespace Reg.D5.S1.Recurrence.Algebraic.HannaA158119Parity
open _root_.D5.S1.Recurrence.Algebraic.HannaA158119Parity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ m => a m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, Odd (R.readout () () m) ↔ m = 0 ∨ ∃ j : ℕ, m = 2 ^ j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := (h 0).mpr (Or.inl rfl)
  change Odd (0 : ℕ) at h0
  exact (by decide : ¬ Odd (0 : ℕ)) h0

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 3, ?_⟩
    change a 0 ≠ a 3
    have h0 : Odd (a 0) := (result 0).mpr (Or.inl rfl)
    have h3 : ¬ Odd (a 3) := by
      intro h
      rcases (result 3).mp h with h | ⟨j, hj⟩
      · omega
      · cases j with
        | zero => norm_num at hj
        | succ j => rw [pow_succ] at hj; omega
    intro h
    exact h3 (h ▸ h0)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    result (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Algebraic.HannaA158119Parity.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA158119Parity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => a m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.HannaA158119Parity
    definition := some {
      owner := `D5.S1.Recurrence.Algebraic.HannaA158119Parity
      name := `D5.S1.Recurrence.Algebraic.HannaA158119Parity.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

abbrev quotientSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => PowerSeries ℤ) (fun _ => PowerSeries ℤ)

def quotientActual : Realization quotientSignature :=
  realize quotientSignature (fun _ _ f => B * f) (fun e => nomatch e)

def quotientRejected : Realization quotientSignature :=
  realize quotientSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev quotientArena : Arena where
  signature := quotientSignature
  Law R := R.readout () () Q = PowerSeries.X

private theorem quotient_rejected_law : ¬ quotientArena.Law quotientRejected := by
  intro h
  change (0 : PowerSeries ℤ) = PowerSeries.X at h
  exact PowerSeries.X_ne_zero h.symm

def quotientFamily : Registration quotientArena (type_of% quotient_equation) where
  actual := quotientActual
  bridge := Iff.rfl
  variation := ⟨quotient_equation, quotientRejected, quotient_rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    quotientArena.Law quotientActual quotientRejected quotient_rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, Q, ?_⟩
    change B * 0 ≠ B * Q
    rw [mul_zero, quotient_equation]
    exact Ne.symm PowerSeries.X_ne_zero

def quotientAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    quotient_equation (Realization quotientSignature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Algebraic.HannaA158119Parity.quotientUnit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA158119Parity.quotientFamily
  realizationSource := none
  generated := false
  arena := .source ⟨quotientArena⟩
  objectArena := .source ⟨quotientArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source quotientArena ⟨quotientFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize quotientSignature (fun _ _ f => B * f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.HannaA158119Parity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms quotientAudit

end
end Reg.D5.S1.Recurrence.Algebraic.HannaA158119Parity
