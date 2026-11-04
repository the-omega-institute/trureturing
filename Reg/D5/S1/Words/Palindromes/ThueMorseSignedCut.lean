import D5.S1.Words.Palindromes.ThueMorseSignedCut
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound models for the literal signed-potential statements. -/

open _root_.D5.S1.Words.Complexity
open _root_.D5.S1.Words.Palindromes.PeriodDoubling
open _root_.D5.S1.Words.Palindromes.ThueMorse
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.Palindromes.ThueMorseSignedCut
noncomputable section
open Classical

abbrev natSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def transitionActual : Realization natSignature :=
  realize natSignature (fun _ _ n => transition n) (fun e => nomatch e)
def transitionBad : Realization natSignature :=
  realize natSignature (fun _ _ _ => 2) (fun e => nomatch e)
abbrev transitionArena : Arena where
  signature := natSignature
  Law R := ∀ n, R.readout () () n = if u_pd n then 0 else 1

theorem transitionBadLaw : ¬ transitionArena.Law transitionBad := by
  intro h
  have hh := h 0
  change 2 = if u_pd 0 then 0 else 1 at hh
  cases hv : u_pd 0 <;> simp [hv] at hh

def transitionRegistration : Registration transitionArena (transitionArena.Law transitionActual) where
  actual := transitionActual
  bridge := Iff.rfl
  variation := ⟨transition_period_doubling, transitionBad, transitionBadLaw⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨transitionBad, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, transitionBadLaw⟩
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change transition 0 ≠ transition 1
    have hz : transition 0 = 1 := by simpa using transition_two_mul 0
    have ho : transition 1 = 0 := by simpa [hz] using transition_two_mul_add_one 0
    rw [hz, ho]
    decide

def cutActual : Realization natSignature :=
  realize natSignature (fun _ _ n => signedWeight (n : ℤ)) (fun e => nomatch e)
def cutBad : Realization natSignature :=
  realize natSignature (fun _ _ n => 2 * n) (fun e => nomatch e)
abbrev cutArena : Arena where
  signature := natSignature
  Law R := ∀ i j : ℕ, i < j → Allowed (factor (j - i) i) →
    R.readout () () j ≤ R.readout () () i + 1

theorem cutBadLaw : ¬ cutArena.Law cutBad := by
  intro h
  have hh := h 0 1 (by omega) (by
    left
    change List.Palindrome [false]
    exact List.Palindrome.singleton false)
  have hbad : (2 : ℕ) ≤ 1 := hh
  omega

def cutRegistration : Registration cutArena (cutArena.Law cutActual) where
  actual := cutActual
  bridge := Iff.rfl
  variation := ⟨allowed_factor_signed_cut, cutBad, cutBadLaw⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨cutBad, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, cutBadLaw⟩
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change signedWeight (0 : ℤ) ≠ signedWeight (1 : ℤ)
    rw [signed_weight_arithmetic.1, signed_weight_arithmetic.2.1]
    omega

abbrev costSignature : Signature where
  Params := Unit
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def costActual : Realization costSignature :=
  realize costSignature (fun _ _ w => combinedLength w) (fun e => nomatch e)
def costBad : Realization costSignature :=
  realize costSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev costArena : Arena where
  signature := costSignature
  Law R := ∀ n : ℕ, signedWeight (n : ℤ) ≤ R.readout () () (factor n 0) ∧
    R.readout () () (factor n 0) ≤ _root_.D5.S1.Words.FridPrefix.PL (factor n 0)

theorem costBadLaw : ¬ costArena.Law costBad := by
  intro h
  have hh := (h 1).1
  change signedWeight 1 ≤ 0 at hh
  rw [signed_weight_arithmetic.2.1] at hh
  omega

def costRegistration : Registration costArena (costArena.Law costActual) where
  actual := costActual
  bridge := Iff.rfl
  variation := ⟨combined_prefix_signed_lower, costBad, costBadLaw⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨costBad, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, costBadLaw⟩
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), factor 0 0, factor 1 0, ?_⟩
    change combinedLength (factor 0 0) ≠ combinedLength (factor 1 0)
    have hz := (combined_prefix_signed_lower 0).2
    have ho := (combined_prefix_signed_lower 1).1
    have hp : _root_.D5.S1.Words.FridPrefix.PL (factor 0 0) = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply Nat.find_le
      exact ⟨[], rfl, rfl, by simp⟩
    rw [hp] at hz
    change signedWeight 1 ≤ combinedLength (factor 1 0) at ho
    rw [signed_weight_arithmetic.2.1] at ho
    omega

noncomputable def registration_transition : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.Palindromes.ThueMorse.transition_period_doubling)
    (type_of% (realize.{0,0,0,0,0} natSignature transitionActual.readout transitionActual.anchor)) Unit Unit := {
  unitName := .str (.str `D5.S1.Words.Palindromes.ThueMorse.transition_period_doubling
    "Reg.D5.S1.Words.Palindromes.ThueMorseSignedCut/transitionArena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S1.Words.Palindromes.ThueMorseSignedCut.transitionRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨transitionArena⟩
  objectArena := .source ⟨transitionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source transitionArena ⟨transitionRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} natSignature transitionActual.readout transitionActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S1.Words.Palindromes.ThueMorseSignedCut, definition := none, coordinates := #[], readouts := #[{ path := #["body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration_transition

noncomputable def registration_cut : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.Palindromes.ThueMorse.allowed_factor_signed_cut)
    (type_of% (realize.{0,0,0,0,0} natSignature cutActual.readout cutActual.anchor)) Unit Unit := {
  unitName := .str (.str `D5.S1.Words.Palindromes.ThueMorse.allowed_factor_signed_cut
    "Reg.D5.S1.Words.Palindromes.ThueMorseSignedCut/cutArena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S1.Words.Palindromes.ThueMorseSignedCut.cutRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨cutArena⟩
  objectArena := .source ⟨cutArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cutArena ⟨cutRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} natSignature cutActual.readout cutActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S1.Words.Palindromes.ThueMorseSignedCut, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }, { path := #["body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration_cut

noncomputable def registration_cost : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.Palindromes.ThueMorse.combined_prefix_signed_lower)
    (type_of% (realize.{0,0,0,0,0} costSignature costActual.readout costActual.anchor)) Unit Unit := {
  unitName := .str (.str `D5.S1.Words.Palindromes.ThueMorse.combined_prefix_signed_lower
    "Reg.D5.S1.Words.Palindromes.ThueMorseSignedCut/costArena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S1.Words.Palindromes.ThueMorseSignedCut.costRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨costArena⟩
  objectArena := .source ⟨costArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source costArena ⟨costRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} costSignature costActual.readout costActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S1.Words.Palindromes.ThueMorseSignedCut, definition := none, coordinates := #[], readouts := #[{ path := #["body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }, { path := #["body", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration_cost

end
end Reg.D5.S1.Words.Palindromes.ThueMorseSignedCut
