import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Congruence.CohnUniformThreeAdic
import Reg.Support.DependentFamily

open D5.S3.Arith.Congruence.CohnUniformThreeAdic
open D5.S3.Arith.Congruence.CohnUniformThreeAdic.Exported
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

namespace Reg.D5.S3.Arith.Congruence.CohnUniformThreeAdic

@[reducible] def signature : Signature where
  Params := ℕ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q ξ => (cohnPolynomial q).eval ξ) (fun a => nomatch a)

def shifted : Realization signature :=
  realize signature (fun _ q ξ => (cohnPolynomial q).eval ξ + 1) (fun a => nomatch a)

def constantOne : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun a => nomatch a)

@[reducible] def congruenceArena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ) (ξ : ℤ), 7 ≤ q → q % 6 = 1 → (3 : ℤ) ∣ ξ →
    (3 : ℤ) ^ (padicValNat 3 (q - 1) + 2) ∣ R.readout () q ξ - 2 ^ (q - 1)

@[reducible] def obstructionArena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ) (ξ : ℤ), 7 ≤ q → q % 6 = 1 → (3 : ℤ) ∣ ξ →
    R.readout () q ξ ≠ 1

theorem shifted_fails : ¬ congruenceArena.Law shifted := by
  intro h
  have bad := h 7 0 (by decide) (by decide) (dvd_zero _)
  change (3 : ℤ) ^ (padicValNat 3 (7 - 1) + 2) ∣
    (cohnPolynomial 7).eval 0 + 1 - 2 ^ (7 - 1) at bad
  have h3 : (3 : ℤ) ∣ (3 : ℤ) ^ (padicValNat 3 (7 - 1) + 2) :=
    dvd_pow_self _ (by omega)
  have contra := h3.trans bad
  norm_num [cohnPolynomial, Finset.sum_range_succ,
    show Nat.choose 7 3 = 35 by decide, show Nat.choose 7 5 = 21 by decide] at contra

theorem constant_one_fails : ¬ obstructionArena.Law constantOne := by
  intro h
  exact h 7 0 (by decide) (by decide) (dvd_zero _) rfl

theorem actual_dependence : actual.readout () 7 0 ≠ actual.readout () 7 3 := by
  change (cohnPolynomial 7).eval 0 ≠ (cohnPolynomial 7).eval 3
  norm_num [cohnPolynomial, Finset.sum_range_succ,
    show Nat.choose 7 3 = 35 by decide, show Nat.choose 7 5 = 21 by decide]

def congruenceRegistration : Registration congruenceArena (congruenceArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cohn_stationary_congruence, shifted, shifted_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨shifted, ?_, rfl, shifted_fails⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    exact ⟨7, 0, 3, actual_dependence⟩

def obstructionRegistration : Registration obstructionArena (obstructionArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cohn_polynomial_ne_one, constantOne, constant_one_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨constantOne, ?_, rfl, constant_one_fails⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    exact ⟨7, 0, 3, actual_dependence⟩

noncomputable def audit_congruence :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@cohn_stationary_congruence)
      (type_of% (realize signature (fun _ q ξ => (cohnPolynomial q).eval ξ) (fun e => nomatch e)))
      (Type) (Unit) := {
  unitName := `CohnUniformThreeAdicCongruence,
  realizationName := `Reg.D5.S3.Arith.Congruence.CohnUniformThreeAdic.congruenceRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨congruenceArena⟩,
  objectArena := .source ⟨congruenceArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source congruenceArena ⟨congruenceRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ q ξ => (cohnPolynomial q).eval ξ) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.Congruence.CohnUniformThreeAdic,
    definition := none, coordinates := #[0],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def audit_obstruction :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@cohn_polynomial_ne_one)
      (type_of% (realize signature (fun _ q ξ => (cohnPolynomial q).eval ξ) (fun e => nomatch e)))
      (Type) (Unit) := {
  unitName := `CohnUniformThreeAdicObstruction,
  realizationName := `Reg.D5.S3.Arith.Congruence.CohnUniformThreeAdic.obstructionRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨obstructionArena⟩,
  objectArena := .source ⟨obstructionArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source obstructionArena ⟨obstructionRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ q ξ => (cohnPolynomial q).eval ξ) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.Congruence.CohnUniformThreeAdic,
    definition := none, coordinates := #[0],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }


end Reg.D5.S3.Arith.Congruence.CohnUniformThreeAdic

open Polynomial
open scoped QuadraticAlgebra

namespace Reg.D5.S3.Arith.Congruence.CohnUniformThreeAdic.Visibility
@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ[X]
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m => (cohnPolynomial (2 * m + 1)).comp (X ^ 2 - 1))
    (fun a => nomatch a)
def zeroFamily : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun a => nomatch a)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, R.readout () () m =
    ((⟨X, 1⟩ : QuadraticAlgebra ℤ[X] (-3) 0) ^ (2 * m + 1)).im

theorem actual_law : arena.Law actual := polynomial_identification

theorem zero_fails : ¬ arena.Law zeroFamily := by
  intro h
  have bad := h 0
  change (0 : ℤ[X]) = _ at bad
  norm_num at bad

theorem actual_dependence : actual.readout () () 0 ≠ actual.readout () () 1 := by
  intro h
  have H := congrArg (Polynomial.eval (0 : ℤ)) h
  norm_num [actual, realize, cohnPolynomial, Finset.sum_range_succ] at H

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, zeroFamily, zero_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroFamily, ?_, rfl, zero_fails⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    exact ⟨(), 0, 1, actual_dependence⟩

noncomputable def audit_identification :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@polynomial_identification)
      (type_of% (realize signature (fun _ _ m => (cohnPolynomial (2 * m + 1)).comp (X ^ 2 - 1)) (fun a => nomatch a)))
      (Type) (Unit) := {
  unitName := `CohnPolynomialIdentificationVisibility,
  realizationName := `Reg.D5.S3.Arith.Congruence.CohnUniformThreeAdic.Visibility.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ m => (cohnPolynomial (2 * m + 1)).comp (X ^ 2 - 1)) (fun a => nomatch a)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.Congruence.CohnUniformThreeAdic,
    definition := none, coordinates := #[0],
    readouts := #[{ path := #["body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end Reg.D5.S3.Arith.Congruence.CohnUniformThreeAdic.Visibility
