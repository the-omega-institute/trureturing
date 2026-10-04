import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius

open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

def signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def quotientCard (ell : ℕ) : ℕ :=
  Nat.card (EisensteinOrder ⧸ Ideal.span {(ell : EisensteinOrder)})

def actual : Realization signature :=
  realize signature (fun _ _ ell => quotientCard ell) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℕ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (ell : ℕ) [Fact ell.Prime] (_hell3 : ell % 3 = 2),
    let I : Ideal EisensteinOrder := Ideal.span {(ell : EisensteinOrder)}
    I.IsMaximal ∧ R.readout () () ell = ell ^ 2 ∧
      CharP (EisensteinOrder ⧸ I) ell ∧
      ∃ e : EisensteinOrder ⧸ I ≃+* QuadraticAlgebra (ZMod ell) (-1) (-1),
        (∀ z : EisensteinOrder,
          (e (Ideal.Quotient.mk I z)).re = (z.re : ZMod ell) ∧
          (e (Ideal.Quotient.mk I z)).im = (z.im : ZMod ell)) ∧
        ∀ z : EisensteinOrder,
          (Ideal.Quotient.mk I z) ^ ell = Ideal.Quotient.mk I (star z)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := (h 2 (by decide)).2.1
  change (0 : ℕ) = 2 ^ 2 at hcard
  norm_num at hcard

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro ell _ hell3
    exact inert_eisenstein_quotient_frobenius ell hell3
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    change ∃ (_ : Unit) (x y : ℕ), quotientCard x ≠ quotientCard y
    refine ⟨(), 2, 5, ?_⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
    have htwo : quotientCard 2 = 2 ^ 2 :=
      (inert_eisenstein_quotient_frobenius 2 (by decide)).2.1
    have hfive : quotientCard 5 = 5 ^ 2 :=
      (inert_eisenstein_quotient_frobenius 5 (by decide)).2.1
    intro h
    have hcontr : (2 : ℕ) ^ 2 = 5 ^ 2 := htwo.symm.trans (h.trans hfive)
    norm_num at hcontr

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.inert_eisenstein_quotient_frobenius) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ ell => quotientCard ell) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "QuadraticIdeals") "InertEisensteinFrobenius") "inert_eisenstein_quotient_frobenius") "Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius/Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ ell => quotientCard ell) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end

end Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius
