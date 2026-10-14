import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore
import Reg.Support.DependentFamily

open D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore
open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section
namespace Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore

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
  realize signature (fun _ _ x => x ^ 2 + 3) (fun a => nomatch a)

def zeroFamily : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun a => nomatch a)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (x y : ℤ) (e : ℕ), 2 ≤ x → 2 ≤ e →
    R.readout () e x ≠ y ^ e

theorem zeroFamily_fails : ¬ arena.Law zeroFamily := by
  intro h
  exact h 2 0 2 (by norm_num) (by norm_num) rfl

theorem actual_dependence : actual.readout () 2 2 ≠ actual.readout () 2 3 := by
  norm_num [actual, realize]

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨int_sq_add_three_not_pow, zeroFamily, zeroFamily_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroFamily, ?_, rfl, zeroFamily_fails⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    exact ⟨2, 2, 3, actual_dependence⟩

noncomputable def audit_main :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@int_sq_add_three_not_pow)
      (type_of% (realize signature (fun _ _ x => x ^ 2 + 3) (fun a => nomatch a)))
      (Type) (Unit) := {
  unitName := `EisensteinCohnReductionMain,
  realizationName := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ x => x ^ 2 + 3) (fun a => nomatch a)),
  variation := .absent, sensitivity := .absent,
  partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore,
    definition := none, coordinates := #[0],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore
