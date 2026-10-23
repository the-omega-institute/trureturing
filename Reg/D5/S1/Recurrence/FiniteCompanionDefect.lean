import D5.S1.Recurrence.FiniteCompanionDefect
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S1.Recurrence.FiniteCompanionDefect
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.FiniteCompanionDefect
noncomputable section
universe u

abbrev signature : Signature where
  Params := (Type u) × ℕ
  State p := Fin (p.2 + 1) → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin (p.2 + 1) → p.1
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {A : Type u} [AddCommGroup A] (J : A →+ A) (n : ℕ) (v : Fin (n + 1) → A),
    codomainEquiv J n (companion J n (r.readout () ⟨A, n⟩ v)) =
      ((domainEquiv n v).1 + J (if Odd (n + 1) then (domainEquiv n v).1 else 0),
        (domainEquiv n v).2)

abbrev actual : Realization signature.{u} :=
  realize signature (fun _ _ v => v) (fun e => nomatch e)

abbrev bad : Realization signature.{u} :=
  realize signature (fun _ _ v => fun _ => v 0) (fun e => nomatch e)

private theorem bad_law : ¬ arena.{u}.Law bad := by
  intro h
  let v : Fin 2 → ULift.{u} ℤ := Fin.cons 0 (fun _ => 1)
  have hh := @h (ULift.{u} ℤ) inferInstance (0 : ULift.{u} ℤ →+ ULift.{u} ℤ) 1 v
  have ht := congrArg (fun z => (z.2 0).down) hh
  norm_num [bad, realize, v, codomainEquiv, companion, domainEquiv] at ht

private theorem actual_law : arena.{u}.Law actual := by
  intro A inst J n v
  exact eliminate J n v

def eliminationRegistration : Registration arena.{u}
    (∀ {A : Type u} [AddCommGroup A] (J : A →+ A) (n : ℕ) (v : Fin (n + 1) → A),
      codomainEquiv J n (companion J n v) =
        ((domainEquiv n v).1 + J (if Odd (n + 1) then (domainEquiv n v).1 else 0),
          (domainEquiv n v).2)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} ℤ, 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    intro hh
    have ht := congrArg (fun v : Fin 1 → ULift.{u} ℤ => (v 0).down) hh
    norm_num [actual, realize] at ht

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,u+1,u,0,u,0,0}
    (@_root_.D5.S1.Recurrence.FiniteCompanionDefect.eliminate.{u})
    (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.FiniteCompanionDefect.elimination_unit
  realizationName := `Reg.D5.S1.Recurrence.FiniteCompanionDefect.eliminationRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨eliminationRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.FiniteCompanionDefect
    definition := none
    coordinates := #[0, 3]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S1.Recurrence.FiniteCompanionDefect
