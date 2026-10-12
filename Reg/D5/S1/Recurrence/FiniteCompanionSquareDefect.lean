import D5.S1.Recurrence.FiniteCompanionSquareDefect
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S1.Recurrence.FiniteCompanionSquareDefect
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.FiniteCompanionSquareDefect
noncomputable section
universe u

abbrev signature : Signature where
  Params := (Type u) × ℕ
  State p := Fin (p.2 + 2) → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin (p.2 + 2) → p.1
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature.{u} :=
  realize signature (fun _ _ v => v) (fun e => nomatch e)

abbrev bad : Realization signature.{u} :=
  realize signature (fun _ _ v => fun _ => v 0) (fun e => nomatch e)

abbrev eliminationArena : Arena where
  signature := signature.{u}
  Law r := ∀ {A : Type u} [AddCommGroup A] (J : A →+ A) (hJ : ∀ a, J (J a) = a)
    (n : ℕ) (v : Fin (n + 2) → A),
    codomainEquiv J n (squareDefect J (n+1) (r.readout () ⟨A,n⟩ v)) =
      (headResidual J (n+2) (domainEquiv n v).1,(domainEquiv n v).2)

abbrev normalArena : Arena where
  signature := signature.{u}
  Law r := ∀ {A : Type u} [AddCommGroup A] (J : A →+ A) (hJ : ∀ a, J (J a) = a)
    (n : ℕ) (v : Fin (n + 2) → A),
    normalCodomainEquiv J n (squareDefect J (n+1) (r.readout () ⟨A,n⟩ v)) =
      (headNormal J (n+2) (normalDomainEquiv J n v).1,(normalDomainEquiv J n v).2)

private theorem bad_elimination : ¬ eliminationArena.{u}.Law bad := by
  intro h
  let v : Fin 3 → ULift.{u} ℤ := Fin.cons 0 (Fin.cons 0 (fun _ => 1))
  have hh := @h (ULift.{u} ℤ) inferInstance (AddMonoidHom.id _) (fun _ => rfl) 1 v
  have he := eliminate (AddMonoidHom.id (ULift.{u} ℤ)) (fun _ => rfl) 1
    (bad.readout () ⟨ULift.{u} ℤ,1⟩ v)
  rw [he] at hh
  have ht := congrArg (fun z => (z.2 0).down) hh
  norm_num [domainEquiv,bad,realize,v] at ht

private theorem bad_normal : ¬ normalArena.{u}.Law bad := by
  intro h
  let v : Fin 3 → ULift.{u} ℤ := Fin.cons 0 (Fin.cons 0 (fun _ => 1))
  have hh := @h (ULift.{u} ℤ) inferInstance (AddMonoidHom.id _) (fun _ => rfl) 1 v
  have he := normal_form (AddMonoidHom.id (ULift.{u} ℤ)) (fun _ => rfl) 1
    (bad.readout () ⟨ULift.{u} ℤ,1⟩ v)
  rw [he] at hh
  have ht := congrArg (fun z => (z.2 0).down) hh
  change (0 : ℤ) = 1 at ht
  omega

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} ℤ,0⟩,(fun _ => 0),(fun _ => 1),?_⟩
  intro hh
  have ht := congrArg (fun v : Fin 2 → ULift.{u} ℤ => (v 0).down) hh
  norm_num [actual,realize] at ht

def eliminationEvidence : Registration eliminationArena.{u}
    (∀ {A : Type u} [AddCommGroup A] (J : A →+ A) (hJ : ∀ a, J (J a) = a)
      (n : ℕ) (v : Fin (n+2) → A),
      codomainEquiv J n (squareDefect J (n+1) v) =
        (headResidual J (n+2) (domainEquiv n v).1,(domainEquiv n v).2)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨eliminate,bad,bad_elimination⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_elimination⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def normalEvidence : Registration normalArena.{u}
    (∀ {A : Type u} [AddCommGroup A] (J : A →+ A) (hJ : ∀ a, J (J a) = a)
      (n : ℕ) (v : Fin (n+2) → A),
      normalCodomainEquiv J n (squareDefect J (n+1) v) =
        (headNormal J (n+2) (normalDomainEquiv J n v).1,(normalDomainEquiv J n v).2)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨normal_form,bad,bad_normal⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_normal⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def eliminate_registration : Contract.Registration.{_,_,_,0,0,0,u+1,u,0,u,0,0}
    (@_root_.D5.S1.Recurrence.FiniteCompanionSquareDefect.eliminate.{u})
    (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.FiniteCompanionSquareDefect.eliminate_unit
  realizationName := `Reg.D5.S1.Recurrence.FiniteCompanionSquareDefect.eliminationEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨eliminationArena.{u}⟩
  objectArena := .source ⟨eliminationArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source eliminationArena.{u} ⟨eliminationEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.FiniteCompanionSquareDefect
    definition := none
    coordinates := #[0,4]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def normal_form_registration : Contract.Registration.{_,_,_,0,0,0,u+1,u,0,u,0,0}
    (@_root_.D5.S1.Recurrence.FiniteCompanionSquareDefect.normal_form.{u})
    (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.FiniteCompanionSquareDefect.normal_form_unit
  realizationName := `Reg.D5.S1.Recurrence.FiniteCompanionSquareDefect.normalEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨normalArena.{u}⟩
  objectArena := .source ⟨normalArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source normalArena.{u} ⟨normalEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.FiniteCompanionSquareDefect
    definition := none
    coordinates := #[0,4]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S1.Recurrence.FiniteCompanionSquareDefect
