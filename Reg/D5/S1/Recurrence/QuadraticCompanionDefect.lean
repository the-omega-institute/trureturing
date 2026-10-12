import D5.S1.Recurrence.QuadraticCompanionDefect
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S1.Recurrence.QuadraticCompanionDefect
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.QuadraticCompanionDefect
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

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {A : Type u} [AddCommGroup A] (J : A →+ A) (n : ℕ) (v : Fin (n + 2) → A),
    codomainEquiv J n (companion J n (r.readout () ⟨A, n⟩ v)) =
      (boundary J n (v 0) (v (0 : Fin (n + 1)).succ), (domainEquiv n v).2)

abbrev actual : Realization signature.{u} :=
  realize signature (fun _ _ v => v) (fun e => nomatch e)

abbrev bad : Realization signature.{u} :=
  realize signature (fun _ _ v => fun _ => v 0) (fun e => nomatch e)

private theorem bad_law : ¬ arena.{u}.Law bad := by
  intro h
  let v : Fin 2 → ULift.{u} ℤ := Fin.cons 0 (fun _ => 1)
  have hh := @h (ULift.{u} ℤ) inferInstance (0 : ULift.{u} ℤ →+ ULift.{u} ℤ) 0 v
  have hb : bad.readout () ⟨ULift.{u} ℤ, 0⟩ v = 0 := by
    funext j
    change (0 : ULift.{u} ℤ) = 0
    rfl
  rw [hb, map_zero, map_zero] at hh
  have ht := congrArg (fun z => z.1.2.down) hh
  norm_num [v, boundary, reconstruct] at ht

private theorem actual_law : arena.{u}.Law actual := by
  intro A inst J n v
  exact eliminate J n v

def eliminationRegistration : Registration arena.{u}
    (∀ {A : Type u} [AddCommGroup A] (J : A →+ A) (n : ℕ) (v : Fin (n + 2) → A),
      codomainEquiv J n (companion J n v) =
        (boundary J n (v 0) (v (0 : Fin (n + 1)).succ), (domainEquiv n v).2)) where
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
    have ht := congrArg (fun v : Fin 2 → ULift.{u} ℤ => (v 0).down) hh
    norm_num [actual, realize] at ht

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,u+1,u,0,u,0,0}
    (@_root_.D5.S1.Recurrence.QuadraticCompanionDefect.eliminate.{u})
    (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.QuadraticCompanionDefect.elimination_unit
  realizationName := `Reg.D5.S1.Recurrence.QuadraticCompanionDefect.eliminationRegistration
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
    owner := `D5.S1.Recurrence.QuadraticCompanionDefect
    definition := none
    coordinates := #[0, 3]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev boundarySignature : Signature where
  Params := Σ A : Type u, ℕ × A
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev boundaryArena : Arena where
  signature := boundarySignature.{u}
  Law r := ∀ {A : Type u} [AddCommGroup A] (J : A →+ A) (hJ : ∀ x, J (J x) = x)
      (m : ℕ) (a b : A),
    boundary J (4 * m + 1) (r.readout () ⟨A, m, b⟩ a) b =
      (a + b + J (a + b), b + J b)

abbrev boundaryActual : Realization boundarySignature.{u} :=
  realize boundarySignature (fun _ _ a => a) (fun e => nomatch e)

abbrev boundaryBad : Realization boundarySignature.{u} :=
  realize boundarySignature (fun _ p _ => p.2.2) (fun e => nomatch e)

private theorem boundary_bad : ¬ boundaryArena.{u}.Law boundaryBad := by
  intro h
  have hh := @h (ULift.{u} ℤ) inferInstance (AddMonoidHom.id (ULift.{u} ℤ))
    (fun _ => rfl) 0 1 0
  have ht := congrArg (fun z => z.1.down) hh
  norm_num [boundaryBad, realize, boundary, reconstruct, prefixSum,
    Fin.sum_univ_succ] at ht

def boundaryRegistration : Registration boundaryArena.{u}
    (∀ {A : Type u} [AddCommGroup A] (J : A →+ A) (hJ : ∀ x, J (J x) = x)
      (m : ℕ) (a b : A), boundary J (4 * m + 1) a b =
        (a + b + J (a + b), b + J b)) where
  actual := boundaryActual
  bridge := Iff.rfl
  variation := ⟨boundary_three_mod_four, boundaryBad, boundary_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨boundaryBad, ?_, rfl, boundary_bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} ℤ, 0, 0⟩, 0, 1, ?_⟩
    intro h
    have ht := congrArg (fun a : ULift.{u} ℤ => a.down) h
    norm_num [boundaryActual, realize] at ht

noncomputable def registration_2 : Contract.Registration.{_,_,_,0,0,0,u+1,u,0,u,0,0}
    (@_root_.D5.S1.Recurrence.QuadraticCompanionDefect.boundary_three_mod_four.{u})
    (Realization boundarySignature.{u}) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.QuadraticCompanionDefect.boundary_unit
  realizationName := `Reg.D5.S1.Recurrence.QuadraticCompanionDefect.boundaryRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨boundaryArena.{u}⟩
  objectArena := .source ⟨boundaryArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source boundaryArena.{u} ⟨boundaryRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize boundarySignature.{u} (fun _ _ a => a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.QuadraticCompanionDefect
    definition := none
    coordinates := #[0, 4, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S1.Recurrence.QuadraticCompanionDefect
