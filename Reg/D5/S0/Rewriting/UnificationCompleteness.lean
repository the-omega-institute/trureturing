import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Rewriting.UnificationCompleteness
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Lambda Strata.Util
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S0.Rewriting.UnificationCompleteness

/-- Equations vary in the state; neither the common solution nor the current
well-formed substitution is replaced by a finite catalog. -/
abbrev signature : Signature where
  Params := Σ _ : SubstInfo, Subst
  State _ := Constraints
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Except UnifyError SubstInfo
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p cs => Constraints.unify cs p.1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => .error (.ImpossibleToUnify (.bitvec 0, .bitvec 1)))
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law F := ∀ (cs : Constraints) (S : SubstInfo) (R : Subst),
    (∀ p ∈ cs, LMonoTy.subst R p.1 = LMonoTy.subst R p.2) →
    Subst.absorbs R S.subst → ∃ newS, F.readout () ⟨S, R⟩ cs = .ok newS

theorem actual_law : arena.Law actual := Constraints.unify_complete

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨S, hS⟩ := h [] SubstInfo.empty [] (by simp)
    (by intro s t hf; simp [SubstInfo.empty, Subst.empty, HMaps.find?] at hf)
  cases hS

def registration : Registration arena (type_of% Constraints.unify_complete) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨SubstInfo.empty, []⟩, [], [(LMonoTy.bitvec 0, .tcons "foreign" [])], ?_⟩
    intro h
    change Constraints.unify [] SubstInfo.empty =
      Constraints.unify [(LMonoTy.bitvec 0, .tcons "foreign" [])] SubstInfo.empty at h
    simp [Constraints.unify, Constraints.unifyCore.eq_def, Constraint.unifyOne.eq_def,
      Bind.bind, Except.bind, Except.mapError] at h

noncomputable def registration_complete :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@Constraints.unify_complete)
      (type_of% (realize signature (fun _ p cs => Constraints.unify cs p.1)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.UnificationCompleteness.complete,
  realizationName := `Reg.D5.S0.Rewriting.UnificationCompleteness.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p cs => Constraints.unify cs p.1)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.UnificationCompleteness,
    definition := none, coordinates := #[1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

namespace SingleStep
abbrev signature : Signature where
  Params := Subst
  State _ := LMonoTy
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := LMonoTy
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ R t => LMonoTy.subst R t) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => .bitvec 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (c : Constraint) (S : SubstInfo) (R : Subst),
    F.readout () R c.1 = LMonoTy.subst R c.2 →
    Subst.absorbs R S.subst → ∃ relS, Constraint.unifyOne c S = .ok relS

theorem actual_law : arena.Law actual := Constraint.unifyOne_complete
theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨r, hr⟩ := h (.bitvec 0, .bitvec 1) SubstInfo.empty [] rfl
    (by intro s t hf; simp [SubstInfo.empty, Subst.empty, HMaps.find?] at hf)
  simp [Constraint.unifyOne.eq_def] at hr

def registration : Registration arena (type_of% Constraint.unifyOne_complete) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨bad, fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, bad_law⟩
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨[], .bitvec 0, .bitvec 1, ?_⟩
    decide
end SingleStep

namespace Core
abbrev signature := SingleStep.signature
def actual := SingleStep.actual
def bad := SingleStep.bad
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (cs : Constraints) (S : SubstInfo) (R : Subst),
    (∀ p ∈ cs, F.readout () R p.1 = LMonoTy.subst R p.2) →
    Subst.absorbs R S.subst → ∃ relS, Constraints.unifyCore cs S = .ok relS

theorem actual_law : arena.Law actual := Constraints.unifyCore_complete
theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨r, hr⟩ := h [(.bitvec 0, .bitvec 1)] SubstInfo.empty []
    (by intro p hp; simp only [List.mem_singleton] at hp; subst p; rfl)
    (by intro s t hf; simp [SubstInfo.empty, Subst.empty, HMaps.find?] at hf)
  simp [Constraints.unifyCore.eq_def, Constraint.unifyOne.eq_def,
    Bind.bind, Except.bind, Except.mapError] at hr

def registration : Registration arena (type_of% Constraints.unifyCore_complete) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨bad, fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, bad_law⟩
    · intro i; exact nomatch i
  dependence := SingleStep.registration.dependence
end Core

noncomputable def registration_SingleStep :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@Constraint.unifyOne_complete)
      (type_of% (realize SingleStep.signature (fun _ R t => LMonoTy.subst R t)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.UnificationCompleteness.SingleStep.complete,
  realizationName := `Reg.D5.S0.Rewriting.UnificationCompleteness.SingleStep.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨SingleStep.arena⟩,
  objectArena := .source ⟨SingleStep.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source SingleStep.arena ⟨SingleStep.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize SingleStep.signature (fun _ R t => LMonoTy.subst R t)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.UnificationCompleteness,
    definition := none, coordinates := #[2],
    readouts := #[{
      path := #["body", "body", "body", "domain", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_Core :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@Constraints.unifyCore_complete)
      (type_of% (realize Core.signature (fun _ R t => LMonoTy.subst R t)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.UnificationCompleteness.Core.complete,
  realizationName := `Reg.D5.S0.Rewriting.UnificationCompleteness.Core.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Core.arena⟩,
  objectArena := .source ⟨Core.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Core.arena ⟨Core.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Core.signature (fun _ R t => LMonoTy.subst R t)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.UnificationCompleteness,
    definition := none, coordinates := #[2],
    readouts := #[{
      path := #["body", "body", "body", "domain", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S0.Rewriting.UnificationCompleteness
