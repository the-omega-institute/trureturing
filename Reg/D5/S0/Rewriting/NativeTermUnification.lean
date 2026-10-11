import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Rewriting.NativeTermUnification
import D5.S0.Rewriting.UnificationCompleteness
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open NativeTermUnification Lambda Strata.Util
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S0.Rewriting.NativeTermUnification
private def auditTestInfo : SubstInfo :=
  ⟨Subst.singleton "" (leaf false), SubstWF.single_subst _ _
    (by simp [leaf, LMonoTy.freeVars, LMonoTys.freeVars])⟩


namespace Audit_unifyOne_native
abbrev signature : Signature where
  Params := Unit
  State a := SubstInfo
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Subst
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ S => S.subst) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => [HMap.single "bad" (.bitvec 0)]) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (c : Constraint) (S : SubstInfo)
    (rel : ValidSubstRelation [c] S) (hok : c.unifyOne S = .ok rel)
    (hS : NativeSubst S.subst) (hc : Shape c.1 ∧ Shape c.2),
    NativeSubst (F.readout () () rel.newS)

theorem actual_law : arena.Law actual := @_root_.NativeTermUnification.unifyOne_native
theorem bridge : (type_of% (@_root_.NativeTermUnification.unifyOne_native)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨rel, hok⟩ := Constraint.unifyOne_complete (leaf false, leaf false) SubstInfo.empty [] rfl
    (by intro s t hf; simp [SubstInfo.empty, Subst.empty, HMaps.find?] at hf)
  have hh := h (leaf false, leaf false) SubstInfo.empty rel hok
    (by intro t ht; simp [SubstInfo.empty, Subst.empty, HMaps.values] at ht)
    ⟨Shape.bool false, Shape.bool false⟩
  change NativeSubst [HMap.single "bad" (.bitvec 0)] at hh
  have hb := hh (.bitvec 0) (by simp [HMaps.values, HMap.mem_values_single_iff])
  cases hb

def registration : Registration arena (type_of% (@_root_.NativeTermUnification.unifyOne_native)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨bad, fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, bad_law⟩
    · intro i; exact nomatch i
  dependence := by
    intro i; cases i
    refine ⟨(), SubstInfo.empty, auditTestInfo, ?_⟩
    intro h
    have hh := congrArg (fun S : Subst => S.find? "") h
    change SubstInfo.empty.subst.find? "" = auditTestInfo.subst.find? "" at hh
    simp [SubstInfo.empty, Subst.empty, auditTestInfo, Subst.singleton,
      HMaps.find?_single_scope, HMap.find?_single_self, HMaps.find?] at hh
end Audit_unifyOne_native

noncomputable def registration_unifyOne_native :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NativeTermUnification.unifyOne_native)
      (type_of% (realize Audit_unifyOne_native.signature (fun _ _ S => S.subst) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.NativeTermUnification.Audit_unifyOne_native.unit,
  realizationName := `Reg.D5.S0.Rewriting.NativeTermUnification.Audit_unifyOne_native.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_unifyOne_native.arena⟩,
  objectArena := .source ⟨Audit_unifyOne_native.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_unifyOne_native.arena ⟨Audit_unifyOne_native.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_unifyOne_native.signature (fun _ _ S => S.subst) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.NativeTermUnification,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }


namespace Audit_unifyCore_native
abbrev signature : Signature where
  Params := Unit
  State a := SubstInfo
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Subst
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ S => S.subst) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => [HMap.single "bad" (.bitvec 0)]) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (cs : Constraints) (S : SubstInfo)
    (rel : ValidSubstRelation cs S) (hok : cs.unifyCore S = .ok rel)
    (hS : NativeSubst S.subst) (hc : ∀ c ∈ cs, Shape c.1 ∧ Shape c.2),
    NativeSubst (F.readout () () rel.newS)

theorem actual_law : arena.Law actual := @_root_.NativeTermUnification.unifyCore_native
theorem bridge : (type_of% (@_root_.NativeTermUnification.unifyCore_native)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨rel, hok⟩ := Constraints.unifyCore_complete [] SubstInfo.empty [] (by intro p hp; cases hp)
    (by intro s t hf; simp [SubstInfo.empty, Subst.empty, HMaps.find?] at hf)
  have hh := h [] SubstInfo.empty rel hok
    (by intro t ht; simp [SubstInfo.empty, Subst.empty, HMaps.values] at ht)
    (by intro c hc; cases hc)
  change NativeSubst [HMap.single "bad" (.bitvec 0)] at hh
  have hb := hh (.bitvec 0) (by simp [HMaps.values, HMap.mem_values_single_iff])
  cases hb

def registration : Registration arena (type_of% (@_root_.NativeTermUnification.unifyCore_native)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨bad, fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, bad_law⟩
    · intro i; exact nomatch i
  dependence := by
    intro i; cases i
    refine ⟨(), SubstInfo.empty, auditTestInfo, ?_⟩
    intro h
    have hh := congrArg (fun S : Subst => S.find? "") h
    change SubstInfo.empty.subst.find? "" = auditTestInfo.subst.find? "" at hh
    simp [SubstInfo.empty, Subst.empty, auditTestInfo, Subst.singleton,
      HMaps.find?_single_scope, HMap.find?_single_self, HMaps.find?] at hh
end Audit_unifyCore_native

noncomputable def registration_unifyCore_native :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NativeTermUnification.unifyCore_native)
      (type_of% (realize Audit_unifyCore_native.signature (fun _ _ S => S.subst) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.NativeTermUnification.Audit_unifyCore_native.unit,
  realizationName := `Reg.D5.S0.Rewriting.NativeTermUnification.Audit_unifyCore_native.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_unifyCore_native.arena⟩,
  objectArena := .source ⟨Audit_unifyCore_native.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_unifyCore_native.arena ⟨Audit_unifyCore_native.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_unifyCore_native.signature (fun _ _ S => S.subst) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.NativeTermUnification,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }


namespace Audit_unify_native
abbrev signature : Signature where
  Params := Unit
  State a := SubstInfo
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Subst
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ S => S.subst) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => [HMap.single "bad" (.bitvec 0)]) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (cs : Constraints) (S newS : SubstInfo)
    (hok : cs.unify S = .ok newS) (hS : NativeSubst S.subst)
    (hc : ∀ c ∈ cs, Shape c.1 ∧ Shape c.2),
    NativeSubst (F.readout () () newS)

theorem actual_law : arena.Law actual := @_root_.NativeTermUnification.unify_native
theorem bridge : (type_of% (@_root_.NativeTermUnification.unify_native)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hok : Constraints.unify [] SubstInfo.empty = .ok SubstInfo.empty := by
    unfold Constraints.unify; rw [Constraints.unifyCore.eq_def]; rfl
  have hh := h [] SubstInfo.empty SubstInfo.empty hok
    (by intro t ht; simp [SubstInfo.empty, Subst.empty, HMaps.values] at ht)
    (by intro c hc; cases hc)
  change NativeSubst [HMap.single "bad" (.bitvec 0)] at hh
  have hb := hh (.bitvec 0) (by simp [HMaps.values, HMap.mem_values_single_iff])
  cases hb

def registration : Registration arena (type_of% (@_root_.NativeTermUnification.unify_native)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨bad, fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, bad_law⟩
    · intro i; exact nomatch i
  dependence := by
    intro i; cases i
    refine ⟨(), SubstInfo.empty, auditTestInfo, ?_⟩
    intro h
    have hh := congrArg (fun S : Subst => S.find? "") h
    change SubstInfo.empty.subst.find? "" = auditTestInfo.subst.find? "" at hh
    simp [SubstInfo.empty, Subst.empty, auditTestInfo, Subst.singleton,
      HMaps.find?_single_scope, HMap.find?_single_self, HMaps.find?] at hh
end Audit_unify_native

noncomputable def registration_unify_native :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NativeTermUnification.unify_native)
      (type_of% (realize Audit_unify_native.signature (fun _ _ S => S.subst) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.NativeTermUnification.Audit_unify_native.unit,
  realizationName := `Reg.D5.S0.Rewriting.NativeTermUnification.Audit_unify_native.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_unify_native.arena⟩,
  objectArena := .source ⟨Audit_unify_native.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_unify_native.arena ⟨Audit_unify_native.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_unify_native.signature (fun _ _ S => S.subst) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.NativeTermUnification,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S0.Rewriting.NativeTermUnification
