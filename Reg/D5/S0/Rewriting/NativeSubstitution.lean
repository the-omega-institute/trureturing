import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Rewriting.NativeSubstitution
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open NativeTermUnification Lambda Strata.Util
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S0.Rewriting.NativeSubstitution
namespace Audit_shape_subst
abbrev signature : Signature where
  Params := Subst
  State a := LMonoTy
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := LMonoTy
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ S t => LMonoTy.subst S t) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => .bitvec 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (S : Subst) (hS : NativeSubst S) (t : LMonoTy) (ht : Shape t),
    Shape ((F.readout () S t))

theorem actual_law : arena.Law actual := @_root_.NativeTermUnification.shape_subst
theorem bridge : (type_of% (@_root_.NativeTermUnification.shape_subst)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h [] (by intro t ht; simp [HMaps.values] at ht) (leaf false) (Shape.bool false)
  cases hh

def registration : Registration arena (type_of% (@_root_.NativeTermUnification.shape_subst)) where
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
    refine ⟨[], .bitvec 0, .bitvec 1, ?_⟩
    decide +kernel
end Audit_shape_subst

noncomputable def registration_shape_subst :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NativeTermUnification.shape_subst)
      (type_of% (realize Audit_shape_subst.signature (fun _ S t => LMonoTy.subst S t) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.NativeSubstitution.Audit_shape_subst.unit,
  realizationName := `Reg.D5.S0.Rewriting.NativeSubstitution.Audit_shape_subst.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_shape_subst.arena⟩,
  objectArena := .source ⟨Audit_shape_subst.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_shape_subst.arena ⟨Audit_shape_subst.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_shape_subst.signature (fun _ S t => LMonoTy.subst S t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.NativeSubstitution,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }


namespace Audit_native_insert
abbrev signature : Signature where
  Params := Σ _ : String, LMonoTy
  State a := Subst
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Subst
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a S => S.insert a.1 a.2) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => [HMap.single "bad" (.bitvec 0)]) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (S : Subst) (s : String) (t : LMonoTy)
    (hS : NativeSubst S) (ht : Shape t),
    NativeSubst ((F.readout () ⟨s,t⟩ S))

theorem actual_law : arena.Law actual := @_root_.NativeTermUnification.native_insert
theorem bridge : (type_of% (@_root_.NativeTermUnification.native_insert)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h [] "s" (leaf false) (by intro t ht; simp [HMaps.values] at ht) (Shape.bool false)
  change NativeSubst [HMap.single "bad" (.bitvec 0)] at hh
  have hb := hh (.bitvec 0) (by simp [HMaps.values, HMap.mem_values_single_iff])
  cases hb

def registration : Registration arena (type_of% (@_root_.NativeTermUnification.native_insert)) where
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
    refine ⟨⟨"s", leaf false⟩, [], [HMap.single "u" (leaf true)], ?_⟩
    intro h
    have hh := congrArg (fun S : Subst => S.find? "u") h
    change (actual.readout () ⟨"s", leaf false⟩ []).find? "u" =
      (actual.readout () ⟨"s", leaf false⟩ [HMap.single "u" (leaf true)]).find? "u" at hh
    simp [actual, realize, Subst.apply, HMaps.find?_mapValues,
      HMaps.find?_insert_ne _ "u" "s" _ (by decide), HMaps.find?_single_scope,
      HMap.find?_single_self, HMaps.find?, leaf, LMonoTy.subst_tcons,
      LMonoTys.subst_eq_map] at hh
end Audit_native_insert

noncomputable def registration_native_insert :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NativeTermUnification.native_insert)
      (type_of% (realize Audit_native_insert.signature (fun _ a S => S.insert a.1 a.2) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.NativeSubstitution.Audit_native_insert.unit,
  realizationName := `Reg.D5.S0.Rewriting.NativeSubstitution.Audit_native_insert.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_native_insert.arena⟩,
  objectArena := .source ⟨Audit_native_insert.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_native_insert.arena ⟨Audit_native_insert.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_native_insert.signature (fun _ a S => S.insert a.1 a.2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.NativeSubstitution,
    definition := none, coordinates := #[1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["fn", "fn", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }


namespace Audit_native_apply
abbrev signature : Signature where
  Params := Σ _ : String, LMonoTy
  State a := Subst
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Subst
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a S => Subst.apply (HMap.single a.1 a.2) S) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => [HMap.single "bad" (.bitvec 0)]) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (S : Subst) (s : String) (t : LMonoTy)
    (hS : NativeSubst S) (ht : Shape t),
    NativeSubst ((F.readout () ⟨s,t⟩ S))

theorem actual_law : arena.Law actual := @_root_.NativeTermUnification.native_apply
theorem bridge : (type_of% (@_root_.NativeTermUnification.native_apply)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h [] "s" (leaf false) (by intro t ht; simp [HMaps.values] at ht) (Shape.bool false)
  change NativeSubst [HMap.single "bad" (.bitvec 0)] at hh
  have hb := hh (.bitvec 0) (by simp [HMaps.values, HMap.mem_values_single_iff])
  cases hb

def registration : Registration arena (type_of% (@_root_.NativeTermUnification.native_apply)) where
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
    refine ⟨⟨"s", leaf false⟩, [], [HMap.single "u" (leaf true)], ?_⟩
    intro h
    have hh := congrArg (fun S : Subst => S.find? "u") h
    change (actual.readout () ⟨"s", leaf false⟩ []).find? "u" =
      (actual.readout () ⟨"s", leaf false⟩ [HMap.single "u" (leaf true)]).find? "u" at hh
    simp [actual, realize, Subst.apply, HMaps.find?_mapValues,
      HMaps.find?_insert_ne _ "u" "s" _ (by decide), HMaps.find?_single_scope,
      HMap.find?_single_self, HMaps.find?, leaf, LMonoTy.subst_tcons,
      LMonoTys.subst_eq_map] at hh
end Audit_native_apply

noncomputable def registration_native_apply :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NativeTermUnification.native_apply)
      (type_of% (realize Audit_native_apply.signature (fun _ a S => Subst.apply (HMap.single a.1 a.2) S) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.NativeSubstitution.Audit_native_apply.unit,
  realizationName := `Reg.D5.S0.Rewriting.NativeSubstitution.Audit_native_apply.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_native_apply.arena⟩,
  objectArena := .source ⟨Audit_native_apply.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_native_apply.arena ⟨Audit_native_apply.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_native_apply.signature (fun _ a S => Subst.apply (HMap.single a.1 a.2) S) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.NativeSubstitution,
    definition := none, coordinates := #[1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }


namespace Audit_shape_children
abbrev signature : Signature where
  Params := String
  State a := LMonoTys
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := LMonoTy
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ nm args => .tcons nm args) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => leaf false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {nm : String} {args : LMonoTys} (h : Shape ((F.readout () nm args))),
    ∀ t ∈ args, Shape t

theorem actual_law : arena.Law actual := @_root_.NativeTermUnification.shape_children
theorem bridge : (type_of% (@_root_.NativeTermUnification.shape_children)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (nm := "bad") (args := [.bitvec 0]) (Shape.bool false) (.bitvec 0) (by simp)
  cases hh

def registration : Registration arena (type_of% (@_root_.NativeTermUnification.shape_children)) where
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
    refine ⟨"c", [], [.bitvec 0], ?_⟩
    decide +kernel
end Audit_shape_children

noncomputable def registration_shape_children :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NativeTermUnification.shape_children)
      (type_of% (realize Audit_shape_children.signature (fun _ nm args => .tcons nm args) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.NativeSubstitution.Audit_shape_children.unit,
  realizationName := `Reg.D5.S0.Rewriting.NativeSubstitution.Audit_shape_children.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_shape_children.arena⟩,
  objectArena := .source ⟨Audit_shape_children.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_shape_children.arena ⟨Audit_shape_children.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_shape_children.signature (fun _ nm args => .tcons nm args) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.NativeSubstitution,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "domain", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S0.Rewriting.NativeSubstitution
