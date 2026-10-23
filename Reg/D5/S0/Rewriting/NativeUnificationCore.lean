import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Rewriting.NativeUnificationCore
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open NativeTermUnification Lambda Strata.Util
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S0.Rewriting.NativeUnificationCore


/-- The type and its complete presentation remain parameters; states are all
native terms of that original type, without a finite term catalog. -/
abbrev signature : Signature where
  Params := Σ X : Type, Presentation X
  State p := Term p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option (Term p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p t => nativeDecode p.2 (encode p.2 t)) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => none) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (t : Term X),
    F.readout () ⟨X,p⟩ t = some t

theorem actual_law : arena.Law actual := @decode_encode

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h (finPresentation 0) (.of (.inl false))
  cases hf

def registration : Registration arena (type_of% (@decode_encode)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j h => (h (@Subsingleton.elim Unit _ j i)).elim,
        rfl, rejected_law⟩
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨Fin 0, finPresentation 0⟩, .of (.inl false), .of (.inl true), ?_⟩
    change nativeDecode (finPresentation 0) (encode (finPresentation 0) (.of (.inl false))) ≠
      nativeDecode (finPresentation 0) (encode (finPresentation 0) (.of (.inl true)))
    rw [decode_encode, decode_encode]
    decide

noncomputable def registration_decode_encode :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@decode_encode)
      (type_of% (realize signature (fun _ p t => nativeDecode p.2 (encode p.2 t))
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.NativeUnificationCore.decodeEncode,
  realizationName := `Reg.D5.S0.Rewriting.NativeUnificationCore.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p t => nativeDecode p.2 (encode p.2 t))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.NativeUnificationCore,
    definition := none, coordinates := #[0,1],
    readouts := #[{
      path := #["body","body","body","fn","arg"], stateBinder := 2,
      functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

namespace Audit_encode_injective
abbrev signature : Signature where
  Params := Σ X : Type, Presentation X
  State a := Term a.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := LMonoTy
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a t => encode a.2 t) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => .bitvec 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X),
    Function.Injective (((fun t => F.readout () ⟨X,p⟩ t)))

theorem actual_law : arena.Law actual := @_root_.NativeTermUnification.encode_injective
theorem bridge : (type_of% (@_root_.NativeTermUnification.encode_injective)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 0) (a₁ := .of (.inl false)) (a₂ := .of (.inl true)) rfl
  cases hh

def registration : Registration arena (type_of% (@_root_.NativeTermUnification.encode_injective)) where
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
    refine ⟨⟨Fin 0, finPresentation 0⟩, .of (.inl false), .of (.inl true), ?_⟩
    decide +kernel
end Audit_encode_injective

noncomputable def registration_encode_injective :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NativeTermUnification.encode_injective)
      (type_of% (realize Audit_encode_injective.signature (fun _ a t => encode a.2 t) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.NativeUnificationCore.Audit_encode_injective.unit,
  realizationName := `Reg.D5.S0.Rewriting.NativeUnificationCore.Audit_encode_injective.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_encode_injective.arena⟩,
  objectArena := .source ⟨Audit_encode_injective.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_encode_injective.arena ⟨Audit_encode_injective.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_encode_injective.signature (fun _ a t => encode a.2 t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.NativeUnificationCore,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "arg"], stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }


namespace Audit_encode_shape
abbrev signature : Signature where
  Params := Σ X : Type, Presentation X
  State a := Term a.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := LMonoTy
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a t => encode a.2 t) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => .bitvec 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (t : Term X),
    Shape ((F.readout () ⟨X,p⟩ t))

theorem actual_law : arena.Law actual := @_root_.NativeTermUnification.encode_shape
theorem bridge : (type_of% (@_root_.NativeTermUnification.encode_shape)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 0) (.of (.inl false))
  cases hh

def registration : Registration arena (type_of% (@_root_.NativeTermUnification.encode_shape)) where
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
    refine ⟨⟨Fin 0, finPresentation 0⟩, .of (.inl false), .of (.inl true), ?_⟩
    decide +kernel
end Audit_encode_shape

noncomputable def registration_encode_shape :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NativeTermUnification.encode_shape)
      (type_of% (realize Audit_encode_shape.signature (fun _ a t => encode a.2 t) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.NativeUnificationCore.Audit_encode_shape.unit,
  realizationName := `Reg.D5.S0.Rewriting.NativeUnificationCore.Audit_encode_shape.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_encode_shape.arena⟩,
  objectArena := .source ⟨Audit_encode_shape.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_encode_shape.arena ⟨Audit_encode_shape.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_encode_shape.signature (fun _ a t => encode a.2 t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.NativeUnificationCore,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }


namespace Audit_encode_supported
abbrev signature : Signature where
  Params := Σ X : Type, Presentation X
  State a := Term a.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := LMonoTy
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a t => encode a.2 t) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => .ftvar "foreign") (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (t : Term X),
    Supported p ((F.readout () ⟨X,p⟩ t))

theorem actual_law : arena.Law actual := @_root_.NativeTermUnification.encode_supported
theorem bridge : (type_of% (@_root_.NativeTermUnification.encode_supported)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨x, hx⟩ := h (finPresentation 0) (.of (.inl false)) "foreign" (by change "foreign" ∈ (LMonoTy.ftvar "foreign").freeVars; simp [LMonoTy.freeVars])
  exact Fin.elim0 x

def registration : Registration arena (type_of% (@_root_.NativeTermUnification.encode_supported)) where
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
    refine ⟨⟨Fin 0, finPresentation 0⟩, .of (.inl false), .of (.inl true), ?_⟩
    decide +kernel
end Audit_encode_supported

noncomputable def registration_encode_supported :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NativeTermUnification.encode_supported)
      (type_of% (realize Audit_encode_supported.signature (fun _ a t => encode a.2 t) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.NativeUnificationCore.Audit_encode_supported.unit,
  realizationName := `Reg.D5.S0.Rewriting.NativeUnificationCore.Audit_encode_supported.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_encode_supported.arena⟩,
  objectArena := .source ⟨Audit_encode_supported.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_encode_supported.arena ⟨Audit_encode_supported.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_encode_supported.signature (fun _ a t => encode a.2 t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.NativeUnificationCore,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }


namespace Audit_decode_exact
abbrev signature : Signature where
  Params := Σ X : Type, Presentation X
  State a := LMonoTy
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Option (Term a.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a t => nativeDecode a.2 t) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => none) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (t : LMonoTy) (ht : Shape t) (hs : Supported p t),
    ∃ a, (F.readout () ⟨X,p⟩ t) = some a ∧ encode p a = t

theorem actual_law : arena.Law actual := @_root_.NativeTermUnification.decode_exact
theorem bridge : (type_of% (@_root_.NativeTermUnification.decode_exact)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨a, ha, he⟩ := h (finPresentation 0) (leaf false) (Shape.bool false)
    (by intro s hs; simp [leaf, LMonoTy.freeVars, LMonoTys.freeVars] at hs)
  cases ha

def registration : Registration arena (type_of% (@_root_.NativeTermUnification.decode_exact)) where
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
    refine ⟨⟨Fin 0, finPresentation 0⟩, leaf false, leaf true, ?_⟩
    decide +kernel
end Audit_decode_exact

noncomputable def registration_decode_exact :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NativeTermUnification.decode_exact)
      (type_of% (realize Audit_decode_exact.signature (fun _ a t => nativeDecode a.2 t) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.NativeUnificationCore.Audit_decode_exact.unit,
  realizationName := `Reg.D5.S0.Rewriting.NativeUnificationCore.Audit_decode_exact.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_decode_exact.arena⟩,
  objectArena := .source ⟨Audit_decode_exact.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_decode_exact.arena ⟨Audit_decode_exact.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_decode_exact.signature (fun _ a t => nativeDecode a.2 t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.NativeUnificationCore,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }


namespace Audit_encode_decode
abbrev signature : Signature where
  Params := Σ X : Type, Presentation X
  State a := Term a.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := LMonoTy
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a t => encode a.2 t) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => .bitvec 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (t : LMonoTy) (a : Term X)
    (h : nativeDecode p t = some a),
    (F.readout () ⟨X,p⟩ a) = t

theorem actual_law : arena.Law actual := @_root_.NativeTermUnification.encode_decode
theorem bridge : (type_of% (@_root_.NativeTermUnification.encode_decode)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 0) (leaf false) (.of (.inl false)) (by simp [leaf, nativeDecode])
  cases hh

def registration : Registration arena (type_of% (@_root_.NativeTermUnification.encode_decode)) where
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
    refine ⟨⟨Fin 0, finPresentation 0⟩, .of (.inl false), .of (.inl true), ?_⟩
    decide +kernel
end Audit_encode_decode

noncomputable def registration_encode_decode :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NativeTermUnification.encode_decode)
      (type_of% (realize Audit_encode_decode.signature (fun _ a t => encode a.2 t) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.NativeUnificationCore.Audit_encode_decode.unit,
  realizationName := `Reg.D5.S0.Rewriting.NativeUnificationCore.Audit_encode_decode.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_encode_decode.arena⟩,
  objectArena := .source ⟨Audit_encode_decode.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_encode_decode.arena ⟨Audit_encode_decode.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_encode_decode.signature (fun _ a t => encode a.2 t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.NativeUnificationCore,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }


namespace Audit_decode_domain
abbrev signature : Signature where
  Params := Σ X : Type, Presentation X
  State a := LMonoTy
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Option (Term a.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a t => nativeDecode a.2 t) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => none) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (t : LMonoTy),
    (∃ a, (F.readout () ⟨X,p⟩ t) = some a) ↔ Shape t ∧ Supported p t

theorem actual_law : arena.Law actual := @_root_.NativeTermUnification.decode_domain
theorem bridge : (type_of% (@_root_.NativeTermUnification.decode_domain)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨a, ha⟩ := (h (finPresentation 0) (leaf false)).mpr
    ⟨Shape.bool false, by intro s hs; simp [leaf, LMonoTy.freeVars, LMonoTys.freeVars] at hs⟩
  cases ha

def registration : Registration arena (type_of% (@_root_.NativeTermUnification.decode_domain)) where
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
    refine ⟨⟨Fin 0, finPresentation 0⟩, leaf false, leaf true, ?_⟩
    decide +kernel
end Audit_decode_domain

noncomputable def registration_decode_domain :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NativeTermUnification.decode_domain)
      (type_of% (realize Audit_decode_domain.signature (fun _ a t => nativeDecode a.2 t) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.NativeUnificationCore.Audit_decode_domain.unit,
  realizationName := `Reg.D5.S0.Rewriting.NativeUnificationCore.Audit_decode_domain.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_decode_domain.arena⟩,
  objectArena := .source ⟨Audit_decode_domain.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_decode_domain.arena ⟨Audit_decode_domain.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_decode_domain.signature (fun _ a t => nativeDecode a.2 t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Rewriting.NativeUnificationCore,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "body", "fn", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S0.Rewriting.NativeUnificationCore
