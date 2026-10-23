import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace
import Reg.Support.DependentFamily
import Reg.Support.NativeGroundAssignmentEvidence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

open NativeTermUnification Lambda Strata.Util
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace

/-- Parameters retain every original type, complete presentation, equation list
and actual successful output. States are all complementary ground assignments. -/
structure Inputs where
  X : Type
  p : Presentation X
  C : Equations X
  S : SubstInfo
  success : (encodeEquations p C).unify SubstInfo.empty = .ok S

abbrev signature : Signature where
  Params := Inputs
  State a := Y a.p a.S → Ground
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := a.X → Ground
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a w => _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext a.p a.C a.S a.success w) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ _ => FreeMagma.of true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (success : (encodeEquations p C).unify SubstInfo.empty = .ok S)
    (w : Y p S → Ground), Sol C (F.readout () ⟨X,p,C,S,success⟩ w)

theorem actual_law : arena.Law actual := @Ext_sol

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let p := finPresentation 1
  let C : Equations (Fin 1) := [(.of (.inr 0), .of (.inl false))]
  have hv : Sol C (fun _ => (.of false : Ground)) := by
    intro c hc
    have hc' : c = (.of (.inr 0), .of (.inl false)) := List.mem_singleton.mp hc
    subst c
    rfl
  obtain ⟨S,hS⟩ := native_complete p C (fun _ => (.of false : Ground)) hv
  have hh := h p C S hS (fun _ => .of false)
  have hb := hh (.of (.inr 0), .of (.inl false)) (List.mem_singleton_self _)
  change FreeMagma.of true = FreeMagma.of false at hb
  cases hb

def registration : Registration arena (type_of% (@Ext_sol)) where
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
    let p := finPresentation 1
    have he : (encodeEquations p []).unify SubstInfo.empty = .ok SubstInfo.empty := by
      change Constraints.unify [] SubstInfo.empty = .ok SubstInfo.empty
      unfold Constraints.unify
      rw [Constraints.unifyCore.eq_def]
      rfl
    let y : Y p SubstInfo.empty := ⟨0, by
      simp [D, SubstInfo.empty, Subst.empty, HMaps.keys]⟩
    refine ⟨⟨Fin 1,p,[],SubstInfo.empty,he⟩,
      (fun _ => .of false), (fun _ => .of true), ?_⟩
    intro hh
    have hr := congrArg (restriction p SubstInfo.empty) hh
    change restriction p SubstInfo.empty (_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext p [] SubstInfo.empty he (fun _ => .of false)) =
      restriction p SubstInfo.empty (_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext p [] SubstInfo.empty he (fun _ => .of true)) at hr
    rw [restriction_Ext, restriction_Ext] at hr
    have hb := congrFun hr y
    cases hb

namespace Audit_evaluate_restrictTerm
abbrev signature : Signature where
  Params := Σ X : Type, X → Ground
  State a := Term a.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Ground
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a t => evaluate a.2 t) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => .of true) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (S : SubstInfo) (v : X → Ground)
    (t : Term X) (h : ∀ x ∈ termVars t, x ∉ D p S),
    evaluate (restriction p S v) (restrictTerm p S t h) = (F.readout () ⟨X,v⟩ t)

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.evaluate_restrictTerm
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.evaluate_restrictTerm)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 0) SubstInfo.empty (fun x => Fin.elim0 x) (.of (.inl false))
    (by intro x hx; exact Fin.elim0 x)
  change FreeMagma.of false = FreeMagma.of true at hh
  cases hh

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.evaluate_restrictTerm)) where
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
    refine ⟨⟨Fin 0, fun x => Fin.elim0 x⟩, .of (.inl false), .of (.inl true), ?_⟩
    decide +kernel
end Audit_evaluate_restrictTerm


namespace Audit_restriction_Ext
abbrev signature : Signature where
  Params := Σ X : Type, Σ p : Presentation X, SubstInfo
  State a := a.1 → Ground
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Y a.2.1 a.2.2 → Ground
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a v => restriction a.2.1 a.2.2 v) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ _ => .of true) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) (w : Y p S → Ground),
    ((fun v => F.readout () ⟨X,p,S⟩ v)) (_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext p C S hok w) = w

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.restriction_Ext
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.restriction_Ext)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 1) [] SubstInfo.empty (empty_success _) (fun _ => .of false)
  have hb := congrFun hh y0
  cases hb

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.restriction_Ext)) where
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
    refine ⟨⟨Fin 1, finPresentation 1, SubstInfo.empty⟩, (fun _ => .of false), (fun _ => .of true), ?_⟩
    intro h
    have hh := congrFun h y0
    cases hh
end Audit_restriction_Ext


namespace Audit_Ext_restriction
abbrev signature : Signature where
  Params := Σ X : Type, Σ p : Presentation X, SubstInfo
  State a := a.1 → Ground
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Y a.2.1 a.2.2 → Ground
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a v => restriction a.2.1 a.2.2 v) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ _ => .of true) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) (v : X → Ground)
    (hv : Sol C v),
    _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext p C S hok (((fun v => F.readout () ⟨X,p,S⟩ v)) v) = v

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext_restriction
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext_restriction)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 1) [] SubstInfo.empty (empty_success _) (fun _ => .of false)
    (by intro c hc; cases hc)
  have hb := congrFun hh 0
  have he : _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext (finPresentation 1) [] SubstInfo.empty (empty_success _)
      (fun _ => .of true) 0 = FreeMagma.of true := by
    simp [_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext, sigma, action_identity _ _ _ (empty_unbound _ _), restrictTerm, evaluate]
  change _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext (finPresentation 1) [] SubstInfo.empty (empty_success _) (fun _ => .of true) 0 = FreeMagma.of false at hb
  rw [he] at hb
  cases hb

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext_restriction)) where
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
    refine ⟨⟨Fin 1, finPresentation 1, SubstInfo.empty⟩, (fun _ => .of false), (fun _ => .of true), ?_⟩
    intro h
    have hh := congrFun h y0
    cases hh
end Audit_Ext_restriction


namespace Audit_shape_ground
abbrev signature : Signature where
  Params := Unit
  State a := Ground
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := LMonoTy
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ u => encodeGround u) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => .bitvec 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (t : LMonoTy) (ht : Shape t) (hf : t.freeVars = []),
    ∃ u : Ground, (F.readout () () u) = t

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.shape_ground
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.shape_ground)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨u, hu⟩ := h (leaf false) (Shape.bool false) (by simp [leaf, LMonoTy.freeVars, LMonoTys.freeVars])
  cases hu

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.shape_ground)) where
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
    refine ⟨(), .of false, .of true, ?_⟩
    decide +kernel
end Audit_shape_ground


namespace Audit_native_ground_iff
abbrev signature : Signature where
  Params := Unit
  State a := Ground
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := LMonoTy
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ u => encodeGround u) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => .bitvec 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (t : LMonoTy) (ht : Shape t),
    t.freeVars = [] ↔ ∃! u : Ground, (F.readout () () u) = t

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.native_ground_iff
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.native_ground_iff)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨u, hu, _⟩ := (h (leaf false) (Shape.bool false)).mp
    (by simp [leaf, LMonoTy.freeVars, LMonoTys.freeVars])
  cases hu

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.native_ground_iff)) where
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
    refine ⟨(), .of false, .of true, ?_⟩
    decide +kernel
end Audit_native_ground_iff


namespace Audit_encodeGround_freeVars
abbrev signature : Signature where
  Params := Unit
  State a := Ground
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := LMonoTy
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ u => encodeGround u) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => .ftvar "bad") (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (u : Ground),
    ((F.readout () () u)).freeVars = []

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.encodeGround_freeVars
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.encodeGround_freeVars)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (.of false)
  have hn : (LMonoTy.ftvar "bad").freeVars ≠ [] := by decide
  exact hn hh

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.encodeGround_freeVars)) where
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
    refine ⟨(), .of false, .of true, ?_⟩
    decide +kernel
end Audit_encodeGround_freeVars


namespace Audit_substitute_evaluate
abbrev signature : Signature where
  Params := Σ X : Type, X → Term X
  State a := Term a.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Term a.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a t => substitute a.2 t) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => .of (.inl true)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (f : X → Term X) (v : X → Ground) (t : Term X),
    evaluate v ((F.readout () ⟨X,f⟩ t)) = evaluate (fun x => evaluate v (f x)) t

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.substitute_evaluate
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.substitute_evaluate)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (fun x : Fin 0 => Fin.elim0 x) (fun x => Fin.elim0 x) (.of (.inl false))
  change FreeMagma.of true = FreeMagma.of false at hh
  cases hh

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.substitute_evaluate)) where
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
    refine ⟨⟨Fin 0, fun x => Fin.elim0 x⟩, .of (.inl false), .of (.inl true), ?_⟩
    decide +kernel
end Audit_substitute_evaluate


namespace Audit_action_substitute_encode
abbrev signature : Signature where
  Params := Σ X : Type, Σ p : Presentation X, SubstInfo
  State a := a.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Term a.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a x => action a.2.1 a.2.2 x) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => .of (.inl true)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) (t : Term X),
    encode p (substitute (((fun x => F.readout () ⟨X,p,S⟩ x))) t) = LMonoTy.subst S.subst (encode p t)

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_substitute_encode
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_substitute_encode)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 1) [] SubstInfo.empty (empty_success _) (.of (.inr 0))
  have hn : encode (finPresentation 1) (substitute (fun _ => .of (.inl true)) (.of (.inr 0))) ≠
      LMonoTy.subst SubstInfo.empty.subst (encode (finPresentation 1) (.of (.inr 0))) := by decide +kernel
  exact hn hh

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_substitute_encode)) where
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
    refine ⟨⟨Fin 2, finPresentation 2, SubstInfo.empty⟩, 0, 1, ?_⟩
    decide +kernel
end Audit_action_substitute_encode


namespace Audit_action_idempotent
abbrev signature : Signature where
  Params := Σ X : Type, Σ p : Presentation X, SubstInfo
  State a := a.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Term a.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a x => action a.2.1 a.2.2 x) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => .of (.inl true)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) (x : X),
    substitute (((fun x => F.readout () ⟨X,p,S⟩ x))) (action p S x) = action p S x

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_idempotent
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_idempotent)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 1) [] SubstInfo.empty (empty_success _) 0
  change substitute (fun _ => .of (.inl true)) (action (finPresentation 1) SubstInfo.empty 0) =
    action (finPresentation 1) SubstInfo.empty 0 at hh
  rw [action_identity _ _ _ (empty_unbound _ _)] at hh
  change FreeMagma.of (Sum.inl true) = FreeMagma.of (Sum.inr (0 : Fin 1)) at hh
  cases hh

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_idempotent)) where
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
    refine ⟨⟨Fin 2, finPresentation 2, SubstInfo.empty⟩, 0, 1, ?_⟩
    decide +kernel
end Audit_action_idempotent


namespace Audit_total_action_spec
abbrev signature : Signature where
  Params := Σ X : Type, Σ p : Presentation X, SubstInfo
  State a := a.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Term a.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a x => action a.2.1 a.2.2 x) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => .of (.inl true)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S),
    ∀ x, substitute (((fun x => F.readout () ⟨X,p,S⟩ x))) (action p S x) = action p S x ∧
      (∀ y ∈ termVars (action p S x), y ∉ D p S) ∧
      (x ∉ D p S → action p S x = .of (.inr x)) ∧
      (x ∈ D p S ↔ action p S x ≠ .of (.inr x))

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.total_action_spec
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.total_action_spec)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 1) [] SubstInfo.empty (empty_success _) 0
  have hh := hh.1
  change substitute (fun _ => .of (.inl true)) (action (finPresentation 1) SubstInfo.empty 0) =
    action (finPresentation 1) SubstInfo.empty 0 at hh
  rw [action_identity _ _ _ (empty_unbound _ _)] at hh
  change FreeMagma.of (Sum.inl true) = FreeMagma.of (Sum.inr (0 : Fin 1)) at hh
  cases hh

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.total_action_spec)) where
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
    refine ⟨⟨Fin 2, finPresentation 2, SubstInfo.empty⟩, 0, 1, ?_⟩
    decide +kernel
end Audit_total_action_spec


namespace Audit_restriction_fill
abbrev signature : Signature where
  Params := Σ X : Type, Σ p : Presentation X, SubstInfo
  State a := Y a.2.1 a.2.2 → Ground
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Y a.2.1 a.2.2 → Ground
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a w => restriction a.2.1 a.2.2 (fill a.2.1 a.2.2 w)) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ _ => .of true) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (S : SubstInfo) (w : Y p S → Ground),
    (F.readout () ⟨X,p,S⟩ w) = w

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.restriction_fill
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.restriction_fill)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 1) SubstInfo.empty (fun _ => .of false)
  have hb := congrFun hh y0
  cases hb

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.restriction_fill)) where
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
    refine ⟨⟨Fin 1, finPresentation 1, SubstInfo.empty⟩, (fun _ => .of false), (fun _ => .of true), ?_⟩
    intro h
    have hh := congrFun h y0
    change restriction (finPresentation 1) SubstInfo.empty (fill (finPresentation 1) SubstInfo.empty (fun _ => .of false)) y0 =
      restriction (finPresentation 1) SubstInfo.empty (fill (finPresentation 1) SubstInfo.empty (fun _ => .of true)) y0 at hh
    rw [restriction_fill, restriction_fill] at hh
    cases hh
end Audit_restriction_fill


namespace Audit_Ext_evaluate_action
abbrev signature : Signature where
  Params := Σ X : Type, Σ p : Presentation X, Σ S : SubstInfo, Y p S → Ground
  State a := Term a.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Ground
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a t => evaluate (fill a.2.1 a.2.2.1 a.2.2.2) t) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => .of true) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) (w : Y p S → Ground) (x : X),
    _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext p C S hok w x = (F.readout () ⟨X,p,S,w⟩ (action p S x))

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext_evaluate_action
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext_evaluate_action)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 1) [] SubstInfo.empty (empty_success _) (fun _ => .of false) 0
  change _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext (finPresentation 1) [] SubstInfo.empty (empty_success _) (fun _ => .of false) 0 = FreeMagma.of true at hh
  simp [_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext, sigma, action_identity _ _ _ (empty_unbound _ _), restrictTerm, evaluate] at hh
  cases hh

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext_evaluate_action)) where
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
    refine ⟨⟨Fin 0, finPresentation 0, SubstInfo.empty, fun x => Fin.elim0 x.val⟩,
      .of (.inl false), .of (.inl true), ?_⟩
    decide +kernel
end Audit_Ext_evaluate_action


namespace Audit_groundDecoder_exact
abbrev signature : Signature where
  Params := Unit
  State a := LMonoTy
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Option Ground
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ t => groundDecoder t) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => none) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (t : LMonoTy) (u : Ground),
    (F.readout () () t) = some u ↔ encodeGround u = t

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundDecoder_exact
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundDecoder_exact)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := (h (leaf false) (.of false)).mpr rfl
  cases hh

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundDecoder_exact)) where
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
    refine ⟨(), leaf false, leaf true, ?_⟩
    decide +kernel
end Audit_groundDecoder_exact


namespace Audit_output_keys
abbrev signature : Signature where
  Params := Unit
  State a := Subst
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := List String
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ S => S.keys) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => ["bad"]) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S),
    ∀ k ∈ (F.readout () () S.subst), ∃ x, p.code x = k

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.output_keys
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.output_keys)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨x, hx⟩ := h (finPresentation 0) [] SubstInfo.empty (empty_success _) "bad"
    (by change "bad" ∈ ["bad"]; simp)
  exact Fin.elim0 x

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.output_keys)) where
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
    refine ⟨(), [], [HMap.single "v" (leaf false)], ?_⟩
    intro h
    change HMaps.keys ([] : Subst) = HMaps.keys [HMap.single "v" (leaf false)] at h
    have hb : "v" ∈ HMaps.keys [HMap.single "v" (leaf false)] := by simp [HMaps.keys, HMap.mem_keys_single_iff]
    rw [← h] at hb
    simp [HMaps.keys] at hb
end Audit_output_keys

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace
