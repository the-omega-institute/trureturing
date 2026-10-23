import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

open NativeTermUnification Lambda Strata.Util
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace

abbrev Ground := _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Source

theorem empty_success {X : Type} (p : Presentation X) :
    (encodeEquations p []).unify SubstInfo.empty = .ok SubstInfo.empty := by
  change Constraints.unify [] SubstInfo.empty = .ok SubstInfo.empty
  unfold Constraints.unify
  rw [Constraints.unifyCore.eq_def]
  rfl

theorem empty_unbound {X : Type} (p : Presentation X) (x : X) : x ∉ D p SubstInfo.empty := by
  simp [D, SubstInfo.empty, Subst.empty, HMaps.keys]

def y0 : Y (finPresentation 1) SubstInfo.empty := ⟨0, empty_unbound _ _⟩

def testInfo : SubstInfo :=
  ⟨Subst.singleton "" (leaf false), SubstWF.single_subst _ _
    (by simp [leaf, LMonoTy.freeVars, LMonoTys.freeVars])⟩

namespace Audit_groundSubst_find
abbrev signature : Signature where
  Params := Σ X : Type, Σ p : Presentation X, X → Ground
  State a := String
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Option LMonoTy
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a s => (groundSubst a.2.1 a.2.2).find? s) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => none) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (v : X → Ground) (x : X),
    (F.readout () ⟨X,p,v⟩ (p.code x)) = some (encodeGround (v x))

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundSubst_find
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundSubst_find)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 1) (fun _ => .of false) 0
  cases hh

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundSubst_find)) where
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
    refine ⟨⟨Fin 1, finPresentation 1, fun _ => .of false⟩, "", "foreign", ?_⟩
    change (groundSubst (finPresentation 1) (fun _ => .of false)).find? "" ≠
      (groundSubst (finPresentation 1) (fun _ => .of false)).find? "foreign"
    have h1 := groundSubst_find (finPresentation 1) (fun _ => .of false) (0 : Fin 1)
    have h2 := groundSubst_other (finPresentation 1) (fun _ => .of false) "foreign"
      (by intro x; fin_cases x; decide +kernel)
    change (groundSubst (finPresentation 1) (fun _ => .of false)).find? "" = some (encodeGround (.of false)) at h1
    rw [h1, h2]
    simp
end Audit_groundSubst_find


namespace Audit_groundSubst_other
abbrev signature : Signature where
  Params := Σ X : Type, Σ p : Presentation X, X → Ground
  State a := String
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Option LMonoTy
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a s => (groundSubst a.2.1 a.2.2).find? s) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => some (.bitvec 0)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (v : X → Ground) (s : String)
    (hs : ∀ x, p.code x ≠ s),
    (F.readout () ⟨X,p,v⟩ s) = none

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundSubst_other
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundSubst_other)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 0) (fun x => Fin.elim0 x) "bad" (by intro x; exact Fin.elim0 x)
  cases hh

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundSubst_other)) where
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
    refine ⟨⟨Fin 1, finPresentation 1, fun _ => .of false⟩, "", "foreign", ?_⟩
    change (groundSubst (finPresentation 1) (fun _ => .of false)).find? "" ≠
      (groundSubst (finPresentation 1) (fun _ => .of false)).find? "foreign"
    have h1 := groundSubst_find (finPresentation 1) (fun _ => .of false) (0 : Fin 1)
    have h2 := groundSubst_other (finPresentation 1) (fun _ => .of false) "foreign"
      (by intro x; fin_cases x; decide +kernel)
    change (groundSubst (finPresentation 1) (fun _ => .of false)).find? "" = some (encodeGround (.of false)) at h1
    rw [h1, h2]
    simp
end Audit_groundSubst_other


namespace Audit_groundSubst_evaluate
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
  Law F := ∀ {X : Type} (p : Presentation X) (v : X → Ground) (t : Term X),
    LMonoTy.subst (groundSubst p v) (encode p t) = (F.readout () () (evaluate v t))

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundSubst_evaluate
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundSubst_evaluate)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 0) (fun x => Fin.elim0 x) (.of (.inl false))
  have hn : LMonoTy.subst (groundSubst (finPresentation 0) (fun x => Fin.elim0 x))
      (encode (finPresentation 0) (.of (.inl false))) ≠ .bitvec 0 := by decide +kernel
  exact hn hh

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundSubst_evaluate)) where
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
end Audit_groundSubst_evaluate


namespace Audit_encodeGround_injective
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
  Law F := Function.Injective ((fun u => F.readout () () u))

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.encodeGround_injective
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.encodeGround_injective)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (a₁ := .of false) (a₂ := .of true) rfl
  cases hh

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.encodeGround_injective)) where
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
end Audit_encodeGround_injective


namespace Audit_groundSubst_sol
abbrev signature : Signature where
  Params := Σ X : Type, Σ p : Presentation X, X → Ground
  State a := LMonoTy
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := LMonoTy
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a t => LMonoTy.subst (groundSubst a.2.1 a.2.2) t) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => .bitvec 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (C : Equations X) (v : X → Ground)
    (hv : Sol C v),
    ∀ c ∈ encodeEquations p C,
      (F.readout () ⟨X,p,v⟩ c.1) = LMonoTy.subst (groundSubst p v) c.2

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundSubst_sol
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundSubst_sol)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  let C : Equations (Fin 0) := [(.of (.inl false), .of (.inl false))]
  have hv : Sol C (fun x => Fin.elim0 x) := by intro c hc; change c ∈ [(.of (.inl false), .of (.inl false))] at hc; simp only [List.mem_singleton] at hc; subst c; rfl
  have hh := h (finPresentation 0) C (fun x => Fin.elim0 x) hv _ (List.mem_singleton_self _)
  have hn : LMonoTy.bitvec 0 ≠ LMonoTy.subst (groundSubst (finPresentation 0) (fun x => Fin.elim0 x))
      (encode (finPresentation 0) (.of (.inl false))) := by decide +kernel
  exact hn hh

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundSubst_sol)) where
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
    refine ⟨⟨Fin 0, finPresentation 0, fun x => Fin.elim0 x⟩, .bitvec 0, .bitvec 1, ?_⟩
    decide +kernel
end Audit_groundSubst_sol


namespace Audit_native_complete
abbrev signature : Signature where
  Params := Σ X : Type, Presentation X
  State a := Equations a.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Constraints
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a C => encodeEquations a.2 C) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => [(.bitvec 0, .bitvec 1)]) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (C : Equations X) (v : X → Ground)
    (hv : Sol C v),
    ∃ S, ((F.readout () ⟨X,p⟩ C)).unify SubstInfo.empty = .ok S

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.native_complete
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.native_complete)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨S, hS⟩ := h (finPresentation 0) [] (fun x => Fin.elim0 x) (by intro c hc; cases hc)
  change Constraints.unify [(.bitvec 0, .bitvec 1)] SubstInfo.empty = .ok S at hS
  simp [Constraints.unify, Constraints.unifyCore.eq_def, Constraint.unifyOne.eq_def,
    Bind.bind, Except.bind, Except.mapError] at hS

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.native_complete)) where
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
    refine ⟨⟨Fin 0, finPresentation 0⟩, [], [(.of (.inl false), .of (.inl false))], ?_⟩
    decide +kernel
end Audit_native_complete


namespace Audit_output_native
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
  Law F := ∀ {X : Type} (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S),
    NativeSubst (F.readout () () S)

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.output_native
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.output_native)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 0) [] SubstInfo.empty (empty_success _)
  change NativeSubst [HMap.single "bad" (.bitvec 0)] at hh
  have hb := hh (.bitvec 0) (by simp [HMaps.values, HMap.mem_values_single_iff])
  cases hb

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.output_native)) where
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
    refine ⟨(), SubstInfo.empty, testInfo, ?_⟩
    intro h
    have hh := congrArg (fun S : Subst => S.find? "") h
    change SubstInfo.empty.subst.find? "" = testInfo.subst.find? "" at hh
    simp [SubstInfo.empty, Subst.empty, testInfo, Subst.singleton,
      HMaps.find?_single_scope, HMap.find?_single_self, HMaps.find?] at hh
end Audit_output_native


namespace Audit_equations_supported
abbrev signature : Signature where
  Params := Σ X : Type, Presentation X
  State a := Equations a.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := List String
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a C => (encodeEquations a.2 C).freeVars) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => ["bad"]) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (C : Equations X) (s : String)
    (hs : s ∈ (F.readout () ⟨X,p⟩ C)),
    ∃ x, p.code x = s

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.equations_supported
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.equations_supported)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨x, hx⟩ := h (finPresentation 0) [] "bad" (by change "bad" ∈ ["bad"]; simp)
  exact Fin.elim0 x

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.equations_supported)) where
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
    refine ⟨⟨Fin 1, finPresentation 1⟩, [], [(.of (.inr 0), .of (.inr 0))], ?_⟩
    decide +kernel
end Audit_equations_supported


namespace Audit_output_supported
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
  (fun _ _ S => Subst.freeVars S) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => ["bad"]) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S),
    ∀ s ∈ (F.readout () () S.subst), ∃ x, p.code x = s

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.output_supported
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.output_supported)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨x, hx⟩ := h (finPresentation 0) [] SubstInfo.empty (empty_success _) "bad"
    (by change "bad" ∈ ["bad"]; simp)
  exact Fin.elim0 x

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.output_supported)) where
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
    refine ⟨(), [], [HMap.single "v" (.ftvar "bad")], ?_⟩
    intro h
    change Subst.freeVars [] = Subst.freeVars [HMap.single "v" (.ftvar "bad")] at h
    have hb : "bad" ∈ Subst.freeVars [HMap.single "v" (.ftvar "bad")] := by
      simp only [Subst.freeVars, List.mem_flatMap]
      exact ⟨.ftvar "bad", by simp [HMaps.values, HMap.mem_values_single_iff], by simp [LMonoTy.freeVars]⟩
    rw [← h] at hb
    simp [Subst.freeVars, HMaps.values] at hb
end Audit_output_supported


namespace Audit_action_encode
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
    encode p ((F.readout () ⟨X,p,S⟩ x)) = LMonoTy.subst S.subst (.ftvar (p.code x))

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_encode
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_encode)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 1) [] SubstInfo.empty (empty_success _) 0
  have hn : encode (finPresentation 1) (.of (.inl true)) ≠
      LMonoTy.subst SubstInfo.empty.subst (.ftvar ((finPresentation 1).code 0)) := by decide +kernel
  exact hn hh

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_encode)) where
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
end Audit_action_encode


namespace Audit_encode_variables
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
  (fun _ _ _ => .ftvar "bad") (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (t : Term X),
    ((F.readout () ⟨X,p⟩ t)).freeVars = (termVars t).map p.code

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.encode_variables
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.encode_variables)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 0) (.of (.inl false))
  have hn : (LMonoTy.ftvar "bad").freeVars ≠ (termVars (.of (.inl false) : Term (Fin 0))).map (finPresentation 0).code := by decide +kernel
  exact hn hh

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.encode_variables)) where
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
end Audit_encode_variables


namespace Audit_action_support
abbrev signature : Signature where
  Params := Σ X : Type, Presentation X
  State a := SubstInfo
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Set a.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a S => D a.2 S) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => Set.univ) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {X : Type} (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) (x y : X)
    (hy : y ∈ termVars (action p S x)),
    y ∉ (F.readout () ⟨X,p⟩ S)

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_support
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_support)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 1) [] SubstInfo.empty (empty_success _) 0 0
    (by rw [action_identity _ _ _ (empty_unbound _ _)]; simp [termVars])
  exact hh (Set.mem_univ _)

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_support)) where
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
    refine ⟨⟨Fin 1, finPresentation 1⟩, SubstInfo.empty, testInfo, ?_⟩
    intro h
    have he : (0 : Fin 1) ∉ D (finPresentation 1) SubstInfo.empty := empty_unbound _ _
    have hs : (0 : Fin 1) ∈ D (finPresentation 1) testInfo := by
      simp [D, testInfo, Subst.singleton, HMaps.keys, HMap.mem_keys_single_iff, finPresentation, finName]
    change D (finPresentation 1) SubstInfo.empty = D (finPresentation 1) testInfo at h
    rw [h] at he
    exact he hs
end Audit_action_support


namespace Audit_action_identity
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
  Law F := ∀ {X : Type} (p : Presentation X) (S : SubstInfo) (x : X)
    (hx : x ∉ D p S),
    (F.readout () ⟨X,p,S⟩ x) = .of (.inr x)

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_identity
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_identity)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 1) SubstInfo.empty 0 (empty_unbound _ _)
  cases hh

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_identity)) where
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
end Audit_action_identity


namespace Audit_bound_iff_nonidentity
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
    x ∈ D p S ↔ (F.readout () ⟨X,p,S⟩ x) ≠ .of (.inr x)

theorem actual_law : arena.Law actual := @_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.bound_iff_nonidentity
theorem bridge : (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.bound_iff_nonidentity)) ↔ arena.Law actual := Iff.rfl
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (finPresentation 1) [] SubstInfo.empty (empty_success _) 0
  exact empty_unbound _ _ (hh.mpr (by intro he; cases he))

def registration : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.bound_iff_nonidentity)) where
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
end Audit_bound_iff_nonidentity

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace
