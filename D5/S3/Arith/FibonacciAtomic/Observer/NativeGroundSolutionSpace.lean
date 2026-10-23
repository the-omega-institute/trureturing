/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: All ground solutions of native equations and exact constraint pullback. -/

import D5.S0.Rewriting.UnificationCompleteness
import D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace
open Lambda Strata.Util NativeTermUnification

abbrev Source := GenealogicalFiberTransport.Source
abbrev Equations (X : Type) := List (Term X × Term X)

variable {X : Type}

def encodeEquations (p : Presentation X) (C : Equations X) : Constraints :=
  C.map (fun c => (encode p c.1, encode p c.2))

def Sol (C : Equations X) (v : X → Source) : Prop :=
  ∀ c ∈ C, evaluate v c.1 = evaluate v c.2

def groundValue (p : Presentation X) (v : X → Source) (s : String) : LMonoTy :=
  encodeGround (match p.decode s with | some x => v x | none => .of false)

/-- A finite ground assignment binds all original variables and leaves every
other identifier unbound. -/
def groundSubst (p : Presentation X) (v : X → Source) : Subst :=
  [HMap.ofList ((p.enumeration.map p.code).map (fun s => (s, groundValue p v s)))]

theorem groundSubst_find (p : Presentation X) (v : X → Source) (x : X) :
    (groundSubst p v).find? (p.code x) = some (encodeGround (v x)) := by
  rw [groundSubst, HMaps.find?_single_scope]
  have h := HMap.find?_ofList_self_map (p.enumeration.map p.code) (groundValue p v)
    (p.code x) (List.mem_map.mpr ⟨x, p.complete x, rfl⟩)
  simpa [groundValue, p.decode_code] using h

theorem groundSubst_other (p : Presentation X) (v : X → Source) (s : String)
    (hs : ∀ x, p.code x ≠ s) : (groundSubst p v).find? s = none := by
  rw [groundSubst, HMaps.find?_single_scope]
  apply HMap.not_mem_keys_find?_none
  intro hk
  have hk' : s ∈ p.enumeration.map p.code := by
    simpa only [List.map_map, Function.comp_def] using HMap.mem_keys_ofList _ s hk
  obtain ⟨x, hx, he⟩ := List.mem_map.mp hk'
  exact hs x he

theorem groundSubst_evaluate (p : Presentation X) (v : X → Source) (t : Term X) :
    LMonoTy.subst (groundSubst p v) (encode p t) = encodeGround (evaluate v t) := by
  induction t with
  | of a => cases a with
    | inl b => cases b <;> simp [encode, leaf, LMonoTy.subst_tcons,
        LMonoTys.subst_eq_map, evaluate, encodeGround, FreeMagma.lift_of]
    | inr x => simp [encode, LMonoTy.subst_unfold, groundSubst_find, evaluate]
  | mul a b ha hb =>
    simpa [encode, pair, LMonoTy.subst_tcons, LMonoTys.subst_eq_map,
      evaluate, encodeGround, map_mul] using congrArg₂ pair ha hb

/-- Injectivity retains the two distinct Boolean labels and ordered branches. -/
theorem encodeGround_injective : Function.Injective encodeGround := by
  intro a
  induction a with
  | of b =>
    intro t h
    cases t with
    | of c => cases b <;> cases c <;> simp_all [encodeGround, leaf]
    | mul l r => cases b <;> simp_all [encodeGround, leaf, pair]
  | mul a b ha hb =>
    intro t h
    cases t with
    | of c => cases c <;> simp_all [encodeGround, leaf, pair]
    | mul l r =>
      simp only [encodeGround, pair, LMonoTy.tcons.injEq, List.cons.injEq] at h
      exact congrArg₂ FreeMagma.mul (ha h.2.1) (hb h.2.2.1)

theorem groundSubst_sol (p : Presentation X) (C : Equations X) (v : X → Source)
    (hv : Sol C v) :
    ∀ c ∈ encodeEquations p C,
      LMonoTy.subst (groundSubst p v) c.1 = LMonoTy.subst (groundSubst p v) c.2 := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  simp only [groundSubst_evaluate]
  exact congrArg encodeGround (hv d hd)

/-- Native satisfiability implies success of the actual unifier. -/
theorem native_complete (p : Presentation X) (C : Equations X) (v : X → Source)
    (hv : Sol C v) : ∃ S, (encodeEquations p C).unify SubstInfo.empty = .ok S := by
  apply Constraints.unify_complete _ _ (groundSubst p v) (groundSubst_sol p C v hv)
  intro s t h
  simp [SubstInfo.empty, Subst.empty, HMaps.find?] at h

/-- Successful output values have the exact native constructor shape. -/
theorem output_native (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) : NativeSubst S.subst := by
  apply unify_native _ _ _ hok
  · intro t ht; simp [SubstInfo.empty, Subst.empty, HMaps.values] at ht
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact ⟨encode_shape p d.1, encode_shape p d.2⟩

theorem equations_supported (p : Presentation X) (C : Equations X) (s : String)
    (hs : s ∈ (encodeEquations p C).freeVars) : ∃ x, p.code x = s := by
  induction C with
  | nil => simp [encodeEquations, Constraints.freeVars] at hs
  | cons c rest ih =>
    simp only [encodeEquations, List.map_cons, Constraints.freeVars,
      Constraint.freeVars, List.mem_append] at hs
    rcases hs with (h | h) | h
    · exact encode_supported p c.1 s h
    · exact encode_supported p c.2 s h
    · exact ih h

theorem output_supported (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) :
    ∀ s ∈ Subst.freeVars S.subst, ∃ x, p.code x = s := by
  unfold Constraints.unify at hok
  simp only [Bind.bind, Except.bind] at hok
  split at hok
  · simp at hok
  · rename_i rel hr
    cases hok
    intro s hs
    have h := rel.goodSubset hs
    simp only [SubstInfo.empty, Subst.empty, Subst.freeVars, HMaps.values,
      List.flatMap_nil, List.append_nil] at h
    exact equations_supported p C s h

/-- Every original variable has a total action, including unbound and unused
termVars. The default is unreachable on a successful native output. -/
def action (p : Presentation X) (S : SubstInfo) (x : X) : Term X :=
  (nativeDecode p (LMonoTy.subst S.subst (.ftvar (p.code x)))).getD (.of (.inr x))

theorem action_encode (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) (x : X) :
    encode p (action p S x) = LMonoTy.subst S.subst (.ftvar (p.code x)) := by
  have hs := output_native p C S hok
  have ht := shape_subst S.subst hs (.ftvar (p.code x)) (Shape.var _)
  have hu : Supported p (LMonoTy.subst S.subst (.ftvar (p.code x))) := by
    intro s h
    rcases List.mem_append.mp (LMonoTy.freeVars_of_subst_subset S.subst (.ftvar (p.code x)) h)
      with h | h
    · simp only [LMonoTy.freeVars, List.mem_singleton] at h
      exact ⟨x, h.symm⟩
    · exact output_supported p C S hok s h
  obtain ⟨a, hd⟩ := (decode_domain p _).2 ⟨ht, hu⟩
  have he := encode_decode p _ a hd
  simpa only [action, hd, Option.getD_some] using he

/-- The bound set is the actual key set, restricted to the original variables. -/
def D (p : Presentation X) (S : SubstInfo) : Set X := {x | p.code x ∈ S.subst.keys}
abbrev Y (p : Presentation X) (S : SubstInfo) := {x : X // x ∉ D p S}

end D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace
open Lambda Strata.Util NativeTermUnification
variable {X : Type}

def termVars : Term X → List X
  | .of (.inl _) => []
  | .of (.inr x) => [x]
  | .mul a b => termVars a ++ termVars b

theorem encode_variables (p : Presentation X) (t : Term X) :
    (encode p t).freeVars = (termVars t).map p.code := by
  induction t with
  | of a => cases a with
    | inl b => cases b <;> simp [encode, leaf, termVars, LMonoTy.freeVars, LMonoTys.freeVars]
    | inr x => rfl
  | mul a b ha hb => simp [encode, pair, termVars, LMonoTy.freeVars, LMonoTys.freeVars, ha, hb]

theorem action_support (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) (x y : X)
    (hy : y ∈ termVars (action p S x)) : y ∉ D p S := by
  have hkey := LMonoTy.subst_keys_not_in_substituted_type S.isWF (.ftvar (p.code x))
  simp only [List.all_eq_true, decide_eq_true_eq] at hkey
  intro hd
  apply hkey (p.code y) hd
  rw [← action_encode p C S hok x, encode_variables]
  exact List.mem_map.mpr ⟨y, hy, rfl⟩

theorem action_identity (p : Presentation X) (S : SubstInfo) (x : X)
    (hx : x ∉ D p S) : action p S x = .of (.inr x) := by
  have hf := HMaps.not_mem_keys_find?_none S.subst (p.code x) hx
  simp [action, LMonoTy.subst_unfold, hf, nativeDecode, p.decode_code]

theorem bound_iff_nonidentity (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) (x : X) :
    x ∈ D p S ↔ action p S x ≠ .of (.inr x) := by
  constructor
  · intro hd he
    have hy : x ∈ termVars (action p S x) := by simp [he, termVars]
    exact action_support p C S hok x x hy hd
  · intro hn
    by_contra hd
    exact hn (action_identity p S x hd)

/-- Relabel a term's termVars by the complement of the actual bound keys.
The supplied support proof changes labels only; it does not normalize terms. -/
def restrictTerm (p : Presentation X) (S : SubstInfo) :
    (t : Term X) → (∀ x ∈ termVars t, x ∉ D p S) → Term (Y p S)
  | .of (.inl b), _ => .of (.inl b)
  | .of (.inr x), h => .of (.inr ⟨x, h x (by simp [termVars])⟩)
  | .mul a b, h => .mul (restrictTerm p S a (fun x hx => h x (List.mem_append_left _ hx)))
      (restrictTerm p S b (fun x hx => h x (List.mem_append_right _ hx)))

def sigma (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) (x : X) : Term (Y p S) :=
  restrictTerm p S (action p S x) (fun y hy => action_support p C S hok x y hy)

/-- Extend an arbitrary assignment on the unbound original variables. -/
def Ext (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S)
    (w : Y p S → Source) (x : X) : Source := evaluate w (sigma p C S hok x)

def restriction (p : Presentation X) (S : SubstInfo) (v : X → Source) : Y p S → Source :=
  fun y => v y.val

theorem evaluate_restrictTerm (p : Presentation X) (S : SubstInfo) (v : X → Source)
    (t : Term X) (h : ∀ x ∈ termVars t, x ∉ D p S) :
    evaluate (restriction p S v) (restrictTerm p S t h) = evaluate v t := by
  induction t with
  | of a => cases a <;> rfl
  | mul a b ha hb =>
    change evaluate (restriction p S v) (restrictTerm p S a _) *
      evaluate (restriction p S v) (restrictTerm p S b _) = evaluate v a * evaluate v b
    exact congrArg₂ FreeMagma.mul (ha _) (hb _)

theorem restriction_Ext (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) (w : Y p S → Source) :
    restriction p S (Ext p C S hok w) = w := by
  funext y
  simp only [restriction, Ext, sigma, action_identity p S y.val y.property]
  rfl

/-- Every ground solution is the extension of its exact restriction. -/
theorem Ext_restriction (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) (v : X → Source)
    (hv : Sol C v) : Ext p C S hok (restriction p S v) = v := by
  have ha := Constraints.unify_mgu (encodeEquations p C) SubstInfo.empty S hok
    (groundSubst p v) (groundSubst_sol p C v hv)
    (by intro s t h; simp [SubstInfo.empty, Subst.empty, HMaps.find?] at h)
  funext x
  apply encodeGround_injective
  have h := LMonoTy.subst_absorbs (groundSubst p v) S.subst (.ftvar (p.code x)) ha
  rw [← action_encode p C S hok x, groundSubst_evaluate,
    LMonoTy.subst_unfold] at h
  simpa [Ext, sigma, evaluate_restrictTerm, groundSubst_find] using h

/-- Groundness of a native constructor tree is exactly empty variable support. -/
theorem shape_ground (t : LMonoTy) (ht : Shape t) (hf : t.freeVars = []) :
    ∃ u : Source, encodeGround u = t := by
  induction ht with
  | var s => simp [LMonoTy.freeVars] at hf
  | bool b => exact ⟨.of b, rfl⟩
  | @mul a b ha hb iha ihb =>
    have he : a.freeVars = [] ∧ b.freeVars = [] := by
      simpa [pair, LMonoTy.freeVars, LMonoTys.freeVars] using hf
    obtain ⟨u, hu⟩ := iha he.1
    obtain ⟨v, hv⟩ := ihb he.2
    exact ⟨.mul u v, by simp only [encodeGround, hu, hv]⟩

theorem encodeGround_freeVars (u : Source) : (encodeGround u).freeVars = [] := by
  induction u with
  | of b => cases b <;> simp [encodeGround, leaf, LMonoTy.freeVars, LMonoTys.freeVars]
  | mul u v hu hv => simp [encodeGround, pair, LMonoTy.freeVars, LMonoTys.freeVars, hu, hv]

/-- Shape is essential: a foreign nullary constructor or a bit vector has
empty free-variable support but is not a native ground tree. -/
theorem native_ground_iff (t : LMonoTy) (ht : Shape t) :
    t.freeVars = [] ↔ ∃! u : Source, encodeGround u = t := by
  constructor
  · intro hf
    obtain ⟨u, hu⟩ := shape_ground t ht hf
    exact ⟨u, hu, fun v hv => encodeGround_injective (hv.trans hu.symm)⟩
  · rintro ⟨u, hu, _⟩
    rw [← hu]
    exact encodeGround_freeVars u

end D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace
open Lambda Strata.Util NativeTermUnification
variable {X : Type}

/-- Simultaneous action on terms via the existing free-magma lift. -/
def substitute (f : X → Term X) : Term X → Term X :=
  FreeMagma.lift (Sum.elim (fun b => .of (.inl b)) f)

theorem substitute_evaluate (f : X → Term X) (v : X → Source) (t : Term X) :
    evaluate v (substitute f t) = evaluate (fun x => evaluate v (f x)) t := by
  have h :
      (FreeMagma.lift (Sum.elim FreeMagma.of v)).comp
        (FreeMagma.lift (Sum.elim (fun b => .of (.inl b)) f)) =
      FreeMagma.lift (Sum.elim FreeMagma.of (fun x => evaluate v (f x))) := by
    apply FreeMagma.hom_ext
    funext a
    cases a <;> rfl
  exact congrArg (fun F : Term X →ₙ* Source => F t) h

theorem action_substitute_encode (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) (t : Term X) :
    encode p (substitute (action p S) t) = LMonoTy.subst S.subst (encode p t) := by
  induction t with
  | of a => cases a with
    | inl b => cases b <;> simp [substitute, encode, leaf, LMonoTy.subst_tcons,
        LMonoTys.subst_eq_map]
    | inr x => exact action_encode p C S hok x
  | mul a b ha hb =>
    simpa [substitute, encode, pair, LMonoTy.subst_tcons, LMonoTys.subst_eq_map,
      map_mul] using congrArg₂ pair ha hb

/-- The action is already normalized by the algorithm's well-formedness
invariant; no recursive normalizer is used. -/
theorem action_idempotent (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) (x : X) :
    substitute (action p S) (action p S x) = action p S x := by
  apply encode_injective p
  rw [action_substitute_encode p C S hok, action_encode p C S hok,
    LMonoTy.subst_idempotent S.subst S.isWF]

/-- Fill bound coordinates only to compare evaluations; they never occur in
sigma and therefore do not affect the extension. -/
def fill (p : Presentation X) (S : SubstInfo) (w : Y p S → Source) (x : X) : Source :=
  if h : p.code x ∈ S.subst.keys then .of false else w ⟨x, h⟩

theorem restriction_fill (p : Presentation X) (S : SubstInfo) (w : Y p S → Source) :
    restriction p S (fill p S w) = w := by
  funext y
  have hy : p.code y.val ∉ S.subst.keys := y.property
  simp only [restriction, fill, dif_neg hy]

theorem Ext_evaluate_action (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) (w : Y p S → Source) (x : X) :
    Ext p C S hok w x = evaluate (fill p S w) (action p S x) := by
  unfold Ext sigma
  calc
    _ = evaluate (restriction p S (fill p S w)) (restrictTerm p S (action p S x) _) :=
      congrArg (fun f => evaluate f (restrictTerm p S (action p S x) _))
        (restriction_fill p S w).symm
    _ = _ := evaluate_restrictTerm p S (fill p S w) (action p S x) _

/-- Every parameter assignment solves all original equations under the same
extension, including repeated and shared original variables. -/
theorem Ext_sol (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) (w : Y p S → Source) :
    Sol C (Ext p C S hok w) := by
  intro c hc
  have h := Constraints.unify_sound (encodeEquations p C) SubstInfo.empty S hok
    (encode p c.1, encode p c.2) (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have he : substitute (action p S) c.1 = substitute (action p S) c.2 := by
    apply encode_injective p
    simpa only [action_substitute_encode p C S hok] using h
  have hv : (fun x => evaluate (fill p S w) (action p S x)) = Ext p C S hok w :=
    funext fun x => (Ext_evaluate_action p C S hok w x).symm
  rw [← hv, ← substitute_evaluate, ← substitute_evaluate, he]

/-- The entire set of original ground solutions is parameterized bijectively
by all unbound original variables. -/
def solutionEquiv (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) :
    (Y p S → Source) ≃ {v : X → Source // Sol C v} where
  toFun w := ⟨Ext p C S hok w, Ext_sol p C S hok w⟩
  invFun v := restriction p S v.val
  left_inv := restriction_Ext p C S hok
  right_inv v := Subtype.ext (Ext_restriction p C S hok v.val v.property)

/-- Original disequalities are evaluated on the whole original assignment;
variables omitted from the new equations remain present. -/
def Diseq (Delta : Equations X) (v : X → Source) : Prop :=
  ∀ d ∈ Delta, evaluate v d.1 ≠ evaluate v d.2

/-- The constrained parameter space is an exact subtype of the same parameter
space. No product decomposition or decision procedure for G is asserted. -/
def constrainedEquiv (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S)
    (Delta : Equations X) (G : (X → Source) → Prop) :
    {w : Y p S → Source // Diseq Delta (Ext p C S hok w) ∧ G (Ext p C S hok w)} ≃
    {v : X → Source // Sol C v ∧ Diseq Delta v ∧ G v} where
  toFun w := ⟨Ext p C S hok w.val, Ext_sol p C S hok w.val, w.property⟩
  invFun v := ⟨restriction p S v.val, by
    rw [Ext_restriction p C S hok v.val v.property.1]
    exact v.property.2⟩
  left_inv w := Subtype.ext (restriction_Ext p C S hok w.val)
  right_inv v := Subtype.ext (Ext_restriction p C S hok v.val v.property.1)

/-- The all-variable action also keeps its normalized form under another
application. This includes unused variables and alias outputs. -/
theorem total_action_spec (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) :
    ∀ x, substitute (action p S) (action p S x) = action p S x ∧
      (∀ y ∈ termVars (action p S x), y ∉ D p S) ∧
      (x ∉ D p S → action p S x = .of (.inr x)) ∧
      (x ∈ D p S ↔ action p S x ≠ .of (.inr x)) := by
  intro x
  exact ⟨action_idempotent p C S hok x, fun y hy => action_support p C S hok x y hy,
    action_identity p S x, bound_iff_nonidentity p C S hok x⟩

end D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace
open Lambda Strata.Util NativeTermUnification
variable {X : Type}

/-- Effective ground decoding uses the exact fragment with zero variables. -/
def groundDecoder (t : LMonoTy) : Option Source :=
  (nativeDecode (finPresentation 0) t).map (evaluate (fun x : Fin 0 => Fin.elim0 x))

/-- A successful ground nativeDecode is exactly an actual native ground encoding. -/
theorem groundDecoder_exact (t : LMonoTy) (u : Source) :
    groundDecoder t = some u ↔ encodeGround u = t := by
  have hzero : ∀ a : Term (Fin 0),
      encodeGround (evaluate (fun x : Fin 0 => Fin.elim0 x) a) = encode (finPresentation 0) a := by
    intro a
    induction a with
    | of z => cases z with
      | inl b => rfl
      | inr x => exact Fin.elim0 x
    | mul a b ha hb =>
      change pair (encodeGround (evaluate (fun x : Fin 0 => Fin.elim0 x) a))
        (encodeGround (evaluate (fun x : Fin 0 => Fin.elim0 x) b)) =
        pair (encode (finPresentation 0) a) (encode (finPresentation 0) b)
      exact congrArg₂ pair ha hb
  constructor
  · intro h
    obtain ⟨a, ha, hu⟩ := Option.map_eq_some_iff.mp h
    rw [← hu, hzero]
    exact encode_decode (finPresentation 0) t a ha
  · intro hu
    let a : Term (Fin 0) := FreeMagma.lift (fun b : Bool => .of (.inl b)) u
    have heval : evaluate (fun x : Fin 0 => Fin.elim0 x) a = u := by
      dsimp only [a]
      clear hu
      induction u with
      | of b => rfl
      | mul l r hl hr =>
        change evaluate (fun x : Fin 0 => Fin.elim0 x)
          (FreeMagma.lift (fun b : Bool => .of (.inl b)) l) *
          evaluate (fun x : Fin 0 => Fin.elim0 x)
          (FreeMagma.lift (fun b : Bool => .of (.inl b)) r) = l * r
        exact congrArg₂ FreeMagma.mul hl hr
    have ha : encode (finPresentation 0) a = t := by rw [← hzero, heval, hu]
    simp only [groundDecoder, ← ha, decode_encode, Option.map_some, heval]

/-- Key support, separately from constructor shape, remains in the original
alphabet after actual success. -/
theorem output_keys (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) :
    ∀ k ∈ S.subst.keys, ∃ x, p.code x = k := by
  unfold Constraints.unify at hok
  simp only [Bind.bind, Except.bind] at hok
  split at hok
  · simp at hok
  · rename_i rel hr
    cases hok
    intro k hk
    have h := (Constraints.unifyCore_sound _ _ rel hr).keys_incl k hk
    simp only [SubstInfo.empty, Subst.empty, HMaps.keys, List.not_mem_nil,
      Subst.freeVars, HMaps.values, List.flatMap_nil, false_or, or_false] at h
    exact equations_supported p C k h

/-- Complete successful-output interface. Every original coordinate, every
old disequality and every supplied guard remains in this same parameterization. -/
structure Parameterization (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) where
  keys_original : ∀ k ∈ S.subst.keys, ∃ x, p.code x = k
  action_laws : ∀ x, substitute (action p S) (action p S x) = action p S x ∧
    (∀ y ∈ termVars (action p S x), y ∉ D p S) ∧
    (x ∉ D p S → action p S x = .of (.inr x)) ∧
    (x ∈ D p S ↔ action p S x ≠ .of (.inr x))
  ground_exact : ∀ x, termVars (action p S x) = [] ↔
    ∃! u : Source, groundDecoder (LMonoTy.subst S.subst (.ftvar (p.code x))) = some u
  ground_bindings : ∀ (v : X → Source) (s : String), (∀ x, p.code x ≠ s) →
    (groundSubst p v).find? s = none
  solutions : (Y p S → Source) ≃ {v : X → Source // Sol C v}
  constrained : ∀ (Delta : Equations X) (G : (X → Source) → Prop),
    {w : Y p S → Source // Diseq Delta (Ext p C S hok w) ∧ G (Ext p C S hok w)} ≃
    {v : X → Source // Sol C v ∧ Diseq Delta v ∧ G v}

/-- Construct all fields from the actual successful output and the original
soundness, MGU and normalization suppliers. -/
def parameterization (p : Presentation X) (C : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S) : Parameterization p C S hok where
  keys_original := output_keys p C S hok
  action_laws := total_action_spec p C S hok
  ground_exact x := by
    have ht := shape_subst S.subst (output_native p C S hok) (.ftvar (p.code x)) (Shape.var _)
    have hf := native_ground_iff (LMonoTy.subst S.subst (.ftvar (p.code x))) ht
    have hm : termVars (action p S x) = [] ↔
        (LMonoTy.subst S.subst (.ftvar (p.code x))).freeVars = [] := by
      rw [← action_encode p C S hok x, encode_variables]
      simp
    rw [hm, hf]
    constructor
    · rintro ⟨u, hu, huniq⟩
      exact ⟨u, (groundDecoder_exact _ _).2 hu,
        fun v hv => huniq v ((groundDecoder_exact _ _).1 hv)⟩
    · rintro ⟨u, hu, huniq⟩
      exact ⟨u, (groundDecoder_exact _ _).1 hu,
        fun v hv => huniq v ((groundDecoder_exact _ _).2 hv)⟩
  ground_bindings := groundSubst_other p
  solutions := solutionEquiv p C S hok
  constrained := constrainedEquiv p C S hok

end D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace
