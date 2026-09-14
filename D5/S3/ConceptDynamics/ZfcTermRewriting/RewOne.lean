/- GID: D5/S3/ConceptDynamics/ZfcTermRewriting/RewOne
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcTermRewriting/RewOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Syntax.Predicate.Rew for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcPredicate.Quantifier
public import D5.S3.ConceptDynamics.ZfcPredicate.Term
public import D5.S3.ConceptDynamics.ZfcSupport.Function

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Syntax/Predicate/Rew.lean, original lines 1-320.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

namespace LO

namespace FirstOrder

/--
A structure for maps which rewrite the semiterms occurring in a term.

toFun - A function from `Semiterm L ξ₁ n₁` to `Semiterm L ξ₂ n₂`.

func'' - A proof that `toFun` respects the function symbols of `L`.
-/
structure Rew (L : Language) (ξ₁ : Type*) (n₁ : ℕ) (ξ₂ : Type*) (n₂ : ℕ) where
  toFun : Semiterm L ξ₁ n₁ → Semiterm L ξ₂ n₂
  func'' (f : L.Func k) (v : Fin k → Semiterm L ξ₁ n₁) : toFun (Semiterm.func f v) = Semiterm.func f fun i ↦ toFun (v i)

abbrev SyntacticRew (L : Language) (n₁ n₂ : ℕ) := Rew L ℕ n₁ ℕ n₂

namespace Rew

open Semiterm
variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}
variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)

instance : FunLike (Rew L ξ₁ n₁ ξ₂ n₂) (Semiterm L ξ₁ n₁) (Semiterm L ξ₂ n₂) where
  coe := fun f => f.toFun
  coe_injective := fun f g h => by rcases f; rcases g; simpa using h

@[simp] protected lemma func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω (func f v) = func f (ω ∘ v) := ω.func'' f v

lemma func' {k} (f : L.Func k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω (func f v) = func f fun i ↦ ω (v i) := ω.func'' f v

@[ext] lemma ext (ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂) (hb : ∀ x, ω₁ #x = ω₂ #x) (hf : ∀ x, ω₁ &x = ω₂ &x) : ω₁ = ω₂ := by
  apply DFunLike.ext ω₁ ω₂; intro t
  induction t <;> simp [*, ω₁.func, ω₂.func, Function.comp_def]

lemma ext' {ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂} (h : ω₁ = ω₂) (t) : ω₁ t = ω₂ t := by simp [h]

protected def id : Rew L ξ n ξ n where
  toFun := id
  func'' := fun _ _ => rfl

@[simp] lemma id_app (t : Semiterm L ξ n) : Rew.id t = t := rfl

protected def comp (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) : Rew L ξ₁ n₁ ξ₃ n₃ where
  toFun := fun t => ω₂ (ω₁ t)
  func'' := fun f v => by simp; rfl

lemma comp_app (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁) :
    (ω₂.comp ω₁) t = ω₂ (ω₁ t) := rfl

def bindAux (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂) : Semiterm L ξ₁ n₁ → Semiterm L ξ₂ n₂
  |       #x => b x
  |       &x => e x
  | func f v => func f (fun i => bindAux b e (v i))

/-- `LO.FirstOrder.Rew.bind f` is a substitution of the bound variables occurring in a term by `b : Fin n₁ → Semiterm L ξ₂ n₂`, and the free variables occurring in a term by `e : ξ₁ → Semiterm L ξ₂ n₂`. -/
def bind (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂) : Rew L ξ₁ n₁ ξ₂ n₂ where
  toFun := bindAux b e
  func'' := fun _ _ => rfl

/-- `LO.FirstOrder.Rew.rewrite f` is a substitution of the free variables occurring in a term by `f : ξ₁ → Semiterm L ξ₂ n`. -/
def rewrite (f : ξ₁ → Semiterm L ξ₂ n) : Rew L ξ₁ n ξ₂ n := bind Semiterm.bvar f

/-- `LO.FirstOrder.Rew.rewriteMap` f is a substitution of the free variables occurring in a term by `e : ξ₁ → ξ₂`. -/
def rewriteMap (e : ξ₁ → ξ₂) : Rew L ξ₁ n ξ₂ n := rewrite (fun m => &(e m))

def map (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂) : Rew L ξ₁ n₁ ξ₂ n₂ :=
  bind (fun n => #(b n)) (fun m => &(e m))

/-- `LO.FirstOrder.Rew.subst v` is a substitution of the bound variables occurring in a term by `v : Fin n → Semiterm L ξ n'`. -/
def subst {n'} (v : Fin n → Semiterm L ξ n') : Rew L ξ n ξ n' :=
  bind v fvar

/-- `LO.FirstOrder.Rew.emb` is a embedding of a term with no free variables. It can be thought of as a cast from `Semiterm L Empty n` to `Semiterm L ξ n` for any type `ξ`. -/
def emb {o : Type v₁} [h : IsEmpty o] {ξ : Type v₂} {n} : Rew L o n ξ n := map id h.elim

/-- `LO.FirstOrder.Rew.bShift` is a transformation of the bounded variables occurring in a term by `#x ↦ #(Fin.succ x)`. -/
def bShift : Rew L ξ n ξ (n + 1) :=
  map Fin.succ id

/-- `LO.FirstOrder.Rew.embSubsts v` is a substitution of the bound variables occurring in a term with no free variables by `v : Fin n → Semiterm L ξ n'`.
This closely resembles `LO.FirstOrder.Rew.subst`, however the term is required to have free variables of type `Empty`. -/
def embSubsts (v : Fin k → Semiterm L ξ n) : Rew L Empty k ξ n := Rew.bind v Empty.elim

protected def q (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Rew L ξ₁ (n₁ + 1) ξ₂ (n₂ + 1) :=
  bind (#0 :> bShift ∘ ω ∘ bvar) (bShift ∘ ω ∘ fvar)

section bind

variable (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂)

@[simp] lemma bind_fvar (m : ξ₁) : bind b e (&m : Semiterm L ξ₁ n₁) = e m := rfl

@[simp] lemma bind_bvar (n : Fin n₁) : bind b e (#n : Semiterm L ξ₁ n₁) = b n := rfl

lemma eq_bind (ω : Rew L ξ₁ n₁ ξ₂ n₂) : ω = bind (ω ∘ bvar) (ω ∘ fvar) := by
  ext t; induction t
  · simp
  · simp [*]

@[simp] lemma bind_eq_id_of_zero (f : Fin 0 → Semiterm L ξ₂ 0) : bind f fvar = Rew.id := by
  ext x <;> simp only [bind_bvar, bind_fvar, id_app]; exact Fin.elim0 x

end bind

section map

variable (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂)

@[simp] lemma map_fvar (m : ξ₁) : map b e (&m : Semiterm L ξ₁ n₁) = &(e m) := rfl

@[simp] lemma map_bvar (n : Fin n₁) : map b e (#n : Semiterm L ξ₁ n₁) = #(b n) := rfl

lemma map_inj {b : Fin n₁ → Fin n₂} {e : ξ₁ → ξ₂} (hb : Function.Injective b) (he : Function.Injective e) :
    Function.Injective <| map (L := L) b e
  |                    #x,                    #y => by simpa using @hb _ _
  |                    #x,                    &y => by simp
  |                    #x,              func f w => by simp [Rew.func]
  |                    &x,                    #y => by simp
  |                    &x,                    &y => by simpa using @he _ _
  |                    &x,              func f w => by simp [Rew.func]
  |              func f v,                    #y => by simp [Rew.func]
  |              func f v,                    &y => by simp [Rew.func]
  | func (arity := k) f v, func (arity := l) g w => fun h ↦ by
    have : k = l := by simp [Rew.func] at h; simp_all
    rcases this
    have : f = g := by simp [Rew.func] at h; simp_all
    rcases this
    have : v = w := by
      have : (fun i ↦ (map b e) (v i)) = (fun i ↦ (map b e) (w i)) := by simpa [Rew.func, Function.comp_def] using h
      funext i; exact map_inj hb he (congrFun this i)
    simp_all

end map

section rewrite

variable (f : ξ₁ → Semiterm L ξ₂ n)

@[simp] lemma rewrite_fvar (x : ξ₁) : rewrite f &x = f x := rfl

@[simp] lemma rewrite_bvar (x : Fin n) : rewrite e (#x : Semiterm L ξ₁ n) = #x := rfl

end rewrite

section rewriteMap

variable (e : ξ₁ → ξ₂)

@[simp] lemma rewriteMap_fvar (x : ξ₁) : rewriteMap e (&x : Semiterm L ξ₁ n) = &(e x) := rfl

end rewriteMap

section emb

variable {o : Type v₂} [IsEmpty o]

@[simp] lemma emb_bvar (x : Fin n) : emb (ξ := ξ) (#x : Semiterm L o n) = #x := rfl

end emb

section bShift

@[simp] lemma bShift_bvar (x : Fin n) : bShift (#x : Semiterm L ξ n) = #(Fin.succ x) := rfl

@[simp] lemma bShift_fvar (x : ξ) : bShift (&x : Semiterm L ξ n) = &x := rfl

end bShift

section bShiftAdd

end bShiftAdd

section subst

variable {n'} (w : Fin n → Semiterm L ξ n')

@[simp] lemma subst_bvar (x : Fin n) : subst w #x = w x := by
  simp [subst]

@[simp] lemma subst_fvar (x : ξ) : subst w &x = &x := by
  simp [subst]

end subst

section cast

variable {n'} (h : n = n')

end cast
end Rew
end FirstOrder
end LO
end
