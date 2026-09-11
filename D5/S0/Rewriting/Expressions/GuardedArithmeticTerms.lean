/- GID: D5/S0/Rewriting/Expressions/GuardedArithmeticTerms
   generality: G
   mirror-B: D5/B/S0/Rewriting/Expressions/GuardedArithmeticTerms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite arithmetic terms have guarded realization and structural legality. -/

import Mathlib.ModelTheory.Semantics

set_option autoImplicit false

namespace D5.S0.Rewriting.Expressions.GuardedArithmeticTerms

open FirstOrder
universe u v w z

/-- Exactly the four arithmetic symbols; arity is part of the type. -/
inductive Symbol : Nat → Type
  | neg : Symbol 1
  | add : Symbol 2
  | mul : Symbol 2
  | div : Symbol 2

abbrev language : FirstOrder.Language := ⟨Symbol, fun _ => Empty⟩

/-- Mathlib's finite terms retain the ordered children and all brackets. -/
abbrev Expr (C : Type u) (V : Type v) := language.Term (C ⊕ V)

variable {C : Type u} {V : Type v} {R : Type w} {S : Type z}

def constant (c : C) : Expr C V := .var (.inl c)
def var (v : V) : Expr C V := .var (.inr v)
def neg (a : Expr C V) : Expr C V := Language.Functions.apply₁ Symbol.neg a
def add (a b : Expr C V) : Expr C V := Language.Functions.apply₂ Symbol.add a b
def mul (a b : Expr C V) : Expr C V := Language.Functions.apply₂ Symbol.mul a b
def div (a b : Expr C V) : Expr C V := Language.Functions.apply₂ Symbol.div a b

/-- Operation data only. Division consumes its actual domain proof. -/
structure Algebra (C : Type u) (R : Type w) where
  const : C → R
  neg : R → R
  add : R → R → R
  mul : R → R → R
  guard : R → R → Prop
  divide : (x y : R) → guard x y → R

noncomputable section

def divide? (A : Algebra C R) (x y : R) : Option R := by
  classical
  exact if h : A.guard x y then some (A.divide x y h) else none

def operation (A : Algebra C R) : {n : Nat} → Symbol n → (Fin n → Option R) → Option R
  | _, .neg, xs => (xs 0).map A.neg
  | _, .add, xs => (xs 0).bind fun x => (xs 1).map (A.add x)
  | _, .mul, xs => (xs 0).bind fun x => (xs 1).map (A.mul x)
  | _, .div, xs => (xs 0).bind fun x => (xs 1).bind (divide? A x)

@[instance_reducible]
def optionStructure (A : Algebra C R) : language.Structure (Option R) where
  funMap := operation A
  RelMap r := Empty.elim r

def eval (A : Algebra C R) (env : V → R) (e : Expr C V) : Option R :=
  @Language.Term.realize language (Option R) (optionStructure A) (C ⊕ V)
    (Sum.elim (fun c => some (A.const c)) (fun v => some (env v))) e

def Legal (A : Algebra C R) (env : V → R) (e : Expr C V) : Prop :=
  ∃ x, eval A env e = some x

/-- A division node records its two actual child results and its domain proof. -/
def NodeGuard (A : Algebra C R) : {n : Nat} → Symbol n → (Fin n → Option R) → Prop
  | _, .neg, _ => True
  | _, .add, _ => True
  | _, .mul, _ => True
  | _, .div, xs => ∃ x y, xs 0 = some x ∧ xs 1 = some y ∧ A.guard x y

/-- Recursion is on the library term: every child is retained at every node. -/
def AllLegal (A : Algebra C R) (env : V → R) : Expr C V → Prop
  | .var _ => True
  | .func f ts => (∀ i, AllLegal A env (ts i)) ∧
      NodeGuard A f (fun i => eval A env (ts i))

theorem operation_defined_iff (A : Algebra C R) {n : Nat}
    (f : Symbol n) (xs : Fin n → Option R) :
    (∃ x, operation A f xs = some x) ↔
      (∀ i, ∃ x, xs i = some x) ∧ NodeGuard A f xs := by
  classical
  cases f with
  | neg => cases h : xs 0 <;> simp [operation, NodeGuard, Fin.forall_fin_succ, h]
  | add =>
    cases h : xs 0 <;> cases k : xs 1 <;>
      simp [operation, NodeGuard, Fin.forall_fin_succ, h, k]
  | mul =>
    cases h : xs 0 <;> cases k : xs 1 <;>
      simp [operation, NodeGuard, Fin.forall_fin_succ, h, k]
  | div =>
    cases h : xs 0 with
    | none => simp [operation, NodeGuard, Fin.forall_fin_succ, h]
    | some x =>
      cases k : xs 1 with
      | none => simp [operation, NodeGuard, Fin.forall_fin_succ, k]
      | some y =>
        by_cases g : A.guard x y <;>
          simp [operation, NodeGuard, Fin.forall_fin_succ, h, k, divide?, g]

theorem legal_iff_allLegal (A : Algebra C R) (env : V → R) (e : Expr C V) :
    Legal A env e ↔ AllLegal A env e := by
  induction e with
  | var v => cases v <;> simp [Legal, eval, AllLegal, Language.Term.realize]
  | func f ts ih =>
    change (∃ x, operation A f (fun i => eval A env (ts i)) = some x) ↔ _
    rw [operation_defined_iff]
    exact and_congr (forall_congr' ih) Iff.rfl

theorem allLegal_div (A : Algebra C R) (env : V → R) (a b : Expr C V) :
    AllLegal A env (div a b) ↔ AllLegal A env a ∧ AllLegal A env b ∧
      ∃ x y, eval A env a = some x ∧ eval A env b = some y ∧ A.guard x y := by
  simp [div, Language.Functions.apply₂, AllLegal, NodeGuard, Fin.forall_fin_succ,
    and_assoc]

/-- Conditional transport: callers must prove these primitive preservation laws. -/
def mapHom (A : Algebra C R) (B : Algebra C S) (q : R → S)
    (hn : ∀ x, q (A.neg x) = B.neg (q x))
    (ha : ∀ x y, q (A.add x y) = B.add (q x) (q y))
    (hm : ∀ x y, q (A.mul x y) = B.mul (q x) (q y))
    (hg : ∀ x y, A.guard x y ↔ B.guard (q x) (q y))
    (hd : ∀ x y (h : A.guard x y),
      q (A.divide x y h) = B.divide (q x) (q y) ((hg x y).mp h)) :
    letI := optionStructure A
    letI := optionStructure B
    Option R →[language] Option S := by
  classical
  letI := optionStructure A
  letI := optionStructure B
  refine ⟨Option.map q, ?_, fun {_} r => Empty.elim r⟩
  intro n f xs
  change (operation A f xs).map q = operation B f (Option.map q ∘ xs)
  cases f with
  | neg => cases h : xs 0 <;> simp [operation, h, hn]
  | add => cases h : xs 0 <;> cases k : xs 1 <;>
      simp [operation, h, k, ha]
  | mul => cases h : xs 0 <;> cases k : xs 1 <;>
      simp [operation, h, k, hm]
  | div =>
    cases h : xs 0 with
    | none => simp [operation, h]
    | some x =>
      cases k : xs 1 with
      | none => simp [operation, k]
      | some y =>
        by_cases g : A.guard x y
        · simp [operation, h, k, divide?, g, (hg x y).mp g, hd]
        · simp [operation, h, k, divide?, g, mt (hg x y).mpr g]

theorem eval_map (A : Algebra C R) (B : Algebra C S) (q : R → S)
    (hc : ∀ c, q (A.const c) = B.const c)
    (hn : ∀ x, q (A.neg x) = B.neg (q x))
    (ha : ∀ x y, q (A.add x y) = B.add (q x) (q y))
    (hm : ∀ x y, q (A.mul x y) = B.mul (q x) (q y))
    (hg : ∀ x y, A.guard x y ↔ B.guard (q x) (q y))
    (hd : ∀ x y (h : A.guard x y),
      q (A.divide x y h) = B.divide (q x) (q y) ((hg x y).mp h))
    (env : V → R) (e : Expr C V) :
    (eval A env e).map q = eval B (q ∘ env) e := by
  let := optionStructure A
  let := optionStructure B
  let H := mapHom A B q hn ha hm hg hd
  have he := (Language.HomClass.realize_term H (t := e)
    (v := Sum.elim (fun c => some (A.const c)) (fun v => some (env v)))).symm
  change (eval A env e).map q = _ at he
  rw [he]
  apply congrArg (fun v => e.realize v)
  funext v
  cases v with
  | inl c => change some (q (A.const c)) = some (B.const c); rw [hc]
  | inr v => rfl

theorem legal_iff_of_eval_map (A : Algebra C R) (B : Algebra C S) (q : R → S)
    (env : V → R) (e : Expr C V)
    (h : (eval A env e).map q = eval B (q ∘ env) e) :
    Legal A env e ↔ Legal B (q ∘ env) e := by
  unfold Legal
  rw [← h]
  cases eval A env e <;> simp

end
end D5.S0.Rewriting.Expressions.GuardedArithmeticTerms
