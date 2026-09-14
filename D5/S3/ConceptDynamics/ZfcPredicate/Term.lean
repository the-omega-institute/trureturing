/- GID: D5/S3/ConceptDynamics/ZfcPredicate/Term
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcPredicate/Term
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Syntax.Predicate.Term for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcPredicate.LanguageTwo

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Syntax/Predicate/Term.lean, original lines 1-253.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

namespace LO

namespace FirstOrder

/--
A semiterm of language `L`, with bound variables indexed by `Fin n` and free variables indexed by `ξ`. In `LO.FirstOrder.Semiformula`, bound variables are de Bruijn indices with a separate type from free variables.
-/
inductive Semiterm (L : Language) (ξ : Type*) (n : ℕ)
  | bvar : Fin n → Semiterm L ξ n
  | fvar : ξ → Semiterm L ξ n
  | func : ∀ {arity}, L.Func arity → (Fin arity → Semiterm L ξ n) → Semiterm L ξ n

/-- `&x` is the free variable indexed by the element `x : ξ`. -/
scoped prefix:max "&" => Semiterm.fvar

/-- `#x` is the bound variable with de Bruijn index `x`. -/
scoped prefix:max "#" => Semiterm.bvar

abbrev Term (L : Language) (ξ : Type*) := Semiterm L ξ 0

abbrev ClosedSemiterm (L : Language) (n : ℕ) := Semiterm L Empty n

abbrev SyntacticSemiterm (L : Language) (n : ℕ) := Semiterm L ℕ n

abbrev SyntacticTerm (L : Language) := SyntacticSemiterm L 0

namespace Semiterm

variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}

instance [Inhabited ξ] : Inhabited (Semiterm L ξ n) := ⟨&default⟩

section ToString

variable [∀ k, ToString (L.Func k)] [ToString ξ]

end ToString

section Decidable

variable [∀ k, DecidableEq (L.Func k)] [DecidableEq ξ]

def hasDecEq : (t u : Semiterm L ξ n) → Decidable (Eq t u)
  |                   #x,                   #y => by simpa using decEq x y
  |                   #_,                   &_ => isFalse (by simp)
  |                   #_,             func _ _ => isFalse (by simp)
  |                   &_,                   #_ => isFalse (by simp)
  |                   &x,                   &y => by simpa using decEq x y
  |                   &_,             func _ _ => isFalse (by simp)
  |             func _ _,                   #_ => isFalse (by simp)
  |             func _ _,                   &_ => isFalse (by simp)
  | @func L ξ _ k₁ r₁ v₁, @func L ξ _ k₂ r₂ v₂ => by
      by_cases e : k₁ = k₂
      · rcases e with rfl
        exact match decEq r₁ r₂ with
        |  isTrue h => by simpa [h] using Matrix.decVec _ _ fun i ↦ hasDecEq (v₁ i) (v₂ i)
        | isFalse h => isFalse (by simp [h])
      · exact isFalse (by simp [e])

instance : DecidableEq (Semiterm L ξ n) := hasDecEq

end Decidable

/--
The complexity of a semiterm, taking suprema at function symbols.
-/
def complexity : Semiterm L ξ n → ℕ
  |       #_ => 0
  |       &_ => 0
  | func _ v => Finset.sup Finset.univ (fun i ↦ complexity (v i)) + 1

namespace Positive

end Positive

section freeVariables

variable [DecidableEq ξ]

/--
The set of free variables occuring in a semiterm.
-/
def freeVariables : Semiterm L ξ n → Finset ξ
  |       #_ => ∅
  |       &x => {x}
  | func _ v => .biUnion .univ fun i ↦ freeVariables (v i)

@[simp] lemma freeVariables_bvar : (#x : Semiterm L ξ n).freeVariables = ∅ := rfl

@[simp] lemma freeVariables_fvar : (&x : Semiterm L ξ n).freeVariables = {x} := rfl

lemma freeVariables_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    (func f v).freeVariables = .biUnion .univ fun i ↦ (v i).freeVariables := rfl

abbrev FVar? (t : Semiterm L ξ n) (x : ξ) : Prop := x ∈ t.freeVariables

@[simp] lemma fvar?_bvar (x z) : ¬(#x : Semiterm L ξ n).FVar? z := by simp [FVar?]

@[simp] lemma fvar?_fvar (x z) : (&x : Semiterm L ξ n).FVar? z ↔ x = z := by simp [FVar?, Eq.comm]

@[simp] lemma fvar?_func (x) {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    (func f v).FVar? x ↔ ∃ i, (v i).FVar? x := by simp [FVar?, freeVariables_func]

end freeVariables

section lMap

variable (Φ : L₁ →ᵥ L₂)

/--
The map on terms induced from a homomorphism between languages.
-/
def lMap (Φ : L₁ →ᵥ L₂) : Semiterm L₁ ξ n → Semiterm L₂ ξ n
  |       #x => #x
  |       &x => &x
  | func f v => func (Φ.func f) fun i ↦ lMap Φ (v i)

@[simp] lemma lMap_bvar (x : Fin n) : (#x : Semiterm L₁ ξ n).lMap Φ = #x := rfl

@[simp] lemma lMap_fvar (x : ξ) : (&x : Semiterm L₁ ξ n).lMap Φ = &x := rfl

@[simp] lemma lMap_func {k} (f : L₁.Func k) (v : Fin k → Semiterm L₁ ξ n) :
    (func f v).lMap Φ = func (Φ.func f) (lMap Φ ∘ v) := rfl

lemma lMap_func' {k} (f : L₁.Func k) (v : Fin k → Semiterm L₁ ξ n) :
    (func f v).lMap Φ = func (Φ.func f) fun i ↦ lMap Φ (v i) := rfl

end lMap

section

end

section idxOfFVar

end idxOfFVar

end Semiterm

end FirstOrder

end LO
end
