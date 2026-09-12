/- GID: D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcTermRewriting/RewThree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Syntax.Predicate.Rew for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcPredicate.Quantifier
public import D5.S3.ConceptDynamics.ZfcPredicate.Term
public import D5.S3.ConceptDynamics.ZfcSupport.Function
public import D5.S3.ConceptDynamics.ZfcTermRewriting.RewTwo

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Syntax/Predicate/Rew.lean, original lines 638-953.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section
namespace LO
namespace FirstOrder
namespace Rew
open Semiterm
variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}
variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)
section Syntactic

@[simp] lemma fixitr_bvar (n m) (x : Fin n) : fixitr n m (#x : SyntacticSemiterm L n) = #(x.castAdd m) := by
  induction m
  · simp [*]
  case succ m ih =>
    rw [fixitr_succ, comp_app, ih]; simp [Fin.castSucc_castAdd]

lemma fixitr_fvar (n m) (x : ℕ) :
    fixitr n m (&x : SyntacticSemiterm L n) = if h : x < m then #(Fin.natAdd n ⟨x, h⟩) else &(x - m) := by
  induction m
  · simp [*]
  case succ m ih =>
    suffices fix (fixitr n m &x) = if h : x < m + 1 then #⟨n + x, _⟩ else &(x - (m + 1)) from Eq.trans (comp_app _ _ _) this
    simp only [ih, Fin.natAdd_mk]
    by_cases hx : x < m
    · simp [hx, Nat.lt_add_right 1 hx]
    by_cases hx2 : x < m + 1
    · have : x = m := Nat.le_antisymm (by { simpa [Nat.lt_succ_iff] using hx2 }) (by simpa using hx)
      aesop
    · simp [hx, hx2]
      have : x - m = x - (m + 1) + 1 := by omega
      simp [this]

end Syntactic

end Rew

namespace Semiterm

variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}

lemma rew_eq_of_funEqOn [DecidableEq ξ₁] (ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁)
  (hb : ∀ x, ω₁ #x = ω₂ #x)
  (he : Function.funEqOn t.FVar? (ω₁ ∘ Semiterm.fvar) (ω₂ ∘ Semiterm.fvar)) :
    ω₁ t = ω₂ t := by
  induction t
  case bvar => simp [hb]
  case fvar => simpa [FVar?, Function.funEqOn] using he
  case func k f v ih =>
    simp only [Rew.func, func.injEq, heq_eq_eq, true_and]
    funext i
    exact ih i (he.of_subset <| by intro x hx; simpa using ⟨i, hx⟩)

section lMap

variable (Φ : L₁ →ᵥ L₂)
open Rew

lemma lMap_bind (b : Fin n₁ → Semiterm L₁ ξ₂ n₂) (e : ξ₁ → Semiterm L₁ ξ₂ n₂) (t) :
    lMap Φ (bind b e t) = bind (lMap Φ ∘ b) (lMap Φ ∘ e) (t.lMap Φ) := by
  induction t <;> simp [*, -lMap_func, lMap_func', -Rew.func, Rew.func']

lemma lMap_map (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂) (t) :
    (map b e t).lMap Φ = map b e (t.lMap Φ) := by
  simp [map, lMap_bind, Function.comp_def]

lemma lMap_bShift (t : Semiterm L₁ ξ₁ n) : (bShift t).lMap Φ = bShift (t.lMap Φ) := by
  simp [bShift, lMap_map]

end lMap

lemma fvar?_rew [DecidableEq ξ₁] [DecidableEq ξ₂]
    {ω : Rew L ξ₁ n₁ ξ₂ n₂}
    {t : Semiterm L ξ₁ n₁} {x} :
    (ω t).FVar? x → (∃ i : Fin n₁, (ω #i).FVar? x) ∨ (∃ z : ξ₁, t.FVar? z ∧ (ω &z).FVar? x) := by
  induction t
  case bvar z =>
    intro h; left; exact ⟨z, h⟩
  case fvar z =>
    intro h; right; exact ⟨z, by simp [h]⟩
  case func k F v ih =>
    simp only [Rew.func, fvar?_func, forall_exists_index]
    intro i hx
    rcases ih i hx with (h | ⟨z, hi, hz⟩)
    · left; exact h
    · right; exact ⟨z, ⟨i, hi⟩, hz⟩

@[simp] lemma fvar?_bShift [DecidableEq ξ] {t : Semiterm L ξ n} {x} :
    (Rew.bShift t).FVar? x ↔ t.FVar? x := by
  induction t <;> simp [Rew.func, *]

def toEmpty [DecidableEq ξ] {n : ℕ} : (t : Semiterm L ξ n) → t.freeVariables = ∅ → ClosedSemiterm L n
  |       #x, _ => #x
  |       &x, h => by simp at h
  | func f v, h =>
    have : ∀ i, (v i).freeVariables = ∅ := by
      intro i; ext x
      have := by simpa using Eq.to_iff (congrFun (congrArg Membership.mem h) x)
      simpa using this i
    func f fun i ↦ toEmpty (v i) (this i)

@[simp] lemma emb_toEmpty [DecidableEq ξ] (t : Semiterm L ξ n) (ht : t.freeVariables = ∅) : Rew.emb (t.toEmpty ht) = t := by
  induction t <;> try simp [toEmpty, Rew.func, *, Function.comp_def]
  case fvar => simp at ht

end Semiterm

/--
A typeclass for `Rew`s which additionally respect quantifiers.

`app` - A notion of application of `Rew`s to formulas.

`app_all` - Application preserves universal quantification.

`app_exs` - Application preserves existential quantification.
-/
class Rewriting (L : outParam Language) (ξ : outParam Type*) (F : ℕ → Type*) (ζ : Type*) (G : outParam (ℕ → Type*))
    [LCWQ F] [LCWQ G] where
  app {n₁ n₂} : Rew L ξ n₁ ζ n₂ → F n₁ →ˡᶜ G n₂
  app_all (ω₁₂ : Rew L ξ n₁ ζ n₂) (φ) : app ω₁₂ (∀¹ φ) = ∀¹ (app ω₁₂.q φ)
  app_exs (ω₁₂ : Rew L ξ n₁ ζ n₂) (φ) : app ω₁₂ (∃¹ φ) = ∃¹ (app ω₁₂.q φ)

abbrev SyntacticRewriting (L : outParam Language) (F : ℕ → Type*) (G : outParam (ℕ → Type*)) [LCWQ F] [LCWQ G] :=
  Rewriting L ℕ F ℕ G

namespace Rewriting

variable [LCWQ F] [LCWQ G] [Rewriting L ξ F ζ G]

attribute [simp] app_all app_exs

/-- Application of a `Rewriting` to a formula. -/
infixr:73 " ▹ " => app

lemma smul_ext' {ω₁ ω₂ : Rew L ξ n₁ ζ n₂} (h : ω₁ = ω₂) {φ : F n₁} : ω₁ ▹ φ = ω₂ ▹ φ := by rw [h]

abbrev subst [Rewriting L ξ F ξ F] (φ : F n₁) (w : Fin n₁ → Semiterm L ξ n₂) : F n₂ := Rew.subst w ▹ φ

/-- Applies the substitution `LO.FirstOrder.Rew.subst w` to a formula. This substitutes the bound variables occurring in the formula by `w : Fin n₁ → Semiterm L ξ n₂`. -/
infix:90 " ⇜ " => LO.FirstOrder.Rewriting.subst

/-- Applies the substitution `LO.FirstOrder.Rew.shift` to a formula. This substitutes each free variable `&x` with `&(x + 1)`. -/
abbrev shift [Rewriting L ℕ F ℕ F] : F n →ˡᶜ F n := app Rew.shift

abbrev free [Rewriting L ℕ F ℕ F] : F (n + 1) →ˡᶜ F n := app Rew.free

def shifts [Rewriting L ℕ F ℕ F] (Γ : List (F n)) : List (F n) := Γ.map Rewriting.shift

/-- Applies the substitution `LO.FirstOrder.Rew.shift` to each formula in a list of formulas. This substitutes each free variable `&x` with `&(x + 1)`. -/
scoped[LO.FirstOrder] postfix:max "⁺" => FirstOrder.Rewriting.shifts

@[simp] lemma shifts_nil [Rewriting L ℕ F ℕ F] : ([] : List (F n))⁺ = [] := by rfl

@[simp] lemma shifts_cons [Rewriting L ℕ F ℕ F] (φ : F n) (Γ : List (F n)) : (φ :: Γ)⁺ = shift φ :: Γ⁺ := by simp [shifts]

@[simp] lemma shifts_neg [Rewriting L ℕ F ℕ F] (Γ : List (F n)) : (∼Γ)⁺ = ∼(Γ⁺) := by
  simp [shifts, List.tilde_def]

abbrev emb {ο ξ} [IsEmpty ο] {O F : ℕ → Type*} [LCWQ O] [LCWQ F] [Rewriting L ο O ξ F] : O n →ˡᶜ F n := app (Rew.emb (ξ := ξ))

end Rewriting

section Notation

open Lean PrettyPrinter Delaborator

syntax (name := substNotation) term:max "/[" term,* "]" : term

/-- Slash notation for rewriting bound variables of a formula.

The notation `φ/w` is equivalent to `φ ⇜ w`, which for a formula `φ` with bound variables from `Fin n₁`, substitutes the bound variables occurring in `φ` by `w : Fin n₁ → Semiterm L ξ n₂`. -/
macro_rules (kind := substNotation)
  | `($φ:term /[$terms:term,*]) => `($φ ⇜ ![$terms,*])

end Notation

class ReflectiveRewriting (L : outParam Language) (ξ : outParam Type*) (F : ℕ → Type*)
    [LCWQ F] [Rewriting L ξ F ξ F] where
  id_app (φ : F n) : @Rew.id L ξ n ▹ φ = φ

class TransitiveRewriting (L : outParam Language)
    (ξ₁ : outParam Type*) (F₁ : ℕ → Type*) (ξ₂ : Type*) (F₂ : outParam (ℕ → Type*)) (ξ₃ : Type*) (F₃ : outParam (ℕ → Type*))
    [LCWQ F₁] [LCWQ F₂] [LCWQ F₃]
    [Rewriting L ξ₁ F₁ ξ₂ F₂] [Rewriting L ξ₂ F₂ ξ₃ F₃] [Rewriting L ξ₁ F₁ ξ₃ F₃] where
  comp_app (ω₁₂ : Rew L ξ₁ n₁ ξ₂ n₂) (ω₂₃ : Rew L ξ₂ n₂ ξ₃ n₃) (φ : F₁ n₁) : (ω₂₃.comp ω₁₂) ▹ φ = ω₂₃ ▹ ω₁₂ ▹ φ

class InjMapRewriting (L : outParam Language) (ξ : outParam Type*) (F : ℕ → Type*) (ζ : Type*) (G : outParam (ℕ → Type*))
    [LCWQ F] [LCWQ G] [Rewriting L ξ F ζ G] where
  smul_map_injective {b : Fin n₁ → Fin n₂} {f : ξ → ζ} :
    (hb : Function.Injective b) → (hf : Function.Injective f) → Function.Injective fun φ : F n₁ ↦ Rew.map (L := L) b f ▹ φ

class LawfulSyntacticRewriting (L : outParam Language) (S : ℕ → Type*) [LCWQ S] [SyntacticRewriting L S S] extends
  ReflectiveRewriting L ℕ S, TransitiveRewriting L ℕ S ℕ S ℕ S, InjMapRewriting L ℕ S ℕ S

attribute [simp] ReflectiveRewriting.id_app

namespace LawfulSyntacticRewriting

variable {S : ℕ → Type*} [LCWQ S] [SyntacticRewriting L S S]

open Rewriting ReflectiveRewriting TransitiveRewriting InjMapRewriting Semiterm

lemma shift_conj₂ (Γ : List (S n)) : shift (⋀Γ) = ⋀Γ⁺ := by
  induction Γ using List.induction_with_singleton
  case hnil => simp
  case hsingle => simp
  case hcons φ Γ hΓ ih =>
    have : Γ⁺ ≠ [] := by intro H; have : Γ = [] := List.map_eq_nil_iff.mp H; contradiction
    simp [hΓ, this, ih]

variable [LawfulSyntacticRewriting L S]

/-- `hom_subst_mbar_zero_comp_shift_eq_free` -/
@[simp] lemma app_subst_fbar_zero_comp_shift_eq_free (φ : S 1) :
    (shift φ)/[&0] = free φ := by simp [← comp_app, Rew.subst_mbar_zero_comp_shift_eq_free]

end LawfulSyntacticRewriting
end FirstOrder
end LO
end
