/- GID: D5/S3/ConceptDynamics/ZfcLogic/LogicSymbolTwo
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcLogic/LogicSymbolTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logic.LogicSymbol for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcFiniteCollections.List
public import D5.S3.ConceptDynamics.ZfcLanguageSupport.NotationClass
public import D5.S3.ConceptDynamics.ZfcLogic.LogicSymbolOne

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Logic/LogicSymbol.lean, original lines 320-638.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

open LO

namespace Matrix

variable {α : Type*}

section conjunction

variable [Top α] [Wedge α]

/-- The conjunction of a vector of elements of type `α`, where `α` is a type with `Wedge α`. -/
def conj : {n : ℕ} → (Fin n → α) → α
  |     0, _ => ⊤
  | _ + 1, v => v 0 ⋏ conj (vecTail v)

end conjunction

section disjunction

variable [Bot α] [Vee α]

end disjunction

variable
  [LogicalConnective α] [LogicalConnective β]
  [LogicalNeutral α] [LogicalNeutral β]

/--
Homomorphisms commute with `k`-ary conjunctions (vector version).
-/
@[simp] lemma conj_hom_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop]
  (f : F) (v : Fin n → α) : f (conj v) = ∀ i, f (v i) := by
  induction' n with n ih
  · simp [conj]
  · suffices (f (v 0) ∧ ∀ (i : Fin n), f (vecTail v i)) ↔ ∀ (i : Fin (n + 1)), f (v i) by simpa [conj, ih]
    constructor
    · intro ⟨hz, hs⟩ i; cases i using Fin.cases; { exact hz }; { exact hs _ }
    · intro h; exact ⟨h 0, fun i => h _⟩

end Matrix

namespace List

variable {α : Type*}

variable {φ ψ : α}

section tilde

variable [Tilde α]

instance : Tilde (List α) := ⟨fun l ↦ l.map (∼·)⟩

lemma tilde_def (l : List α) : ∼l = l.map (∼·) := rfl

@[simp] lemma tilde_nil : ∼([] : List α) = [] := rfl

@[simp] lemma tilde_cons (a : α) (l : List α) : ∼(a :: l) = ∼a :: ∼l := rfl

@[simp] lemma tilde_append (l k : List α) : ∼(l ++ k) = ∼l ++ ∼k := by
  induction l with
  |          nil => simp [*]
  | cons a as ih => simp [*, List.cons_append]

@[simp] lemma mem_tilde_iff [TildeInvolutive α] {a : α} {l : List α} : a ∈ ∼l ↔ ∼a ∈ l := by
  induction l with
  |          nil => simp [*]
  | cons b bs ih =>
    suffices a = ∼b ↔ ∼a = b by
      simp [ih, this]
    constructor <;> {rintro rfl; simp}

instance [TildeInvolutive α] : TildeInvolutive (List α) where
  tilde_involutive l := by
    induction l with
    |          nil => simp [*]
    | cons a as ih =>
      simp [ih, TildeInvolutive.tilde_involutive a]

end tilde

section conjunction

variable [Top α] [Wedge α]

/-- Remark: `[φ].conj₂ = φ ≠ φ ⋏ ⊤ = [φ].conj`. -/
def conj₂ : List α → α
|           [] => ⊤
|          [φ] => φ
| φ :: ψ :: rs => φ ⋏ (ψ :: rs).conj₂

/--
The conjunction of a list of members of type `α`.
-/
prefix:80 "⋀" => List.conj₂

@[simp] lemma conj₂_nil : ⋀[] = (⊤ : α) := rfl

@[simp] lemma conj₂_singleton : ⋀[φ] = φ := rfl

@[simp] lemma conj₂_cons_nonempty {a : α} {as : List α} (h : as ≠ [] := by assumption) : ⋀(a :: as) = a ⋏ ⋀as := by
  cases as with
  | nil => contradiction;
  | cons ψ rs => simp [List.conj₂]

end conjunction

section disjunction

variable [Bot α] [Vee α]

/-- Remark: `[φ].disj₂ = φ ≠ φ ⋎ ⊥ = [φ].disj`. -/
def disj₂ : List α → α
|           [] => ⊥
|          [φ] => φ
| φ :: ψ :: rs => φ ⋎ (ψ :: rs).disj₂

/--
The disjunction of a list of members of type `α`.
-/
prefix:80 "⋁" => disj₂

@[simp] lemma disj₂_nil : ⋁[] = (⊥ : α) := rfl

@[simp] lemma disj₂_singleton : ⋁[φ] = φ := rfl

@[simp] lemma disj₂_cons_nonempty {a : α} {as : List α} (h : as ≠ [] := by assumption) : ⋁(a :: as) = a ⋎ ⋁as := by
  cases as with
  | nil => contradiction;
  | cons ψ rs => simp [disj₂]

end disjunction

section tilde

variable [LogicalConnective α] [LogicalNeutral α] [LogicalNeutral.DeMorgan α] [LogicalConnective.DeMorgan α]

/--
Variadic de Morgan's law for lists of elements of type `α`.
-/
@[simp] lemma tilde_conj₂ (l : List α) : ∼⋁l = ⋀(∼l) := by
  match l with
  |          [] => simp
  |         [a] => simp
  | a :: b :: l => simp [tilde_conj₂ (b :: l)]

/--
Variadic de Morgan's law for lists of elements of type `α`.
-/
@[simp] lemma tilde_disj₂ (l : List α) : ∼⋀l = ⋁(∼l) := by
  match l with
  |          [] => simp
  |         [a] => simp
  | a :: b :: l => simp [tilde_disj₂ (b :: l)]

end tilde

section

variable
  [LogicalConnective α] [LogicalNeutral α]
  [LogicalConnective β] [LogicalNeutral β]
  [FunLike G α β] [LogicalConnective.HomClass G α β]

end

section

variable [LogicalConnective α] [LogicalNeutral α] [FunLike G α Prop] [LogicalConnective.HomClass G α Prop]

end

end List

namespace Finset

open Classical

variable {α : Type*}

section tilde

end tilde
end Finset
end
