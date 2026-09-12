/- GID: D5/S3/ConceptDynamics/ZfcSyntax/FormulaOne
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcSyntax/FormulaOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Cast.Order.Basic]
   utility: none
   digest: FirstOrder.Basic.Syntax.Formula for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcPredicate.Term
public import D5.S3.ConceptDynamics.ZfcPredicate.Quantifier
public import Mathlib.Data.Nat.Cast.Order.Basic

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/FirstOrder/Basic/Syntax/Formula.lean, original lines 1-320.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Selection excludes the optional LO.FirstOrder.Semiformula.neg_allClosure command.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

namespace LO.FirstOrder

/--
A semiformula of language `L`. Free variables are of type `ξ`, and bound variables are implemented as de Bruijn indices, of a type `Fin n` separate from free variables.
-/
inductive Semiformula (L : Language) (ξ : Type*) : ℕ → Type _ where
  |  verum : Semiformula L ξ n
  | falsum : Semiformula L ξ n
  |    rel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  |   nrel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  |    and : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  |     or : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  |    all : Semiformula L ξ (n + 1) → Semiformula L ξ n
  |    exs : Semiformula L ξ (n + 1) → Semiformula L ξ n

abbrev Formula (L : Language) (ξ : Type*) := Semiformula L ξ 0

abbrev Sentence (L : Language) := Formula L Empty

abbrev Semisentence (L : Language) (n : ℕ) := Semiformula L Empty n

abbrev Semiproposition (L : Language) (n : ℕ) := Semiformula L ℕ n

abbrev Proposition (L : Language) := Semiproposition L 0

namespace Semiformula

variable
  {L : Language} {L₁ : Language} {L₂ : Language} {L₃ : Language}
  {ξ ξ₁ ξ₂ ξ₃ : Type*}
  {n n₁ n₂ n₂ m m₁ m₂ m₃ : ℕ}

def neg {n} : Semiformula L ξ n → Semiformula L ξ n
  |    verum => falsum
  |   falsum => verum
  |  rel r v => nrel r v
  | nrel r v => rel r v
  |  and φ ψ => or (neg φ) (neg ψ)
  |   or φ ψ => and (neg φ) (neg ψ)
  |    all φ => exs (neg φ)
  |    exs φ => all (neg φ)

lemma neg_neg (φ : Semiformula L ξ n) : neg (neg φ) = φ :=
  by induction φ <;> simp [*, neg]

instance : LogicalConnective (Semiformula L ξ n) where
  arrow := fun φ ψ => or (neg φ) ψ
  wedge := and
  vee := or
  tilde := neg

instance : LogicalNeutral (Semiformula L ξ n) where
  top := verum
  bot := falsum

instance : TildeInvolutive (Semiformula L ξ n) where
  tilde_involutive := neg_neg

instance : LogicalConnective.DeMorgan (Semiformula L ξ n) where
  imply := fun _ _ => rfl
  and := fun _ _ => rfl
  or := fun _ _ => rfl

instance : LogicalNeutral.DeMorgan (Semiformula L ξ n) where
  verum := rfl
  falsum := rfl

instance : Quantifier (Semiformula L ξ) where
  all := all
  exs := exs

section ToString

variable [∀ k, ToString (L.Func k)] [∀ k, ToString (L.Rel k)] [ToString ξ]

end ToString

@[simp] lemma neg_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ∼(rel r v) = nrel r v := rfl

@[simp] lemma neg_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ∼(nrel r v) = rel r v := rfl

@[simp] lemma neg_all (φ : Semiformula L ξ (n + 1)) : ∼(∀¹ φ) = ∃¹ ∼φ := rfl

@[simp] lemma neg_ex (φ : Semiformula L ξ (n + 1)) : ∼(∃¹ φ) = ∀¹ ∼φ := rfl

lemma neg_eq (φ : Semiformula L ξ n) : ∼φ = neg φ := rfl

lemma imp_eq (φ ψ : Semiformula L ξ n) : φ 🡒 ψ = ∼φ ⋎ ψ := rfl

@[simp] lemma neg_ball (φ ψ : Semiformula L ξ (n + 1)) : ∼(∀¹[φ] ψ) = ∃¹[φ] ∼ψ := by
  simp [ball, bexs, imp_eq]

@[simp] lemma neg_bexs (φ ψ : Semiformula L ξ (n + 1)) : ∼(∃¹[φ] ψ) = ∀¹[φ] ∼ψ := by
  simp [ball, bexs, imp_eq]

@[simp] lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformula L ξ n) : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := Iff.of_eq <| and.injEq _ _ _ _

@[simp] lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformula L ξ n) : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := Iff.of_eq <| or.injEq _ _ _ _

@[simp] lemma all_inj (φ ψ : Semiformula L ξ (n + 1)) : ∀¹ φ = ∀¹ ψ ↔ φ = ψ := Iff.of_eq <| all.injEq _ _

@[simp] lemma exs_inj (φ ψ : Semiformula L ξ (n + 1)) : ∃¹ φ = ∃¹ ψ ↔ φ = ψ := Iff.of_eq <| exs.injEq _ _

/--
The complexity of a semiformula, taking max at logical connectives.
-/
def complexity {n : ℕ} : Semiformula L ξ n → ℕ
|        ⊤ => 0
|        ⊥ => 0
|  rel _ _ => 0
| nrel _ _ => 0
|    φ ⋏ ψ => max φ.complexity ψ.complexity + 1
|    φ ⋎ ψ => max φ.complexity ψ.complexity + 1
|     ∀¹ φ => φ.complexity + 1
|     ∃¹ φ => φ.complexity + 1

@[simp] lemma complexity_top : complexity (⊤ : Semiformula L ξ n) = 0 := rfl

@[simp] lemma complexity_bot : complexity (⊥ : Semiformula L ξ n) = 0 := rfl

@[simp] lemma complexity_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : complexity (rel r v) = 0 := rfl

@[simp] lemma complexity_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : complexity (nrel r v) = 0 := rfl

@[simp] lemma complexity_and (φ ψ : Semiformula L ξ n) : complexity (φ ⋏ ψ) = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_and' (φ ψ : Semiformula L ξ n) : complexity (and φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_or (φ ψ : Semiformula L ξ n) : complexity (φ ⋎ ψ) = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_or' (φ ψ : Semiformula L ξ n) : complexity (or φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_all (φ : Semiformula L ξ (n + 1)) : complexity (∀¹ φ) = φ.complexity + 1 := rfl
@[simp] lemma complexity_all' (φ : Semiformula L ξ (n + 1)) : complexity (all φ) = φ.complexity + 1 := rfl

@[simp] lemma complexity_exs (φ : Semiformula L ξ (n + 1)) : complexity (∃¹ φ) = φ.complexity + 1 := rfl
@[simp] lemma complexity_exs' (φ : Semiformula L ξ (n + 1)) : complexity (exs φ) = φ.complexity + 1 := rfl

@[elab_as_elim]
def cases' {C : ∀ n, Semiformula L ξ n → Sort w}
    (hverum  : ∀ {n : ℕ}, C n ⊤)
    (hfalsum : ∀ {n : ℕ}, C n ⊥)
    (hrel    : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
    (hnrel   : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (nrel r v))
    (hand    : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n (φ ⋏ ψ))
    (hor     : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n (φ ⋎ ψ))
    (hall    : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C n (∀¹ φ))
    (hexs     : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C n (∃¹ φ)) {n : ℕ} :
    (φ : Semiformula L ξ n) → C n φ
  |    verum => hverum
  |   falsum => hfalsum
  |  rel r v => hrel r v
  | nrel r v => hnrel r v
  |  and φ ψ => hand φ ψ
  |   or φ ψ => hor φ ψ
  |     ∀¹ φ => hall φ
  |     ∃¹ φ => hexs φ

@[elab_as_elim]
def rec' {C : ∀ n, Semiformula L ξ n → Sort w}
    (hverum  : ∀ {n : ℕ}, C n ⊤)
    (hfalsum : ∀ {n : ℕ}, C n ⊥)
    (hrel    : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
    (hnrel   : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (nrel r v))
    (hand    : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n φ → C n ψ → C n (φ ⋏ ψ))
    (hor     : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n φ → C n ψ → C n (φ ⋎ ψ))
    (hall    : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C (n + 1) φ → C n (∀¹ φ))
    (hexs     : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C (n + 1) φ → C n (∃¹ φ)) {n : ℕ} :
    (φ : Semiformula L ξ n) → C n φ
  |    verum => hverum
  |   falsum => hfalsum
  |  rel r v => hrel r v
  | nrel r v => hnrel r v
  |  and φ ψ => hand φ ψ (rec' hverum hfalsum hrel hnrel hand hor hall hexs φ) (rec' hverum hfalsum hrel hnrel hand hor hall hexs ψ)
  |   or φ ψ => hor φ ψ (rec' hverum hfalsum hrel hnrel hand hor hall hexs φ) (rec' hverum hfalsum hrel hnrel hand hor hall hexs ψ)
  |     ∀¹ φ => hall φ (rec' hverum hfalsum hrel hnrel hand hor hall hexs φ)
  |     ∃¹ φ => hexs φ (rec' hverum hfalsum hrel hnrel hand hor hall hexs φ)

section Decidable

variable [L.DecidableEq] [DecidableEq ξ]

def hasDecEq {n : ℕ} : (φ ψ : Semiformula L ξ n) → Decidable (φ = ψ)
  |        ⊤, ψ => by cases ψ using cases' <;>
      { simp only [reduceCtorEq]; infer_instance }
  |        ⊥, ψ => by cases ψ using cases' <;>
      { simp only [reduceCtorEq]; infer_instance }
  |  rel r v, ψ => by
      cases ψ using cases' <;> try { simp only [reduceCtorEq]; infer_instance }
      case hrel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          |  isTrue h => by simpa [h] using Matrix.decVec _ _ fun i ↦ decEq (v i) (v₂ i)
          | isFalse h => isFalse (by simp [h])
        · exact isFalse (by simp [e])
  | nrel r v, ψ => by
      cases ψ using cases' <;> try { simp only [reduceCtorEq]; infer_instance }
      case hnrel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          |  isTrue h => by simpa [h] using Matrix.decVec _ _ fun i ↦ decEq (v i) (v₂ i)
          | isFalse h => isFalse (by simp [h])
        · exact isFalse (by simp [e])
  |    φ ⋏ ψ, r => by
      cases r using cases' <;> try { simp only [reduceCtorEq]; infer_instance }
      case hand φ' ψ' =>
        exact match hasDecEq φ φ' with
        |  isTrue hp =>
          match hasDecEq ψ ψ' with
          |  isTrue hq => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp [hp, hq])
        | isFalse hp => isFalse (by simp [hp])
  |    φ ⋎ ψ, r => by
      cases r using cases' <;> try { simp only [reduceCtorEq]; infer_instance }
      case hor φ' ψ' =>
        exact match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          |  isTrue hq => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp [hp, hq])
        | isFalse hp => isFalse (by simp [hp])
  |     ∀¹ φ, ψ => by
      cases ψ using cases' <;> try { simp only [reduceCtorEq]; infer_instance }
      case hall φ' => simpa using hasDecEq φ φ'
  |     ∃¹ φ, ψ => by
      cases ψ using cases' <;> try { simp only [reduceCtorEq]; infer_instance }
      case hexs φ' => simpa using hasDecEq φ φ'

instance : DecidableEq (Semiformula L ξ n) := hasDecEq

end Decidable

section qr

end qr
end Semiformula
end FirstOrder
end LO
end
