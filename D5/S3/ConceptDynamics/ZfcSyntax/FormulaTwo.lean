/- GID: D5/S3/ConceptDynamics/ZfcSyntax/FormulaTwo
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcSyntax/FormulaTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Cast.Order.Basic]
   utility: none
   digest: FirstOrder.Basic.Syntax.Formula for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcPredicate.Term
public import D5.S3.ConceptDynamics.ZfcPredicate.Quantifier
public import Mathlib.Data.Nat.Cast.Order.Basic
public import D5.S3.ConceptDynamics.ZfcSyntax.FormulaOne

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/FirstOrder/Basic/Syntax/Formula.lean, original lines 321-587.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section
namespace LO
namespace FirstOrder
namespace Semiformula
variable
  {L : Language} {L₁ : Language} {L₂ : Language} {L₃ : Language}
  {ξ ξ₁ ξ₂ ξ₃ : Type*}
  {n n₁ n₂ n₂ m m₁ m₂ m₃ : ℕ}
section qr

end qr

section Open

end Open

section FreeVariables

variable [DecidableEq ξ]

def freeVariables {n} : Semiformula L ξ n → Finset ξ
  |  rel _ v => .biUnion .univ fun i ↦ (v i).freeVariables
  | nrel _ v => .biUnion .univ fun i ↦ (v i).freeVariables
  |        ⊤ => ∅
  |        ⊥ => ∅
  |    φ ⋏ ψ => freeVariables φ ∪ freeVariables ψ
  |    φ ⋎ ψ => freeVariables φ ∪ freeVariables ψ
  |     ∀¹ φ => freeVariables φ
  |     ∃¹ φ => freeVariables φ

lemma freeVariables_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v).freeVariables = .biUnion .univ fun i ↦ (v i).freeVariables := rfl

lemma freeVariables_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v).freeVariables = .biUnion .univ fun i ↦ (v i).freeVariables := rfl

@[simp] lemma freeVariables_verum : (⊤ : Semiformula L ξ n).freeVariables = ∅ := rfl

@[simp] lemma freeVariables_falsum : (⊥ : Semiformula L ξ n).freeVariables = ∅ := rfl

@[simp] lemma freeVariables_and (φ ψ : Semiformula L ξ n) : (φ ⋏ ψ).freeVariables = φ.freeVariables ∪ ψ.freeVariables := rfl

@[simp] lemma freeVariables_or (φ ψ : Semiformula L ξ n) : (φ ⋎ ψ).freeVariables = φ.freeVariables ∪ ψ.freeVariables := rfl

@[simp] lemma freeVariables_all (φ : Semiformula L ξ (n + 1)) : (∀¹ φ).freeVariables = φ.freeVariables := rfl

@[simp] lemma freeVariables_exs (φ : Semiformula L ξ (n + 1)) : (∃¹ φ).freeVariables = φ.freeVariables := rfl

@[simp] lemma freeVariables_allClosure (φ : Semiformula L ξ n) : (∀¹* φ).freeVariables = φ.freeVariables := by
  induction n <;> simp [allClosure, *]

abbrev FVar? (φ : Semiformula L ξ n) (x : ξ) : Prop := x ∈ φ.freeVariables

@[simp] lemma fvar?_rel {x k} {R : L.Rel k} {v : Fin k → Semiterm L ξ n} :
    (rel R v).FVar? x ↔ ∃ i, (v i).FVar? x := by simp [FVar?, freeVariables_rel]

@[simp] lemma fvar?_nrel {x k} {R : L.Rel k} {v : Fin k → Semiterm L ξ n} :
    (nrel R v).FVar? x ↔ ∃ i, (v i).FVar? x := by simp [FVar?, freeVariables_nrel]

@[simp] lemma fvar?_and (x) (φ ψ : Semiformula L ξ n) : (φ ⋏ ψ).FVar? x ↔ φ.FVar? x ∨ ψ.FVar? x := by simp [FVar?]

@[simp] lemma fvar?_or (x) (φ ψ : Semiformula L ξ n) : (φ ⋎ ψ).FVar? x ↔ φ.FVar? x ∨ ψ.FVar? x := by simp [FVar?]

@[simp] lemma fvar?_all (x) (φ : Semiformula L ξ (n + 1)) : (∀¹ φ).FVar? x ↔ φ.FVar? x := by simp [FVar?]

def fvSup (φ : Semiproposition L n) : ℕ := (φ.freeVariables.max).recBotCoe 0 .succ

lemma lt_fvSup_of_fvar? {φ : Semiproposition L n} : φ.FVar? m → m < φ.fvSup := by
  unfold fvSup FVar?
  intro hm
  have : ∃ s : ℕ, φ.freeVariables.max = s := Finset.max_of_mem hm
  rcases this with ⟨s, hs⟩
  have : m ≤ s := by
    have : (m : WithBot ℕ) ≤ ↑s := by simpa [hs, -Nat.cast_le] using Finset.le_max hm
    exact WithBot.coe_le_coe.mp this
  simpa [hs, WithBot.recBotCoe] using Nat.lt_add_one_of_le this

lemma not_fvar?_of_lt_fvSup (φ : Semiproposition L n) (h : φ.fvSup ≤ m) : ¬φ.FVar? m :=
  fun hm ↦ (lt_self_iff_false _).mp (lt_of_le_of_lt h <| lt_fvSup_of_fvar? hm)

end FreeVariables

section

variable {α : Type*} [LinearOrder α]

end

variable {L : Language} {L₁ : Language} {L₂ : Language} {L₃ : Language} {ξ : Type*} {Φ : L₁ →ᵥ L₂}

def lMapAux (Φ : L₁ →ᵥ L₂) {n} : Semiformula L₁ ξ n → Semiformula L₂ ξ n
  |        ⊤ => ⊤
  |        ⊥ => ⊥
  |  rel r v => rel (Φ.rel r) (Semiterm.lMap Φ ∘ v)
  | nrel r v => nrel (Φ.rel r) (Semiterm.lMap Φ ∘ v)
  |    φ ⋏ ψ => lMapAux Φ φ ⋏ lMapAux Φ ψ
  |    φ ⋎ ψ => lMapAux Φ φ ⋎ lMapAux Φ ψ
  |     ∀¹ φ => ∀¹ lMapAux Φ φ
  |     ∃¹ φ => ∃¹ lMapAux Φ φ

lemma lMapAux_neg {n} (φ : Semiformula L₁ ξ n) :
    (∼φ).lMapAux Φ = ∼φ.lMapAux Φ := by
  induction φ using Semiformula.rec' <;> simp [*, lMapAux]

/--
The map on semiformulas induced by a homomorphism between languages.
-/
def lMap (Φ : L₁ →ᵥ L₂) {n} : Semiformula L₁ ξ n →ˡᶜ Semiformula L₂ ξ n where
  toTr := lMapAux Φ
  map_top' := by simp [lMapAux]
  map_bot' := by simp [lMapAux]
  map_and' := by simp [lMapAux]
  map_or'  := by simp [lMapAux]
  map_neg' := by simp [lMapAux_neg]
  map_imply' := by simp [Semiformula.imp_eq, lMapAux_neg, ←Semiformula.neg_eq, lMapAux]

@[simp] lemma lMap_rel {k} (r : L₁.Rel k) (v : Fin k → Semiterm L₁ ξ n) :
    lMap Φ (rel r v) = rel (Φ.rel r) (Semiterm.lMap Φ ∘ v) := rfl

@[simp] lemma lMap_nrel {k} (r : L₁.Rel k) (v : Fin k → Semiterm L₁ ξ n) :
    lMap Φ (nrel r v) = nrel (Φ.rel r) (Semiterm.lMap Φ ∘ v) := rfl

@[simp] lemma lMap_all (φ : Semiformula L₁ ξ (n + 1)) :
    lMap Φ (∀¹ φ) = ∀¹ lMap Φ φ := rfl

@[simp] lemma lMap_exs (φ : Semiformula L₁ ξ (n + 1)) :
    lMap Φ (∃¹ φ) = ∃¹ lMap Φ φ := rfl

section enumerateFVar

end enumerateFVar

end Semiformula

abbrev Theory (L : Language) := Set (Sentence L)

namespace Theory

def lMap (Φ : L₁ →ᵥ L₂) (T : Theory L₁) : Theory L₂ := Semiformula.lMap Φ '' T

end Theory

end LO.FirstOrder

end
