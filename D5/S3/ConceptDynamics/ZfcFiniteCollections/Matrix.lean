/- GID: D5/S3/ConceptDynamics/ZfcFiniteCollections/Matrix
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcFiniteCollections/Matrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fin.VecNotation]
   utility: none
   digest: Vorspiel.Matrix for first-order set definition elimination. -/
module

public import Mathlib.Data.Fin.VecNotation
public import D5.S3.ConceptDynamics.ZfcFiniteData.Nat
public import D5.S3.ConceptDynamics.ZfcFiniteData.Fin

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Vorspiel/Matrix.lean, original lines 1-341.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

namespace Matrix

open _root_.Fin

section
variable {n : ℕ} {α : Type u}

infixr:70 " :> " => vecCons

def vecConsLast {n : ℕ} (t : Fin n → α) (h : α) : Fin n.succ → α :=
  Fin.lastCases h t

@[simp] lemma cons_app_two {n : ℕ} (a : α) (s : Fin n.succ.succ → α) : (a :> s) 2 = s 1 := rfl

@[simp] lemma cons_app_three {n : ℕ} (a : α) (s : Fin n.succ.succ.succ → α) : (a :> s) 3 = s 2 := rfl

@[simp] lemma cons_app_four {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ → α) : (a :> s) 4 = s 3 := rfl

section delab
open Lean PrettyPrinter Delaborator SubExpr

end delab

infixl:70 " <: " => vecConsLast

@[simp] lemma rightConcat_last :
    (s <: a) (Fin.last n) = a := by simp [vecConsLast]

@[simp] lemma rightConcat_castSucc (i : Fin n) :
    (s <: a) (Fin.castSucc i) = s i := by simp [vecConsLast]

@[simp] lemma zero_cons_succ_eq_self (f : Fin (n + 1) → α) : (f 0 :> (f ·.succ) : Fin (n + 1) → α) = f := by
    funext x; cases x using Fin.cases <;> simp

lemma eq_vecCons (s : Fin (n + 1) → C) : s 0 :> s ∘ Fin.succ = s :=
   funext $ Fin.cases (by simp) (by simp)

@[simp] lemma vecCons_ext (a₁ a₂ : α) (s₁ s₂ : Fin n → α) :
    a₁ :> s₁ = a₂ :> s₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
  ⟨by intros h
      constructor
      · exact congrFun h 0
      · exact funext (fun i => by simpa using congrFun h (Fin.castSucc i + 1)),
   by intros h; simp [h]⟩

def decVec {α : Type _} : {n : ℕ} → (v w : Fin n → α) → (∀ i, Decidable (v i = w i)) → Decidable (v = w)
  | 0,     _, _, _ => by simpa [Matrix.empty_eq] using isTrue trivial
  | n + 1, v, w, d => by
      rw [←eq_vecCons v, ←eq_vecCons w, vecCons_ext]
      haveI : Decidable (v ∘ Fin.succ = w ∘ Fin.succ) := decVec _ _ (by intros i; simpa using d _)
      refine instDecidableAnd

lemma comp_vecCons (f : α → β) (a : α) (s : Fin n → α) :
    (fun x ↦ f <| (a :> s) x) = f a :> f ∘ s :=
  funext (fun i => Fin.cases (by simp) (by simp) i)

lemma comp_vecCons' (f : α → β) (a : α) (s : Fin n → α) :
    (fun x ↦ f <| (a :> s) x) = f a :> fun i ↦ f (s i) :=
  comp_vecCons f a s

lemma comp_vecCons'' (f : α → β) (a : α) (s : Fin n → α) : f ∘ (a :> s) = f a :> f ∘ s :=
  comp_vecCons f a s

@[simp] lemma comp₀ : f ∘ (![] : Fin 0 → α) = ![] := by simp [Matrix.empty_eq]

@[simp] lemma comp₁ (a : α) : f ∘ ![a] = ![f a] := by simp [comp_vecCons'']

@[simp] lemma comp₂ (a₁ a₂ : α) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] := by simp [comp_vecCons'']

@[simp] lemma comp₃ (a₁ a₂ a₃ : α) : f ∘ ![a₁, a₂, a₃] = ![f a₁, f a₂, f a₃] := by simp [comp_vecCons'']

lemma comp_vecConsLast (f : α → β) (a : α) (s : Fin n → α) : (fun x => f $ (s <: a) x) = f ∘ s <: f a :=
funext (fun i => Fin.lastCases (by simp) (by simp) i)

@[simp] lemma vecTail_comp (f : α → β) (v : Fin (n + 1) → α) : vecTail (f ∘ v) = f ∘ (vecTail v) := by
  simp [vecTail, Function.comp_assoc]

lemma vecConsLast_vecEmpty {s : Fin 0 → α} (a : α) : s <: a = ![a] :=
  funext (fun x => by
    have : 0 = Fin.last 0 := by rfl
    cases' x using Fin.cases with i
    · rw [this, rightConcat_last, cons_val_fin_one]
    have := i.isLt; contradiction )

lemma constant_eq_singleton {a : α} : (fun _ ↦ a) = ![a] := by funext x; simp

lemma fun_eq_vec_two (v : Fin 2 → α) : v = ![v 0, v 1] := by
  funext x;
  cases x using Fin.cases <;> simp

lemma injective_vecCons {f : Fin n → α} (h : Function.Injective f) {a} (ha : ∀ i, a ≠ f i) : Function.Injective (a :> f) := by
  have : ∀ i, f i ≠ a := fun i => (ha i).symm
  intro i j; cases i using Fin.cases <;> cases j using Fin.cases
  · simp
  · simp [*]
  · simp [*]
  · simpa using @h _ _

@[simp] lemma vecCons_empty_eq_singleton (v : Fin 0 → α) (x : α) : x :> v = ![x] := by
  ext i
  rcases Fin.fin_one_eq_zero i
  simp

@[simp] lemma vecConsLast_empty_eq_singleton (v : Fin 0 → α) (x : α) : v <: x = ![x] := by
  ext i
  rcases Fin.fin_one_eq_zero i
  simp [vecConsLast]
  rfl

end

variable {α : Type _}

def toList : {n : ℕ} → (Fin n → α) → List α
  | 0,     _ => []
  | _ + 1, v => v 0 :: toList (v ∘ Fin.succ)

variable {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u}

def getM : {n : ℕ} → {β : Fin n → Type u} → ((i : Fin n) → m (β i)) → m ((i : Fin n) → β i)
  | 0,     _, _ => pure finZeroElim
  | _ + 1, _, f => Fin.cases <$> f 0 <*> getM (f ·.succ)

lemma getM_pure [LawfulMonad m] {n} {β : Fin n → Type u} (v : (i : Fin n) → β i) :
    getM (fun i => (pure (v i) : m (β i))) = pure v := by
  induction' n with n ih
  · unfold getM; congr; funext x; exact x.elim0
  · simp only [getM, map_pure, ih, seq_pure]
    exact congr_arg _ (funext <| Fin.cases rfl fun i ↦ rfl)

@[simp] lemma getM_some {n} {β : Fin n → Type u} (v : (i : Fin n) → β i) :
    getM (fun i => (some (v i) : Option (β i))) = some v := getM_pure v

def appendr {n m} (v : Fin n → α) (w : Fin m → α) : Fin (m + n) → α := Matrix.vecAppend (add_comm m n) v w

@[simp] lemma appendr_nil {m} (w : Fin m → α) : appendr ![] w = w := by funext i; simp [appendr]

@[simp] lemma appendr_cons {m n} (x : α) (v : Fin n → α) (w : Fin m → α) : appendr (x :> v) w = x :> appendr v w := by funext i; simp [appendr]

-- Renamed from `Matrix.forall_iff` to `Matrix.vecForall_iff` to avoid clashing with
-- Mathlib's `Matrix.forall_iff` (Mathlib.Data.Matrix.Reflection), which otherwise makes
-- Foundation unimportable alongside that module.
lemma vecForall_iff {n : ℕ} (φ : (Fin (n + 1) → α) → Prop) :
    (∀ v, φ v) ↔ (∀ a, ∀ v, φ (a :> v)) :=
  ⟨fun h a v ↦ h (a :> v), fun h v ↦ by simpa [eq_vecCons v] using h (v 0) (v ∘ Fin.succ)⟩

-- Renamed from `Matrix.exists_iff` to `Matrix.vecExists_iff`; see `vecForall_iff` above.

def foldr (f : α → β → β) (init : β) : {k : ℕ} → (Fin k → α) → β
  |     0, _ => init
  | _ + 1, v => f (vecHead v) (Matrix.foldr f init (vecTail v))

-- Renamed from `Matrix.map` to `Matrix.vecMap` to avoid clashing with Mathlib's
-- `Matrix.map`: both auto-generate `Matrix.map.eq_1`, which makes Foundation
-- unimportable alongside Mathlib matrix/analysis theory (e.g. Bochner integration).

section vecMap

variable (f : α → β)

end vecMap
section foldr

variable (f : α → β → β) (init : β)

@[simp] lemma foldr_zero (v : Fin 0 → α) : foldr f init v = init := rfl

@[simp] lemma foldr_succ (v : Fin (k + 1) → α) : foldr f init v = f (vecHead v) (foldr f init (vecTail v)) := rfl

end foldr

section foldl

variable (f : α → β → α) (init : α)

end foldl

section vecToNat

def vecToNat (v : Fin n → ℕ) : ℕ := foldr (fun x ih ↦ Nat.pair x ih + 1) 0 v

end vecToNat

section

variable {m : ℕ}

@[simp] lemma appeendr_addCast (u : Fin m → α) (v : Fin n → α) (i : Fin m) :
    appendr u v (i.addCast n) = u i := by simp [appendr, vecAppend_eq_ite]

@[simp] lemma appeendr_addNat (u : Fin m → α) (v : Fin n → α) (i : Fin n) :
    appendr u v (i.addNat m) = v i := by simp [appendr, vecAppend_eq_ite]

end

end Matrix

end
