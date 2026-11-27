/- GID: D5/S3/Topology/ConnectedCategoryGraft
   generality: G
   mirror-B: D5/B/S3/Topology/ConnectedCategoryGraft
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Hom.Basic, mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: The ordinary categorical cover number of a connected poset graft. -/

module

public import Mathlib.Basic.Finite.Sum
public import Mathlib.Order.Hom.Basic
public import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Card
import OmegaBuild.Commands

/-!
# Ordinary category of a connected graft

This is the ordinary-category step for the connected realization construction
motivated by Mosquera-Lois and Tanaka, Question 6.2 (https://arxiv.org/abs/2609.39615v1).
-/

compile_only_with_mathlib

@[expose] public section

set_option autoImplicit false

namespace D5.S3.Topology.ConnectedCategoryGraft

variable {X : Type*} [PartialOrder X] {p : X} {m n : ℕ}

/-- Categorical inclusion of a subposet, via a finite fence of monotone maps. -/
def Categorical (U : Set X) : Prop :=
  ∃ c : X, Relation.EqvGen (· ≤ ·) (OrderEmbedding.subtype U).toOrderHom
    (OrderHom.const U c)

/-- A categorical lower cover with `n` indexed pieces, allowing empty pieces. -/
def HasCategoricalCover (X : Type*) [PartialOrder X] (n : ℕ) : Prop :=
  ∃ U : Fin n → Set X, (∀ i, IsLowerSet (U i) ∧ Categorical (U i)) ∧
    ∀ x, ∃ i, x ∈ U i

/-- The old poset, one new bottom, and `m` new tops. -/
inductive Graft {X : Type*} (p : X) (m : ℕ)
  | old (x : X)
  | bottom
  | top (i : Fin m)

namespace Graft

/-- The graft order. The elements below a new top on the old side satisfy `x ≤ p`. -/
def graftLE : Graft p m → Graft p m → Prop
  | .old x, .old y => x ≤ y
  | .old x, .top _ => x ≤ p
  | .bottom, .bottom => True
  | .bottom, .top _ => True
  | .top i, .top j => i = j
  | _, _ => False

instance : PartialOrder (Graft p m) where
  le := graftLE
  le_refl a := by cases a <;> simp [graftLE]
  le_trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;> first
      | exact False.elim hab
      | exact False.elim hbc
      | exact le_trans hab hbc
      | exact Eq.trans hab hbc
      | exact hab
  le_antisymm a b hab hba := by
    cases a <;> cases b <;> first
      | rfl
      | exact False.elim hab
      | exact False.elim hba
      | exact congrArg Graft.old (le_antisymm hab hba)
      | exact congrArg Graft.top hab

instance [Finite X] : Finite (Graft p m) := by
  let encode : Graft p m → X ⊕ (Unit ⊕ Fin m)
    | .old x => .inl x
    | .bottom => .inr (.inl ())
    | .top i => .inr (.inr i)
  apply Finite.of_injective encode
  intro a b h
  cases a <;> cases b <;> simp_all [encode]

private theorem le_iff {a b : Graft p m} : a ≤ b ↔ graftLE a b := Iff.rfl

private def oldHom : X →o Graft p m :=
  ⟨.old, fun _ _ h => h⟩

private def retractOld : Graft p m →o X where
  toFun
    | .old x => x
    | _ => p
  monotone' := by
    intro a b h
    cases a <;> cases b <;> first | exact h | exact le_rfl | exact False.elim h

end Graft

open Graft

private theorem mapFence {A B : Type*} [Preorder A] [Preorder B]
    (f : A → B) (hf : Monotone f) {a b : A} (h : Relation.EqvGen (· ≤ ·) a b) :
    Relation.EqvGen (· ≤ ·) (f a) (f b) := by
  induction h with
  | rel a b hab => exact .rel _ _ (hf hab)
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

private theorem restrictCover (h : HasCategoricalCover (Graft p m) n) :
    HasCategoricalCover X n := by
  obtain ⟨U, hU, cover⟩ := h
  let V (i : Fin n) : Set X := {x | Graft.old x ∈ U i}
  refine ⟨V, ?_, fun x => cover (.old x)⟩
  intro i
  obtain ⟨hLower, c, hc⟩ := hU i
  let e : V i →o U i :=
    ⟨fun x => ⟨.old x.val, x.property⟩, fun _ _ hab => hab⟩
  refine ⟨?_, retractOld c, ?_⟩
  · intro a b hab hb
    exact hLower (show (Graft.old b : Graft p m) ≤ .old a from hab) hb
  · exact mapFence (fun (f : U i →o Graft p m) => retractOld.comp (f.comp e))
      (fun _ _ hfg x => retractOld.monotone (OrderHom.le_def.mp hfg (e x))) hc

private abbrev Square := Graft (0 : Fin 1) 2

private theorem squareUp (f : Square →o Square) (h : OrderHom.id ≤ f) : f = OrderHom.id := by
  have fixTop (i : Fin 2) : f (.top i) = .top i := by
    have hi : (.top i : Square) ≤ f (.top i) := h (.top i)
    cases he : f (.top i) <;> simp_all [Graft.le_iff, Graft.graftLE]
  have below (x : Square) (i : Fin 2) (hx : x ≤ .top i) : f x ≤ .top i :=
    fixTop i ▸ f.monotone hx
  apply OrderHom.ext
  funext x
  change f x = x
  cases x with
  | top i => exact fixTop i
  | old a =>
    have h₀ := below (.old a) 0 (show a ≤ 0 from (Subsingleton.elim a 0).le)
    have h₁ := below (.old a) 1 (show a ≤ 0 from (Subsingleton.elim a 0).le)
    have hx : (.old a : Square) ≤ f (.old a) := h (.old a)
    cases he : f (.old a) with
    | old b => exact congrArg Graft.old (Subsingleton.elim b a)
    | bottom => simp_all [Graft.le_iff, Graft.graftLE]
    | top i => simp_all [Graft.le_iff, Graft.graftLE]
  | bottom =>
    have h₀ := below .bottom 0 trivial
    have h₁ := below .bottom 1 trivial
    have hx : (.bottom : Square) ≤ f .bottom := h .bottom
    cases he : f .bottom <;> simp_all [Graft.le_iff, Graft.graftLE]

private theorem squareDown (f : Square →o Square) (h : f ≤ OrderHom.id) : f = OrderHom.id := by
  have fixOld : f (.old 0) = .old 0 := by
    have hx : f (.old 0) ≤ (.old 0 : Square) := h (.old 0)
    cases he : f (.old 0) with
    | old a => exact congrArg Graft.old (Subsingleton.elim a 0)
    | bottom => simp_all [Graft.le_iff, Graft.graftLE]
    | top i => simp_all [Graft.le_iff, Graft.graftLE]
  have fixBottom : f .bottom = .bottom := by
    have hx : f .bottom ≤ (.bottom : Square) := h .bottom
    cases he : f .bottom <;> simp_all [Graft.le_iff, Graft.graftLE]
  apply OrderHom.ext
  funext x
  change f x = x
  cases x with
  | old a => simpa only [show a = 0 from Subsingleton.elim _ _] using fixOld
  | bottom => exact fixBottom
  | top i =>
    have hp : (.old 0 : Square) ≤ f (.top i) := fixOld ▸ f.monotone (show
      (.old 0 : Square) ≤ .top i from le_rfl (a := (0 : Fin 1)))
    have hb : (.bottom : Square) ≤ f (.top i) := fixBottom ▸ f.monotone (show
      (.bottom : Square) ≤ .top i from trivial)
    have hx : f (.top i) ≤ (.top i : Square) := h (.top i)
    cases he : f (.top i) <;> simp_all [Graft.le_iff, Graft.graftLE]

private theorem squareIdentity {f g : Square →o Square} (h : Relation.EqvGen (· ≤ ·) f g) :
    (f = OrderHom.id ↔ g = OrderHom.id) := by
  induction h with
  | rel f g hfg =>
    constructor
    · rintro rfl
      exact squareUp g hfg
    · rintro rfl
      exact squareDown f hfg
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem oneTop {U : Set (Graft p m)} (hU : IsLowerSet U) (hcat : Categorical U)
    {i j : Fin m} (hi : .top i ∈ U) (hj : .top j ∈ U) : i = j := by
  classical
  by_contra hij
  have hp : (.old p : Graft p m) ∈ U := hU (show (.old p : Graft p m) ≤ .top i from le_rfl) hi
  have hb : (.bottom : Graft p m) ∈ U := hU (show (.bottom : Graft p m) ≤ .top i from trivial) hi
  let label (k : Fin 2) := if k = 0 then i else j
  have hlabel (k : Fin 2) : .top (label k) ∈ U := by
    unfold label
    split <;> assumption
  let e : Square →o U := {
    toFun := fun
      | .old _ => ⟨.old p, hp⟩
      | .bottom => ⟨.bottom, hb⟩
      | .top k => ⟨.top (label k), hlabel k⟩
    monotone' := by
      intro a b hab
      cases a <;> cases b <;> simp only [Graft.le_iff, Graft.graftLE] at hab
      all_goals first
        | exact le_rfl
        | exact trivial
        | subst_vars; exact le_rfl
  }
  let r : Graft p m →o Square := {
    toFun := fun
      | .old _ => .old 0
      | .bottom => .bottom
      | .top k => .top (if k = j then 1 else 0)
    monotone' := by
      intro a b hab
      cases a <;> cases b <;> simp only [Graft.le_iff, Graft.graftLE] at hab
      all_goals first
        | exact le_rfl
        | exact le_rfl (a := (0 : Fin 1))
        | exact trivial
        | subst_vars; exact le_rfl }
  obtain ⟨c, hc⟩ := hcat
  have hf := mapFence (fun (f : U →o Graft p m) => r.comp (f.comp e))
    (fun _ _ hfg x => r.monotone (OrderHom.le_def.mp hfg (e x))) hc
  have he : r.comp ((OrderEmbedding.subtype U).toOrderHom.comp e) = OrderHom.id := by
    apply OrderHom.ext
    funext x
    cases x with
    | old a =>
      change (Graft.old 0 : Square) = Graft.old a
      exact congrArg Graft.old (Subsingleton.elim _ _)
    | bottom => rfl
    | top k =>
      change (Graft.top (if label k = j then 1 else 0) : Square) = Graft.top k
      by_cases hk : k = 0
      · simp [label, hk, hij]
      · have hk' : k = 1 := by omega
        simp [label, hk']
  change Relation.EqvGen (· ≤ ·) (r.comp ((OrderEmbedding.subtype U).toOrderHom.comp e))
    (OrderHom.const Square (r c)) at hf
  rw [he] at hf
  have eq := (squareIdentity hf).mp rfl
  have impossible : (Graft.old 0 : Square) = Graft.bottom :=
    (DFunLike.congr_fun eq (.old 0)).symm.trans (DFunLike.congr_fun eq .bottom)
  cases impossible

private theorem topsBound (h : HasCategoricalCover (Graft p m) n) : m ≤ n := by
  classical
  obtain ⟨U, hU, cover⟩ := h
  choose slot hslot using fun j : Fin m => cover (.top j)
  have injective : Function.Injective slot := by
    intro i j hij
    exact oneTop (hU (slot i)).1 (hU (slot i)).2 (hslot i) (hij.symm ▸ hslot j)
  simpa using Fintype.card_le_of_injective slot injective

private def oldPiece (p : X) (m : ℕ) (U : Set X) : Set (Graft p m)
  | .old x => x ∈ U
  | _ => False

private def piece (p : X) (m : ℕ) (U : Set X) (j : Fin m) : Set (Graft p m)
  | .old x => x ∈ insert p U
  | .bottom => True
  | .top k => k = j

private theorem oldPieceLower {U : Set X} (hU : IsLowerSet U) :
    IsLowerSet (oldPiece p m U) := by
  intro a b hab hb
  cases a <;> cases b <;> first | exact hU hab hb | exact False.elim hb | exact False.elim hab

private theorem pieceLower {U : Set X} {j : Fin m} (hU : IsLowerSet U) (hp : IsMin p) :
    IsLowerSet (piece p m U j) := by
  have hInsert : IsLowerSet (insert p U) := by
    intro a b hab hb
    rcases Set.mem_insert_iff.mp hb with rfl | hb
    · exact Set.mem_insert_iff.mpr (Or.inl (hp.eq_of_le hab))
    · exact Set.mem_insert_iff.mpr (Or.inr (hU hab hb))
  intro a b hab hb
  cases a <;> cases b <;> first
    | exact hInsert hab hb
    | exact False.elim hab
    | exact Set.mem_insert_iff.mpr (Or.inl (hp.eq_of_le hab))
    | exact trivial
    | exact Eq.trans hab hb

private theorem oldPieceCategorical {U : Set X} (hU : Categorical U) :
    Categorical (oldPiece p m U) := by
  let e : oldPiece p m U →o U := {
    toFun := fun
      | ⟨.old x, hx⟩ => ⟨x, hx⟩
      | ⟨.bottom, hx⟩ => False.elim hx
      | ⟨.top _, hx⟩ => False.elim hx
    monotone' := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      cases a <;> cases b <;> first | exact hab | exact False.elim ha | exact False.elim hb }
  obtain ⟨c, hc⟩ := hU
  have hf := mapFence (fun (f : U →o X) => (oldHom (p := p) (m := m)).comp (f.comp e))
    (fun _ _ hfg x => oldHom.monotone (OrderHom.le_def.mp hfg (e x))) hc
  have he : oldHom.comp ((OrderEmbedding.subtype U).toOrderHom.comp e) =
      (OrderEmbedding.subtype (oldPiece p m U)).toOrderHom := by
    apply OrderHom.ext
    funext x
    obtain ⟨x, hx⟩ := x
    cases x <;> first | rfl | exact False.elim hx
  change Relation.EqvGen (· ≤ ·) (oldHom.comp ((OrderEmbedding.subtype U).toOrderHom.comp e))
    (OrderHom.const (oldPiece p m U) (.old c)) at hf
  rw [he] at hf
  exact ⟨.old c, hf⟩

/-- Extend a map to the adjoined root using its original value there when defined. -/
private noncomputable def extendRoot {U : Set X} (p : X) (f : U →o X) (x : X) : X := by
  classical
  exact if hx : x ∈ U then f ⟨x, hx⟩ else if hp : p ∈ U then f ⟨p, hp⟩ else p

private noncomputable def extendRootHom {U : Set X} (hU : IsLowerSet U) (hp : IsMin p)
    (f : U →o X) : (insert p U : Set X) →o X := by
  classical
  refine ⟨fun x => extendRoot p f x.val, ?_⟩
  intro x y hxy
  change x.val ≤ y.val at hxy
  by_cases hy : y.val ∈ U
  · have hx := hU hxy hy
    simpa only [extendRoot, dite_eq_left hx, dite_eq_left hy] using
      f.monotone (show (⟨x.val, hx⟩ : U) ≤ ⟨y.val, hy⟩ from hxy)
  · have hy' := (Set.mem_insert_iff.mp y.property).resolve_right hy
    have hx' := hp.eq_of_le (hy' ▸ hxy)
    change extendRoot p f x.val ≤ extendRoot p f y.val
    rw [hx', hy']

private theorem extendRootMono {U : Set X} (hU : IsLowerSet U) (hp : IsMin p) :
    Monotone (extendRootHom hU hp) := by
  classical
  intro f g h x
  change extendRoot p f x.val ≤ extendRoot p g x.val
  by_cases hx : x.val ∈ U
  · simpa only [extendRoot, dite_eq_left hx] using h ⟨x.val, hx⟩
  · by_cases hr : p ∈ U
    · simpa only [extendRoot, dite_eq_right hx, dite_eq_left hr] using h ⟨p, hr⟩
    · simp [extendRoot, hx, hr]

private theorem pieceCategorical {U : Set X} {j : Fin m} (hU : IsLowerSet U) (hp : IsMin p)
    (connected : ∀ x : X, Relation.EqvGen (· ≤ ·) x p) (hcat : Categorical U) :
    Categorical (piece p m U j) := by
  classical
  let V := piece p m U j
  let collapse : V →o (insert p U : Set X) := {
    toFun := fun x => ⟨retractOld x.val, by
      obtain ⟨x, hx⟩ := x
      cases x <;> first | exact hx | exact Set.mem_insert_iff.mpr (Or.inl rfl)⟩
    monotone' := fun _ _ h => retractOld.monotone h }
  -- Raise the new bottom to the chosen top, then compare down to the collapsed map.
  let raise : V →o Graft p m := {
    toFun := fun x => match x.val with
      | .bottom => .top j
      | a => a
    monotone' := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      change a ≤ b at hab
      cases a <;> cases b <;> first
        | exact hab
        | exact le_rfl
        | exact False.elim hab
        | exact (show _ = j from hb).symm }
  let lift (f : U →o X) : V →o Graft p m :=
    oldHom.comp ((extendRootHom hU hp f).comp collapse)
  have monotoneLift : Monotone lift :=
    fun _ _ h x => oldHom.monotone (extendRootMono hU hp h (collapse x))
  have start : lift (OrderEmbedding.subtype U).toOrderHom =
      oldHom.comp ((OrderEmbedding.subtype (insert p U : Set X)).toOrderHom.comp collapse) := by
    apply OrderHom.ext
    funext x
    let y := collapse x
    change (Graft.old (extendRoot p (OrderEmbedding.subtype U).toOrderHom y.val) : Graft p m) =
      Graft.old y.val
    by_cases hy : y.val ∈ U
    · simp only [extendRoot, dite_eq_left hy]
      rfl
    · have hy' := (Set.mem_insert_iff.mp y.property).resolve_right hy
      rw [hy']
      by_cases hr : p ∈ U
      · simp only [extendRoot, dite_eq_left hr]
        rfl
      · simp [extendRoot, hr]
  have up : (OrderEmbedding.subtype V).toOrderHom ≤ raise := by
    rintro ⟨x, hx⟩
    cases x <;> first | exact le_rfl | exact trivial
  have down : lift (OrderEmbedding.subtype U).toOrderHom ≤ raise := by
    rw [start]
    rintro ⟨x, hx⟩
    cases x <;> exact le_rfl
  have finish : lift (OrderHom.const U p) = OrderHom.const V (.old p) := by
    apply OrderHom.ext
    funext x
    change (Graft.old (extendRoot p (OrderHom.const U p) (collapse x).val) : Graft p m) =
      Graft.old p
    by_cases hx : (collapse x).val ∈ U <;> by_cases hr : p ∈ U <;> simp [extendRoot, hx, hr]
  obtain ⟨c, hc⟩ := hcat
  have toRoot := mapFence (OrderHom.const U) (OrderHom.const U).monotone (connected c)
  have liftFence := mapFence lift monotoneLift (.trans _ _ _ hc toRoot)
  rw [finish] at liftFence
  exact ⟨.old p, .trans _ _ _ (.rel _ _ up) (.trans _ _ _ (.symm _ _ (.rel _ _ down)) liftFence)⟩

private theorem graftCover (hp : IsMin p)
    (connected : ∀ x : X, Relation.EqvGen (· ≤ ·) x p)
    (h : HasCategoricalCover X n) (hmn : m ≤ n) (hm : 0 < m) :
    HasCategoricalCover (Graft p m) n := by
  obtain ⟨U, hU, cover⟩ := h
  let V (i : Fin n) : Set (Graft p m) :=
    if hi : i.val < m then piece p m (U i) ⟨i.val, hi⟩ else oldPiece p m (U i)
  refine ⟨V, ?_, ?_⟩
  · intro i
    by_cases hi : i.val < m
    · simp only [V, dite_eq_left hi]
      exact ⟨pieceLower (hU i).1 hp, pieceCategorical (hU i).1 hp connected (hU i).2⟩
    · simp only [V, dite_eq_right hi]
      exact ⟨oldPieceLower (hU i).1, oldPieceCategorical (hU i).2⟩
  · intro x
    cases x with
    | old x =>
      obtain ⟨i, hi⟩ := cover x
      refine ⟨i, ?_⟩
      by_cases hlt : i.val < m
      · simp only [V, dite_eq_left hlt]
        exact Set.mem_insert_iff.mpr (Or.inr hi)
      · simp only [V, dite_eq_right hlt]
        exact hi
    | bottom =>
      refine ⟨⟨0, hm.trans_le hmn⟩, ?_⟩
      simp only [V, dite_eq_left hm]
      trivial
    | top j =>
      refine ⟨⟨j.val, j.isLt.trans_le hmn⟩, ?_⟩
      simp only [V, dite_eq_left j.isLt]
      exact Fin.ext rfl

/-- For a connected poset and a minimal root, grafting `B_m` gives a categorical
lower cover with `n` pieces exactly when the original poset has such a cover
and there are at least `m` pieces. -/
theorem hasCategoricalCover_graft_iff (hp : IsMin p)
    (connected : ∀ x : X, Relation.EqvGen (· ≤ ·) x p) (hm : 2 ≤ m) :
    HasCategoricalCover (Graft p m) n ↔ HasCategoricalCover X n ∧ m ≤ n :=
  ⟨fun h => ⟨restrictCover h, topsBound h⟩, fun h => graftCover hp connected h.1 h.2 (by omega)⟩


end D5.S3.Topology.ConnectedCategoryGraft
