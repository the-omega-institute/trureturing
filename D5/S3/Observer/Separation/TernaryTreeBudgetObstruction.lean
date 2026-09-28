/- GID: D5/S3/Observer/Separation/TernaryTreeBudgetObstruction
   generality: I
   mirror-B: D5/B/S3/Observer/Separation/TernaryTreeBudgetObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.claim; result=D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.result; claim=D5/S3/Observer/Separation/TernaryTreeBudgetObstruction.claim
   digest: A ternary partial table has tree support and original costs two but admits no two-by-two simultaneous protocol. -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SimpleGraph

namespace D5.S3.Observer.Separation.TernaryTreeBudgetObstruction

/-- Absence is not an output; all three output symbols are genuine values. -/
abbrev Task (X Y : Type) := X → Y → Option (Fin 3)

def table : Task (Fin 3) (Fin 3) :=
  ![![some 0, none, none], ![some 1, some 0, none], ![none, some 1, some 2]]

def support {X Y : Type} (t : Task X Y) : SimpleGraph (X ⊕ Y) where
  Adj a b := match a, b with
    | .inl x, .inr y => t x y ≠ none
    | .inr y, .inl x => t x y ≠ none
    | _, _ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> exact id⟩
  loopless := ⟨by intro a; cases a <;> exact not_false⟩

def conflictLeft {X Y : Type} (t : Task X Y) : SimpleGraph X where
  Adj x x' := ∃ y a b, t x y = some a ∧ t x' y = some b ∧ a ≠ b
  symm := ⟨by rintro x x' ⟨y, a, b, ha, hb, hab⟩; exact ⟨y, b, a, hb, ha, hab.symm⟩⟩
  loopless := ⟨by rintro x ⟨y, a, b, ha, hb, hab⟩; exact hab (Option.some.inj (ha.symm.trans hb))⟩

def conflictRight {X Y : Type} (t : Task X Y) : SimpleGraph Y :=
  conflictLeft (fun y x => t x y)

/-- Ambient alphabets need not be finite. Only reachable images are charged. -/
def HasBudget {X Y : Type} (t : Task X Y) (p q : ℕ) : Prop :=
  ∃ (A B : Type) (α : X → A) (β : Y → B) (δ : A → B → Fin 3),
    Nat.card (Set.range α) ≤ p ∧ Nat.card (Set.range β) ≤ q ∧
    ∀ x y o, t x y = some o → δ (α x) (β y) = o

/-- A one-sided cut retains the other party's original input at the decoder. -/
def HasOriginalBudget {X Y : Type} (t : Task X Y) (p : ℕ) : Prop :=
  ∃ (A : Type) (α : X → A) (δ : A → Y → Fin 3),
    Nat.card (Set.range α) ≤ p ∧
    ∀ x y o, t x y = some o → δ (α x) y = o

noncomputable def originalCost {X Y : Type} (t : Task X Y) : ℕ :=
  sInf {p | HasOriginalBudget t p}

/-- The order x0,y0,x1,y1,x2,y2 on the actual bipartite vertices. -/
def pathIndex : Fin 3 ⊕ Fin 3 → Fin 6 := Sum.elim ![0, 2, 4] ![1, 3, 5]

/-- The full concrete hypotheses, including exact costs, are certified together. -/
def ActualProperties : Prop :=
  Fintype.card (Fin 3) = 3 ∧
  (∀ o : Fin 3, ∃ x y, table x y = some o) ∧
  (∀ x, ∃ y o, table x y = some o) ∧
  (∀ y, ∃ x o, table x y = some o) ∧
  Nat.card {xy : Fin 3 × Fin 3 // table xy.1 xy.2 ≠ none} = 5 ∧
  Nat.card (support table).edgeSet = 5 ∧
  Fintype.card (Fin 3 ⊕ Fin 3) = 6 ∧
  Function.Bijective pathIndex ∧
  (∀ v w, (support table).Adj v w ↔
    (pathIndex v).val + 1 = (pathIndex w).val ∨
    (pathIndex w).val + 1 = (pathIndex v).val) ∧
  (support table).IsTree ∧
  ((Nat.card {xy : Fin 3 × Fin 3 // table xy.1 xy.2 ≠ none} : ℤ) -
    (Fintype.card (Fin 3) : ℤ) - (Fintype.card (Fin 3) : ℤ) + 1 = 0) ∧
  conflictLeft table = pathGraph 3 ∧
  conflictRight table = pathGraph 3 ∧
  (conflictLeft table).chromaticNumber = 2 ∧
  (conflictRight table).chromaticNumber = 2 ∧
  originalCost table = 2 ∧
  originalCost (fun y x => table x y) = 2

/-- The Boolean-hypothesis-dropping claim specialized to its proposed ternary witness.
Its negation entails both the full positive certificate and absence of every protocol. -/
def claim : Prop := ActualProperties → HasBudget table 2 2

/-- The same actual ternary table has all stated positive properties, yet every
pair of separate encoders with at most two reachable messages fails correctness. -/
theorem result : ¬ claim := by
  classical
  have legalCard : Nat.card {xy : Fin 3 × Fin 3 // table xy.1 xy.2 ≠ none} = 5 := by
    rw [Nat.card_eq_fintype_card]
    decide
  let legalEdge : {xy : Fin 3 × Fin 3 // table xy.1 xy.2 ≠ none} →
      (support table).edgeSet :=
    fun xy => ⟨s(Sum.inl xy.val.1, Sum.inr xy.val.2), xy.property⟩
  have legalBij : Function.Bijective legalEdge := by
    constructor
    · intro a b hab
      have he := congrArg Subtype.val hab
      have he' : a.val.1 = b.val.1 ∧ a.val.2 = b.val.2 := by
        simpa only [legalEdge, Sym2.eq_iff, Prod.mk.injEq, Sum.inl.injEq,
          Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, and_self, or_false] using he
      exact Subtype.ext (Prod.ext he'.1 he'.2)
    · rintro ⟨e, he⟩
      induction e using Sym2.inductionOn with | _ a b =>
        cases a with
        | inl x =>
          cases b with
          | inl x' => exact False.elim he
          | inr y => exact ⟨⟨(x, y), he⟩, rfl⟩
        | inr y =>
          cases b with
          | inl x => exact ⟨⟨(x, y), he⟩, Subtype.ext Sym2.eq_swap⟩
          | inr y' => exact False.elim he
  have edgeCard : Nat.card (support table).edgeSet = 5 :=
    (Nat.card_congr (Equiv.ofBijective legalEdge legalBij)).symm.trans legalCard
  have connected : (support table).Connected := by
    have e00 : (support table).Reachable (.inl 0) (.inr 0) :=
      (show (support table).Adj (.inl 0) (.inr 0) by simp [support, table]).reachable
    have e10 : (support table).Reachable (.inl 1) (.inr 0) :=
      (show (support table).Adj (.inl 1) (.inr 0) by simp [support, table]).reachable
    have e11 : (support table).Reachable (.inl 1) (.inr 1) :=
      (show (support table).Adj (.inl 1) (.inr 1) by simp [support, table]).reachable
    have e21 : (support table).Reachable (.inl 2) (.inr 1) :=
      (show (support table).Adj (.inl 2) (.inr 1) by simp [support, table]).reachable
    have e22 : (support table).Reachable (.inl 2) (.inr 2) :=
      (show (support table).Adj (.inl 2) (.inr 2) by simp [support, table]).reachable
    apply (connected_iff_exists_forall_reachable _).mpr
    refine ⟨.inl 1, ?_⟩
    intro v
    cases v with
    | inl x => fin_cases x; exact e10.trans e00.symm; exact Reachable.refl _; exact e11.trans e21.symm
    | inr y => fin_cases y; exact e10; exact e11; exact (e11.trans e21.symm).trans e22
  have tree : (support table).IsTree := by
    apply isTree_iff_connected_and_card.mpr
    exact ⟨connected, by rw [edgeCard]; simp⟩
  have leftPath : conflictLeft table = pathGraph 3 := by
    ext x x'
    rw [pathGraph_adj]
    dsimp only [conflictLeft]
    fin_cases x <;> fin_cases x' <;> decide
  have rightPath : conflictRight table = pathGraph 3 := by
    ext y y'
    rw [pathGraph_adj]
    dsimp only [conflictRight, conflictLeft]
    fin_cases y <;> fin_cases y' <;> decide
  have two_le {A : Type} (α : Fin 3 → A) (h : α 0 ≠ α 1) :
      2 ≤ Nat.card (Set.range α) := by
    let f : Fin 2 → Set.range α := ![⟨α 0, ⟨0, rfl⟩⟩, ⟨α 1, ⟨1, rfl⟩⟩]
    have hf : Function.Injective f := by
      intro i j hij
      have hv := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact False.elim (h hv)
      · exact False.elim (h hv.symm)
      · rfl
    simpa using Nat.card_le_card_of_injective f hf
  let color : Fin 3 → Fin 2 := ![0, 1, 0]
  have colorCard : Nat.card (Set.range color) ≤ 2 :=
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans (by simp)
  have upperL : HasOriginalBudget table 2 := by
    refine ⟨Fin 2, color, ![![0, 1, 2], ![1, 0, 0]], colorCard, ?_⟩
    decide
  have upperR : HasOriginalBudget (fun y x => table x y) 2 := by
    refine ⟨Fin 2, color, ![![0, 1, 2], ![0, 0, 1]], colorCard, ?_⟩
    decide
  have lowerL : ∀ p, HasOriginalBudget table p → 2 ≤ p := by
    rintro p ⟨A, α, δ, hc, hd⟩
    have h01 : α 0 ≠ α 1 := by
      intro he
      have h0 := hd 0 0 0 rfl
      have h1 := hd 1 0 1 rfl
      rw [he, h1] at h0
      exact (by decide : (1 : Fin 3) ≠ 0) h0
    exact (two_le α h01).trans hc
  have lowerR : ∀ p, HasOriginalBudget (fun y x => table x y) p → 2 ≤ p := by
    rintro p ⟨A, α, δ, hc, hd⟩
    have h01 : α 0 ≠ α 1 := by
      intro he
      have h0 := hd 0 1 1 rfl
      have h1 := hd 1 1 0 rfl
      rw [he, h1] at h0
      exact (by decide : (0 : Fin 3) ≠ 1) h0
    exact (two_le α h01).trans hc
  have costL : originalCost table = 2 :=
    IsLeast.csInf_eq ⟨upperL, lowerL⟩
  have costR : originalCost (fun y x => table x y) = 2 :=
    IsLeast.csInf_eq ⟨upperR, lowerR⟩
  have actual : ActualProperties := by
    refine ⟨by decide, by decide, by decide, by decide, legalCard, edgeCard,
      by decide, ?_, ?_, tree, ?_, leftPath, rightPath, ?_, ?_, costL, costR⟩
    · decide
    · intro v w
      cases v <;> cases w <;> rename_i i j <;> fin_cases i <;> fin_cases j <;> simp [support, table, pathIndex]
    · rw [legalCard]; norm_num
    · rw [leftPath]; exact chromaticNumber_pathGraph 3 (by decide)
    · rw [rightPath]; exact chromaticNumber_pathGraph 3 (by decide)
  have impossible : ¬ HasBudget table 2 2 := by
    rintro ⟨A, B, α, β, δ, ha, hb, hd⟩
    have a01 : α 0 ≠ α 1 := by
      intro he
      have h0 := hd 0 0 0 rfl
      have h1 := hd 1 0 1 rfl
      rw [he, h1] at h0
      exact (by decide : (1 : Fin 3) ≠ 0) h0
    have a12 : α 1 ≠ α 2 := by
      intro he
      have h0 := hd 1 1 0 rfl
      have h1 := hd 2 1 1 rfl
      rw [he, h1] at h0
      exact (by decide : (1 : Fin 3) ≠ 0) h0
    have b01 : β 0 ≠ β 1 := by
      intro he
      have h0 := hd 1 0 1 rfl
      have h1 := hd 1 1 0 rfl
      rw [he, h1] at h0
      exact (by decide : (0 : Fin 3) ≠ 1) h0
    have b12 : β 1 ≠ β 2 := by
      intro he
      have h0 := hd 2 1 1 rfl
      have h1 := hd 2 2 2 rfl
      rw [he, h1] at h0
      exact (by decide : (2 : Fin 3) ≠ 1) h0
    have endpoints {C : Type} (e : Fin 3 → C)
        (hc : Nat.card (Set.range e) ≤ 2) (h01 : e 0 ≠ e 1) (h12 : e 1 ≠ e 2) :
        e 0 = e 2 := by
      by_contra h02
      have hi : Function.Injective e := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      have hthree := Nat.card_range_of_injective hi
      have : Nat.card (Set.range e) = 3 := by simpa using hthree
      omega
    have ae : α 0 = α 2 := endpoints α ha a01 a12
    have be : β 0 = β 2 := endpoints β hb b01 b12
    have h0 := hd 0 0 0 rfl
    have h2 := hd 2 2 2 rfl
    rw [ae, be, h2] at h0
    exact (by decide : (2 : Fin 3) ≠ 0) h0
  intro purported
  exact impossible (purported actual)


end D5.S3.Observer.Separation.TernaryTreeBudgetObstruction
