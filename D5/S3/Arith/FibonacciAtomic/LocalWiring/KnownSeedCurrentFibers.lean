/- GID: D5/S3/Arith/FibonacciAtomic/LocalWiring/KnownSeedCurrentFibers
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LocalWiring/KnownSeedCurrentFibers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Basic]
   utility: none
   digest: Exact known-alpha current fibres and complete one-update presence predictions. -/

import D5.S3.Arith.FibonacciAtomic.LocalWiring.LocalTwoStepRecognizer
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators

/-! Count the actual known-seed fibres and predict the next physical presence bit. -/

namespace D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers

open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.LocalTwoStepRecognizer

abbrev leaves {A : Type} (t : FreeMagma A) : Nat := t.length

private theorem leaves_shape (t : Labelled) : leaves (shape t) = leaves t := by
  induction t with
  | of a => rfl
  | mul a b ha hb =>
    change leaves (shape a) + leaves (shape b) = leaves a + leaves b
    rw [ha, hb]

/-- The physical states that arise from the known alpha seed in exactly the indexed
number of actual serial updates, retaining all possible local newborn choices. -/
inductive After : Nat → Labelled → Prop
  | zero : After 0 alpha
  | next : After n x → Step x y → After (n + 1) y

/-- The physical rank grammar, with each birth allowed to choose its orientation. -/
inductive Rank : Nat → Labelled → Prop
  | zero : Rank 0 alpha
  | one : Rank 1 beta
  | straight : Rank (n + 1) u → Rank n v → Rank (n + 2) (.mul u v)
  | crossed : Rank (n + 1) u → Rank n v → Rank (n + 2) (.mul v u)

private theorem rank_next {n x y} (h : Rank n x) (s : Step x y) : Rank (n + 1) y := by
  induction h generalizing y with
  | zero =>
    cases s
    exact .one
  | one =>
    cases s with
    | betaLeft => exact .straight .one .zero
    | betaRight => exact .crossed .one .zero
  | straight _ _ ih₁ ih₂ =>
    cases s with
    | branch h₁ h₂ => exact .straight (ih₁ h₁) (ih₂ h₂)
  | crossed _ _ ih₁ ih₂ =>
    cases s with
    | branch h₁ h₂ => exact .crossed (ih₁ h₂) (ih₂ h₁)

private theorem rank_previous {n x} (h : Rank n x) (hn : n ≠ 0) :
    ∃ y, Rank (n - 1) y ∧ Step y x := by
  induction h with
  | zero => exact (hn rfl).elim
  | one => exact ⟨_, .zero, .alphaToBeta⟩
  | @straight n _ _ h₁ h₂ ih₁ ih₂ =>
    cases n with
    | zero =>
      cases h₁
      cases h₂
      exact ⟨_, .one, .betaLeft⟩
    | succ n =>
      obtain ⟨a, ha, sa⟩ := ih₁ (Nat.succ_ne_zero _)
      obtain ⟨b, hb, sb⟩ := ih₂ (Nat.succ_ne_zero _)
      exact ⟨_, .straight ha hb, .branch sa sb⟩
  | @crossed n _ _ h₁ h₂ ih₁ ih₂ =>
    cases n with
    | zero =>
      cases h₁
      cases h₂
      exact ⟨_, .one, .betaRight⟩
    | succ n =>
      obtain ⟨a, ha, sa⟩ := ih₁ (Nat.succ_ne_zero _)
      obtain ⟨b, hb, sb⟩ := ih₂ (Nat.succ_ne_zero _)
      exact ⟨_, .crossed ha hb, .branch sb sa⟩

private theorem rank_iff_after (n : Nat) (t : Labelled) : Rank n t ↔ After n t := by
  constructor
  · induction n generalizing t with
    | zero =>
      intro h
      cases h
      exact .zero
    | succ n ih =>
      intro h
      obtain ⟨p, hp, st⟩ := rank_previous h (Nat.succ_ne_zero _)
      exact .next (ih p hp) st
  · intro h
    induction h with
    | zero => exact .zero
    | next _ s ih => exact rank_next ih s

private theorem rank_leaves : Rank n t → leaves t = Nat.fib (n+1) := by
  intro h
  induction h with
  | zero => rfl
  | one => rfl
  | straight hu hv iu iv =>
    simp only [FreeMagma.length, iu, iv, Nat.fib_add_two]
    omega
  | crossed hu hv iu iv =>
    simp only [FreeMagma.length, iu, iv, Nat.fib_add_two]

private theorem fib_successor_lt (m : Nat) (hm : 1 ≤ m) : Nat.fib (m+1) < Nat.fib (m+2) := by
  have := Nat.fib_pos.mpr (by omega : 0 < m)
  rw [Nat.fib_add_two]
  omega

abbrev Address := List Bool

def atTree {A : Type} (t : FreeMagma A) : Address → Option (FreeMagma A)
  | [] => some t
  | false :: p => match t with | .of _ => none | .mul l _ => atTree l p
  | true :: p => match t with | .of _ => none | .mul _ r => atTree r p

def present {A : Type} (t : FreeMagma A) (p : Address) : Bool := (atTree t p).isSome

def isBeta (t : Labelled) (p : Address) : Bool := decide (atTree t p = some beta)

private theorem atTree_append {A : Type} (t : FreeMagma A) (p q : Address) :
    atTree t (p ++ q) = (atTree t p).bind (fun u => atTree u q) := by
  induction p generalizing t with
  | nil => simp [atTree]
  | cons b p ih =>
    cases t with
    | of a => cases b <;> rfl
    | mul l r => cases b <;> exact ih _

private theorem atTree_shape (t : Labelled) (p : Address) :
    atTree (shape t) p = (atTree t p).map shape := by
  induction p generalizing t with
  | nil => simp [atTree]
  | cons b p ih =>
    cases t with
    | of a => cases b <;> rfl
    | mul l r => cases b <;> exact ih _

private theorem present_shape (t : Labelled) (p : Address) :
    present (shape t) p = present t p := by
  simp [present, atTree_shape]

private theorem step_present (t w : Labelled) (h : Step t w) (p : Address) :
    present w p = true ↔ present t p = true ∨
      ∃ q : Address, ∃ b : Bool, isBeta t q = true ∧ p = q ++ [b] := by
  induction h generalizing p with
  | alphaToBeta =>
    have no (q : Address) : ¬ isBeta alpha q = true := by
      cases q with
      | nil => decide
      | cons b q => cases b <;> simp [isBeta, atTree]
    cases p with
    | nil => simp [present, atTree]
    | cons b p => cases b <;> simp [present, atTree, fun q => no q]
  | betaLeft =>
    have bet (q : Address) : isBeta beta q = true ↔ q = [] := by
      cases q with
      | nil => decide
      | cons b q => cases b <;> simp [isBeta, atTree]
    simp only [bet]
    cases p with
    | nil => simp [present, atTree]
    | cons b p =>
      cases b <;> cases p with
      | nil => simp [present, atTree]
      | cons c p => cases c <;> simp [present, atTree]
  | betaRight =>
    have bet (q : Address) : isBeta beta q = true ↔ q = [] := by
      cases q with
      | nil => decide
      | cons b q => cases b <;> simp [isBeta, atTree]
    simp only [bet]
    cases p with
    | nil => simp [present, atTree]
    | cons b p =>
      cases b <;> cases p with
      | nil => simp [present, atTree]
      | cons c p => cases c <;> simp [present, atTree]
  | @branch a a' b b' ha hb ih₁ ih₂ =>
    cases p with
    | nil => simp [present, atTree]
    | cons bit p =>
      cases bit
      · change present a' p = true ↔ present a p = true ∨ _
        rw [ih₁]
        apply or_congr_right
        constructor
        · rintro ⟨q, c, hq, rfl⟩
          exact ⟨false :: q, c, hq, rfl⟩
        · rintro ⟨q, c, hq, he⟩
          cases q with
          | nil => simp [isBeta, atTree] at hq
          | cons d q =>
            simp only [List.cons_append, List.cons.injEq] at he
            obtain ⟨rfl, he⟩ := he
            exact ⟨q, c, hq, he⟩
      · change present b' p = true ↔ present b p = true ∨ _
        rw [ih₂]
        apply or_congr_right
        constructor
        · rintro ⟨q, c, hq, rfl⟩
          exact ⟨true :: q, c, hq, rfl⟩
        · rintro ⟨q, c, hq, he⟩
          cases q with
          | nil => simp [isBeta, atTree] at hq
          | cons d q =>
            simp only [List.cons_append, List.cons.injEq] at he
            obtain ⟨rfl, he⟩ := he
            exact ⟨q, c, hq, he⟩

private theorem cherry_step_bit (t w : Labelled) (h : Step t w) (p : Address)
    (hc : atTree (shape t) p = some cherry) :
    present w (p ++ [false, false]) = isBeta t (p ++ [false]) := by
  rw [atTree_shape] at hc
  cases ha : atTree t p with
  | none => simp [ha] at hc
  | some u =>
    simp only [ha, Option.map_some, Option.some.injEq] at hc
    cases u with
    | of v => cases hc
    | mul l r =>
      cases l with
      | mul a b => cases hc
      | of lab =>
        have hn : present t (p ++ [false, false]) = false := by
          simp [present, atTree_append, ha, atTree]
        apply Bool.eq_iff_iff.mpr
        rw [step_present t w h]
        simp only [hn, Bool.false_eq_true, false_or]
        constructor
        · rintro ⟨q, b, hq, he⟩
          have he' : (p ++ [false]) ++ [false] = q ++ [b] := by simpa using he
          have hq' := congrArg List.dropLast he'
          simpa using (show isBeta t (p ++ [false]) = true by
            simp at hq'
            simpa [hq'] using hq)
        · intro hq
          exact ⟨p ++ [false], false, hq, by simp⟩

private def prefixAddr (b : Bool) : Address ↪ Address :=
  ⟨List.cons b, fun _ _ h => (List.cons.inj h).2⟩

def cherries : Shape → Finset Address
  | .of _ => ∅
  | .mul l r => (if l = tip ∧ r = tip then {[]} else ∅) ∪
       ((cherries l).map (prefixAddr false) ∪ (cherries r).map (prefixAddr true))

private theorem mem_cherries (s : Shape) (p : Address) :
    p ∈ cherries s ↔ atTree s p = some cherry := by
  induction s generalizing p with
  | of a =>
    cases a
    cases p with
    | nil => simp [atTree, cherries]
    | cons b p => cases b <;> simp [atTree, cherries]
  | mul l r ih₁ ih₂ =>
    have he (x y : Shape) : FreeMagma.mul x y = cherry ↔ x = tip ∧ y = tip := by
      constructor
      · intro h; cases h; exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩; rfl
    have pref (b : Bool) (q : Address) : prefixAddr b q = b :: q := rfl
    cases p with
    | nil =>
      change [] ∈ (if l = tip ∧ r = tip then {[]} else ∅) ∪
        ((cherries l).map (prefixAddr false) ∪ (cherries r).map (prefixAddr true)) ↔
          some (FreeMagma.mul l r) = some cherry
      rw [Option.some.injEq, he]
      by_cases hc : l = tip ∧ r = tip <;>
        simp [Finset.mem_map, pref, hc]
    | cons b p =>
      have hroot : b :: p ∉ (if l = tip ∧ r = tip then ({[]} : Finset Address) else ∅) := by
        by_cases hc : l = tip ∧ r = tip <;> simp [hc]
      simp only [cherries, Finset.mem_union, hroot, false_or, Finset.mem_map, pref]
      cases b
      · simpa [atTree] using ih₁ p
      · simpa [atTree] using ih₂ p

private theorem cherries_pair (l r : Shape) (h : ¬ (l = tip ∧ r = tip)) :
    cherries (.mul l r) =
      (cherries l).map (prefixAddr false) ∪ (cherries r).map (prefixAddr true) := by
  simp [cherries, h]

private theorem prefixed_cherries_disjoint (l r : Shape) :
    Disjoint ((cherries l).map (prefixAddr false)) ((cherries r).map (prefixAddr true)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hp
  obtain ⟨b, _, hb⟩ := Finset.mem_map.mp hq
  have he : false :: a = true :: b := ha.trans hb.symm
  cases he

private theorem cherries_pair_card (l r : Shape) (h : ¬ (l = tip ∧ r = tip)) :
    (cherries (.mul l r)).card = (cherries l).card + (cherries r).card := by
  rw [cherries_pair l r h, Finset.card_union_of_disjoint (prefixed_cherries_disjoint l r)]
  simp

private theorem cherries_cherry : cherries cherry = {[]} := by
  simp [cherries]

private theorem not_tip_of_rank {n : Nat} {t : Labelled} (h : Rank (n + 2) t) :
    shape t ≠ tip := by
  cases h <;> intro he <;> cases he

private theorem fib_add_shifted (n : Nat) (hn : 1 ≤ n) :
    Nat.fib ((n + 1) - 1) + Nat.fib (n - 1) = Nat.fib ((n + 2) - 1) := by
  cases n with
  | zero => omega
  | succ m =>
    change Nat.fib (m + 1) + Nat.fib m = Nat.fib (m + 2)
    rw [Nat.fib_add_two (n := m), Nat.add_comm]

private theorem rank_cherries {n : Nat} {t : Labelled} (h : Rank n t) :
    (cherries (shape t)).card = Nat.fib (n - 1) := by
  induction h with
  | zero => decide
  | one => decide
  | @straight n u v hu hv iu iv =>
    cases n with
    | zero =>
      cases hu
      cases hv
      change (cherries cherry).card = Nat.fib 1
      rw [cherries_cherry]
      decide
    | succ m =>
      change (cherries (.mul (shape u) (shape v))).card = _
      rw [cherries_pair_card _ _ (fun h => not_tip_of_rank hu h.1), iu, iv]
      exact fib_add_shifted (m + 1) (by omega)
  | @crossed n u v hu hv iu iv =>
    cases n with
    | zero =>
      cases hu
      cases hv
      change (cherries cherry).card = Nat.fib 1
      rw [cherries_cherry]
      decide
    | succ m =>
      change (cherries (.mul (shape v) (shape u))).card = _
      rw [cherries_pair_card _ _ (fun h => not_tip_of_rank hu h.2), iu, iv, Nat.add_comm]
      exact fib_add_shifted (m + 1) (by omega)
private def branchEmbedding {A : Type} : FreeMagma A × FreeMagma A ↪ FreeMagma A where
  toFun p := .mul p.1 p.2
  inj' := by rintro ⟨x, y⟩ ⟨u, v⟩ h; cases h; rfl

private def branches {A : Type} (s t : Finset (FreeMagma A)) : Finset (FreeMagma A) :=
  (s ×ˢ t).map branchEmbedding

private theorem mem_branches {A : Type} {s t : Finset (FreeMagma A)} {x : FreeMagma A} :
    x ∈ branches s t ↔ ∃ u ∈ s, ∃ v ∈ t, FreeMagma.mul u v = x := by
  simp only [branches, Finset.mem_map, Finset.mem_product]
  constructor
  · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
    exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩

private theorem card_branches {A : Type} (s t : Finset (FreeMagma A)) :
    (branches s t).card = s.card * t.card := by
  simp [branches, Finset.card_product]

private theorem disjoint_branches {A : Type} {s t : Finset (FreeMagma A)}
    (h : Disjoint s t) : Disjoint (branches s t) (branches t s) := by
  rw [Finset.disjoint_left] at h ⊢
  intro x hx hy
  obtain ⟨u, hu, v, _, rfl⟩ := mem_branches.mp hx
  obtain ⟨u', hu', v', _, h'⟩ := mem_branches.mp hy
  cases h'
  exact h hu hu'

/-- Enumerate ranked labelled physical trees, including both physical orders. -/
def rankedTrees : ℕ → Finset Labelled
  | 0 => {alpha}
  | 1 => {beta}
  | n+2 =>
    branches (rankedTrees (n+1)) (rankedTrees n) ∪
      branches (rankedTrees n) (rankedTrees (n+1))

private theorem mem_rankedTrees_iff (n : ℕ) (x : Labelled) : x ∈ rankedTrees n ↔ Rank n x := by
  induction n using Nat.twoStepInduction generalizing x with
  | zero =>
    constructor
    · intro h
      have h' : x = alpha := Finset.mem_singleton.mp h
      subst x
      exact .zero
    · intro h
      cases h
      exact Finset.mem_singleton_self _
  | one =>
    constructor
    · intro h
      have h' : x = beta := Finset.mem_singleton.mp h
      subst x
      exact .one
    · intro h
      cases h
      exact Finset.mem_singleton_self _
  | more n ih₀ ih₁ =>
    simp only [rankedTrees, Finset.mem_union, mem_branches, ih₀, ih₁]
    constructor
    · rintro (⟨u, hu, v, hv, rfl⟩ | ⟨u, hu, v, hv, rfl⟩)
      · exact .straight hu hv
      · exact .crossed hv hu
    · intro h
      cases h with
      | straight hu hv => exact Or.inl ⟨_, hu, _, hv, rfl⟩
      | crossed hu hv => exact Or.inr ⟨_, hv, _, hu, rfl⟩

private theorem rankedTrees_disjoint (n : ℕ) :
    Disjoint (rankedTrees (n+1)) (rankedTrees n) := by
  rw [Finset.disjoint_left]
  intro x h₁ h₀
  have h₁ := (mem_rankedTrees_iff _ _).mp h₁
  have h₀ := (mem_rankedTrees_iff _ _).mp h₀
  cases n with
  | zero => cases h₀; cases h₁
  | succ n =>
    have hlt := fib_successor_lt (n+1) (by omega)
    rw [← rank_leaves h₁, ← rank_leaves h₀] at hlt
    exact (lt_irrefl _ hlt)

private theorem pow_two_branch_count {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    2^(i-1) * 2^(j-1) + 2^(j-1) * 2^(i-1) = (2 : ℕ)^(i+j-1) := by
  rw [Nat.mul_comm (2^(j-1)), ← pow_add]
  have he : i+j-1 = (i-1+(j-1))+1 := by omega
  rw [he, pow_succ, Nat.mul_two]

private theorem card_rankedTrees (n : ℕ) : (rankedTrees n).card = 2^(Nat.fib (n+1)-1) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih₀ ih₁ =>
    rw [rankedTrees, Finset.card_union_of_disjoint
      (disjoint_branches (rankedTrees_disjoint n)), card_branches, card_branches,
      ih₀, ih₁, show n+2+1 = (n+1)+2 by omega, Nat.fib_add_two (n := n+1)]
    rw [Nat.add_comm (Nat.fib (n+1))]
    exact pow_two_branch_count (Nat.fib_pos.mpr (by omega)) (Nat.fib_pos.mpr (by omega))

/-- Shape enumeration is the actual image of the labelled physical enumeration. -/
def rankedShapes (n : ℕ) : Finset Shape := (rankedTrees n).image shape

private theorem mem_rankedShapes_iff (n : ℕ) (s : Shape) :
    s ∈ rankedShapes n ↔ ∃ t, Rank n t ∧ shape t = s := by
  simp [rankedShapes, Finset.mem_image, mem_rankedTrees_iff]

private theorem rankedShapes_zero : rankedShapes 0 = {tip} := by decide
private theorem rankedShapes_one : rankedShapes 1 = {tip} := by decide
private theorem rankedShapes_two : rankedShapes 2 = {cherry} := by decide

private theorem rankedShapes_add_two (n : ℕ) :
    rankedShapes (n+2) =
      branches (rankedShapes (n+1)) (rankedShapes n) ∪
        branches (rankedShapes n) (rankedShapes (n+1)) := by
  ext s
  simp only [mem_rankedShapes_iff, Finset.mem_union, mem_branches]
  constructor
  · rintro ⟨t, h, rfl⟩
    cases h with
    | straight h₁ h₀ =>
      exact Or.inl ⟨_, ⟨_, h₁, rfl⟩, _, ⟨_, h₀, rfl⟩, rfl⟩
    | crossed h₁ h₀ =>
      exact Or.inr ⟨_, ⟨_, h₀, rfl⟩, _, ⟨_, h₁, rfl⟩, rfl⟩
  · rintro (⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩ | ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩)
    · exact ⟨.mul u v, .straight hu hv, rfl⟩
    · exact ⟨.mul u v, .crossed hv hu, rfl⟩

private theorem rankedShapes_disjoint (n : ℕ) (hn : 1 ≤ n) :
    Disjoint (rankedShapes (n+1)) (rankedShapes n) := by
  rw [Finset.disjoint_left]
  intro x h₁ h₀
  obtain ⟨u, hu, he₁⟩ := (mem_rankedShapes_iff _ _).mp h₁
  obtain ⟨v, hv, he₀⟩ := (mem_rankedShapes_iff _ _).mp h₀
  have hu' := (leaves_shape u).trans (rank_leaves hu)
  have hv' := (leaves_shape v).trans (rank_leaves hv)
  rw [he₁] at hu'
  rw [he₀] at hv'
  exact (fib_successor_lt n hn).ne (hv'.symm.trans hu')

private theorem card_rankedShapes (n : ℕ) : (rankedShapes n).card = 2^(Nat.fib n-1) := by
  induction n using Nat.twoStepInduction with
  | zero => rw [rankedShapes_zero]; decide
  | one => rw [rankedShapes_one]; decide
  | more n ih₀ ih₁ =>
    cases n with
    | zero => rw [rankedShapes_two]; decide
    | succ n =>
      rw [rankedShapes_add_two, Finset.card_union_of_disjoint
        (disjoint_branches (rankedShapes_disjoint (n+1) (by omega))),
        card_branches, card_branches, ih₀, ih₁, Nat.fib_add_two (n := n+1)]
      rw [Nat.add_comm (Nat.fib (n+1))]
      exact pow_two_branch_count (Nat.fib_pos.mpr (by omega)) (Nat.fib_pos.mpr (by omega))


/-- The bit at a physical cherry says that its left leaf is beta. -/
def terminalBit (t : Labelled) (p : Address) : Bool := isBeta t (p ++ [false])

private def SameBits (t w : Labelled) : Prop :=
  ∀ p, atTree (shape t) p = some cherry → terminalBit t p = terminalBit w p

private theorem branch_bits_split {l r l' r' : Labelled}
    (h : SameBits (.mul l r) (.mul l' r')) : SameBits l l' ∧ SameBits r r' := by
  constructor
  · intro p hp
    exact h (false :: p) hp
  · intro p hp
    exact h (true :: p) hp

private theorem shape_children {l r l' r' : Labelled}
    (h : shape (.mul l r) = shape (.mul l' r')) : shape l = shape l' ∧ shape r = shape r' := by
  have he : (shape l, shape r) = (shape l', shape r') := branchEmbedding.injective h
  exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

private theorem adjacent_shape_ne {n : Nat} {l r : Labelled}
    (hl : Rank (n + 1) l) (hr : Rank n r) (hn : 1 ≤ n) : shape l ≠ shape r := by
  intro h
  have he := congrArg leaves h
  rw [leaves_shape, leaves_shape, rank_leaves hl, rank_leaves hr] at he
  exact (ne_of_gt (fib_successor_lt n hn)) he

private theorem rank_bits_unique {n : Nat} {t u : Labelled} (ht : Rank n t) (hu : Rank n u)
    (hs : shape t = shape u) (hb : SameBits t u) : t = u := by
  induction ht generalizing u with
  | zero => cases hu; rfl
  | one => cases hu; rfl
  | @straight n l r hl hr il ir =>
    cases hu with
    | straight hl' hr' =>
      obtain ⟨hlS, hrS⟩ := shape_children hs
      obtain ⟨hlB, hrB⟩ := branch_bits_split hb
      exact congrArg₂ FreeMagma.mul (il hl' hlS hlB) (ir hr' hrS hrB)
    | crossed hl' hr' =>
      cases n with
      | zero =>
        cases hl; cases hr; cases hl'; cases hr'
        have bad := hb [] rfl
        cases bad
      | succ n =>
        exact False.elim (adjacent_shape_ne hl hr' (by omega) (shape_children hs).1)
  | @crossed n l r hl hr il ir =>
    cases hu with
    | crossed hl' hr' =>
      obtain ⟨hrS, hlS⟩ := shape_children hs
      obtain ⟨hrB, hlB⟩ := branch_bits_split hb
      exact congrArg₂ FreeMagma.mul (ir hr' hrS hrB) (il hl' hlS hlB)
    | straight hl' hr' =>
      cases n with
      | zero =>
        cases hl; cases hr; cases hl'; cases hr'
        have bad := hb [] rfl
        cases bad
      | succ n =>
        exact False.elim (adjacent_shape_ne hl hr' (by omega) (shape_children hs).2)


private theorem cherry_lookup_only_root (p : Address)
    (h : atTree cherry p = some cherry) : p = [] := by
  cases p with
  | nil => rfl
  | cons b p => cases b <;> cases p <;> first | cases h | rename_i b p; cases b <;> cases h

private theorem seed_leaf_no_cherry (p : Address) (u : Bool) :
    atTree (shape (.of u)) p ≠ some cherry := by
  cases p with
  | nil => intro h; cases h
  | cons b p => cases b <;> intro h <;> cases h

private theorem terminal_orientation_exists (B : Address → Bool) :
    ∃ u, Rank 2 u ∧ shape u = cherry ∧
      ∀ p, atTree cherry p = some cherry → terminalBit u p = B p := by
  cases he : B [] with
  | false =>
    refine ⟨.mul alpha beta, .crossed .one .zero, rfl, ?_⟩
    intro p hp
    rw [cherry_lookup_only_root p hp, he]
    rfl
  | true =>
    refine ⟨.mul beta alpha, .straight .one .zero, rfl, ?_⟩
    intro p hp
    rw [cherry_lookup_only_root p hp, he]
    rfl

private theorem combine_terminal_assignments {l r l' r' : Labelled} (B : Address → Bool)
    (hrs : shape l' = shape l) (hls : shape r' = shape r)
    (hroot : shape (.mul l r) ≠ cherry)
    (hl : ∀ p, atTree (shape l) p = some cherry → terminalBit l' p = B (false :: p))
    (hr : ∀ p, atTree (shape r) p = some cherry → terminalBit r' p = B (true :: p)) :
    shape (.mul l' r') = shape (.mul l r) ∧ ∀ p,
      atTree (shape (.mul l r)) p = some cherry → terminalBit (.mul l' r') p = B p := by
  constructor
  · exact congrArg₂ FreeMagma.mul hrs hls
  · intro p hp
    cases p with
    | nil => exact False.elim (hroot (Option.some.inj hp))
    | cons b p =>
      cases b
      · exact hl p hp
      · exact hr p hp

private theorem rank_bits_exists {n t} (h : Rank n t) (B : Address → Bool) :
    ∃ u, Rank n u ∧ shape u = shape t ∧
      ∀ p, atTree (shape t) p = some cherry → terminalBit u p = B p := by
  induction h generalizing B with
  | zero => exact ⟨_, .zero, rfl, fun p h => (seed_leaf_no_cherry p true h).elim⟩
  | one => exact ⟨_, .one, rfl, fun p h => (seed_leaf_no_cherry p false h).elim⟩
  | @straight n l r hl hr il ir =>
    cases n with
    | zero =>
      cases hl; cases hr
      exact terminal_orientation_exists B
    | succ n =>
      obtain ⟨l', hl', hls, hlB⟩ := il (fun p => B (false :: p))
      obtain ⟨r', hr', hrs, hrB⟩ := ir (fun p => B (true :: p))
      have root_ne : shape (.mul l r) ≠ cherry := by
        intro hc
        exact not_tip_of_rank hl (shape_children (l':=alpha) (r':=alpha) hc).1
      obtain ⟨hs, hb⟩ := combine_terminal_assignments B hls hrs root_ne hlB hrB
      exact ⟨_, .straight hl' hr', hs, hb⟩
  | @crossed n l r hl hr il ir =>
    cases n with
    | zero =>
      cases hl; cases hr
      exact terminal_orientation_exists B
    | succ n =>
      obtain ⟨r', hr', hrs, hrB⟩ := ir (fun p => B (false :: p))
      obtain ⟨l', hl', hls, hlB⟩ := il (fun p => B (true :: p))
      have root_ne : shape (.mul r l) ≠ cherry := by
        intro hc
        exact not_tip_of_rank hl (shape_children (l':=alpha) (r':=alpha) hc).2
      obtain ⟨hs, hb⟩ := combine_terminal_assignments B hrs hls root_ne hrB hlB
      exact ⟨_, .crossed hl' hr', hs, hb⟩

/-- All current labelled states in a fixed physical-shape fibre. -/
def currentFiber (n : Nat) (s : Shape) : Finset Labelled :=
  (rankedTrees n).filter (fun t => shape t = s)

/-- Independent indexed bits read from the actual left leaves of the current cherries. -/
def fiberBits (n : Nat) (s : Shape) (t : ↥(currentFiber n s)) :
    ↥(cherries s) → Bool := fun p => terminalBit t.1 p.1

private theorem mem_currentFiber (n : Nat) (s : Shape) (t : Labelled) :
    t ∈ currentFiber n s ↔ Rank n t ∧ shape t = s := by
  rw [currentFiber, Finset.mem_filter, mem_rankedTrees_iff]

private theorem fiber_bits_bijective {n : Nat} {s : Shape} (hs : s ∈ rankedShapes n) :
    Function.Bijective (fiberBits n s) := by
  constructor
  · intro t u h
    obtain ⟨ht, hts⟩ := (mem_currentFiber n s t.1).mp t.2
    obtain ⟨hu, hus⟩ := (mem_currentFiber n s u.1).mp u.2
    apply Subtype.ext
    refine rank_bits_unique ht hu (hts.trans hus.symm) ?_
    intro p hp
    have hc : p ∈ cherries s := (mem_cherries s p).mpr (hts ▸ hp)
    exact congrFun h ⟨p, hc⟩
  · intro B
    obtain ⟨u, hu, hus⟩ := (mem_rankedShapes_iff n s).mp hs
    let full : Address → Bool := fun p => if h : p ∈ cherries s then B ⟨p, h⟩ else false
    obtain ⟨v, hv, hvs, hB⟩ := rank_bits_exists hu full
    refine ⟨⟨v, (mem_currentFiber n s v).mpr ⟨hv, hvs.trans hus⟩⟩, ?_⟩
    funext p
    have ht := hB p.1 (hus.symm ▸ (mem_cherries s p.1).mp p.2)
    exact ht.trans (dite_eq_left p.2)

private theorem current_fiber_card {n : Nat} {s : Shape} (hs : s ∈ rankedShapes n) :
    (currentFiber n s).card = 2 ^ (cherries s).card := by
  classical
  simpa [Fintype.card_pi_const] using
    Fintype.card_congr (Equiv.ofBijective (fiberBits n s) (fiber_bits_bijective hs))

/-- The whole next response map, computed without making any new birth choices. -/
def nextPresence (t : Labelled) (p : Address) : Bool :=
  present t p || (!p.isEmpty && isBeta t p.dropLast)

private theorem next_presence_set (t : Labelled) (p : Address) :
    nextPresence t p = true ↔ present t p = true ∨
      ∃ q : Address, ∃ b : Bool, isBeta t q = true ∧ p = q ++ [b] := by
  simp only [nextPresence, Bool.or_eq_true, Bool.and_eq_true]
  refine or_congr Iff.rfl ?_
  constructor
  · rintro ⟨he, h⟩
    have hp : p ≠ [] := by rintro rfl; contradiction
    exact ⟨p.dropLast, p.getLast hp, h, (List.dropLast_concat_getLast hp).symm⟩
  · rintro ⟨q, b, h, rfl⟩
    simpa using h

private theorem next_presence_update (t w : Labelled) (h : Step t w) (p : Address) :
    nextPresence t p = present w p :=
  Bool.eq_iff_iff.mpr ((next_presence_set t p).trans (step_present t w h p).symm)

private theorem step_exists (t : Labelled) : ∃ w, Step t w := by
  induction t with
  | of b => cases b
            · exact ⟨_, .betaLeft⟩
            · exact ⟨_, .alphaToBeta⟩
  | mul a b ha hb =>
    obtain ⟨_, sa⟩ := ha
    obtain ⟨_, sb⟩ := hb
    exact ⟨_, .branch sa sb⟩

private theorem terminal_next (t : Labelled) (p : Address)
    (h : atTree (shape t) p = some cherry) :
    nextPresence t (p ++ [false, false]) = terminalBit t p := by
  obtain ⟨w, hw⟩ := step_exists t
  exact (next_presence_update t w hw _).trans (cherry_step_bit t w hw p h)

private theorem fiber_next_injective {n : Nat} {s : Shape} (hs : s ∈ rankedShapes n) :
    Function.Injective (fun t : ↥(currentFiber n s) => nextPresence t.1) := by
  intro t u h
  apply (fiber_bits_bijective hs).1
  funext p
  have htc : atTree (shape t.1) p.1 = some cherry :=
    ((mem_currentFiber n s t.1).mp t.2).2.symm ▸ (mem_cherries s p.1).mp p.2
  have huc : atTree (shape u.1) p.1 = some cherry :=
    ((mem_currentFiber n s u.1).mp u.2).2.symm ▸ (mem_cherries s p.1).mp p.2
  exact (terminal_next t.1 p.1 htc).symm.trans
    ((congrFun h (p.1 ++ [false, false])).trans (terminal_next u.1 p.1 huc))

/-- The actual known-alpha current fibres, all four finite counts, and the exact
one-step prediction on every physical word, including a word that is absent. -/
theorem exact_known_seed_fibres (n : Nat) (s : Shape) (_hn : 2 ≤ n)
    (hs : s ∈ rankedShapes n) :
    (∀ t, t ∈ rankedTrees n ↔ After n t) ∧
    (∀ u, u ∈ rankedShapes n ↔ ∃ t, After n t ∧ shape t = u) ∧
    (∀ t, t ∈ currentFiber n s ↔ After n t ∧ shape t = s) ∧
    (∀ p, p ∈ cherries s ↔ atTree s p = some cherry) ∧
    Function.Bijective (fiberBits n s) ∧
    (cherries s).card = Nat.fib (n - 1) ∧
    (currentFiber n s).card = 2 ^ Nat.fib (n - 1) ∧
    (rankedShapes n).card = 2 ^ (Nat.fib n - 1) ∧
    (rankedTrees n).card = 2 ^ (Nat.fib (n + 1) - 1) ∧
    (∀ t w p, t ∈ currentFiber n s → Step t w → nextPresence t p = present w p) ∧
    (∀ t p, t ∈ currentFiber n s → (nextPresence t p = true ↔ present s p = true ∨
        ∃ q : Address, ∃ b : Bool, isBeta t q = true ∧ p = q ++ [b])) ∧
    (∀ (t : ↥(currentFiber n s)) (p : ↥(cherries s)),
      nextPresence t.1 (p.1 ++ [false, false]) = fiberBits n s t p) ∧
    Function.Injective (fun t : ↥(currentFiber n s) => nextPresence t.1) := by
  obtain ⟨u, hu, hus⟩ := (mem_rankedShapes_iff n s).mp hs
  have hC : (cherries s).card = Nat.fib (n - 1) := hus ▸ rank_cherries hu
  refine ⟨?_, ?_, ?_, mem_cherries s, fiber_bits_bijective hs, hC, ?_, card_rankedShapes n,
    card_rankedTrees n, ?_, ?_, ?_, fiber_next_injective hs⟩
  · intro t
    exact (mem_rankedTrees_iff n t).trans (rank_iff_after n t)
  · intro v
    rw [mem_rankedShapes_iff]
    exact exists_congr (fun t => and_congr_left' (rank_iff_after n t))
  · intro t
    rw [mem_currentFiber, rank_iff_after]
  · rw [current_fiber_card hs, hC]
  · intro t w p _ ht
    exact next_presence_update t w ht p
  · intro t p ht
    rw [← ((mem_currentFiber n s t).mp ht).2, present_shape]
    exact next_presence_set t p
  · intro t p
    apply terminal_next
    exact ((mem_currentFiber n s t.1).mp t.2).2.symm ▸ (mem_cherries s p.1).mp p.2

#print axioms exact_known_seed_fibres

end D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers
