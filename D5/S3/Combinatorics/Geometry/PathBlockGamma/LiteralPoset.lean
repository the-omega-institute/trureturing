/- GID: D5/S3/Combinatorics/Geometry/PathBlockGamma/LiteralPoset
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/PathBlockGamma/LiteralPoset
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Preorder.Chain]
   utility: none
   digest: The alternating path of chain blocks is a finite naturally labelled graded poset. -/

import Mathlib.Order.Preorder.Chain
import Mathlib.Data.Set.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.PathBlockGamma

/-- A literal point of one of the `m` blocks, at one of its `a` levels. -/
@[ext] structure Vertex (a m : ℕ) where
  block : Fin m
  level : Fin a
  deriving DecidableEq, Fintype

abbrev oddBlock {m : ℕ} (i : Fin m) : Prop := i.val % 2 = 0

def adjacentBlocks {m : ℕ} (i j : Fin m) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

/-- Each block is a chain; an odd one-based block lies below both adjacent even blocks. -/
def pathLE {a m : ℕ} (x y : Vertex a m) : Prop :=
  (x.block = y.block ∧ x.level ≤ y.level) ∨
    (oddBlock x.block ∧ ¬ oddBlock y.block ∧ adjacentBlocks x.block y.block)

instance {a m : ℕ} : LE (Vertex a m) := ⟨pathLE⟩

instance {a m : ℕ} : PartialOrder (Vertex a m) where
  le_refl x := Or.inl ⟨rfl, le_rfl⟩
  le_trans x y z hxy hyz := by
    rcases hxy with hsame | hcross
    · rcases hyz with hsame' | hcross'
      · left
        exact ⟨hsame.1.trans hsame'.1, hsame.2.trans hsame'.2⟩
      · right
        exact ⟨hsame.1 ▸ hcross'.1, hcross'.2.1,
          hsame.1 ▸ hcross'.2.2⟩
    · rcases hyz with hsame | hcross'
      · right
        exact ⟨hcross.1, hsame.1 ▸ hcross.2.1,
          hsame.1 ▸ hcross.2.2⟩
      · exact False.elim (hcross.2.1 hcross'.1)
  le_antisymm x y hxy hyx := by
    rcases hxy with hsame | hcross
    · rcases hyx with hsame' | hcross'
      · apply Vertex.ext hsame.1
        exact le_antisymm hsame.2 hsame'.2
      · rw [hsame.1] at hcross'
        exact False.elim (hcross'.2.1 hcross'.1)
    · rcases hyx with hsame | hcross'
      · rw [hsame.1] at hcross
        exact False.elim (hcross.2.1 hcross.1)
      · exact False.elim (hcross.2.1 hcross'.1)

def oddBlockCount (m : ℕ) : ℕ := (m + 1) / 2

/-- Zero-based: odd one-based blocks first, then even blocks, increasing inside each class. -/
def blockLabel {m : ℕ} (i : Fin m) : ℕ :=
  if oddBlock i then i.val / 2 else oddBlockCount m + i.val / 2

def naturalLabel {a m : ℕ} (x : Vertex a m) : ℕ :=
  blockLabel x.block * a + x.level.val

def adjacentPair {a m : ℕ} (i : Fin (m - 1)) : Set (Vertex a m) :=
  {x | x.block.val = i.val ∨ x.block.val = i.val + 1}

/-- The finite carrier, odd-blocks-first labelling, and literal order are derived from indices. -/
theorem literal_poset_card_label_order (a m : ℕ) (ha : 0 < a) :
    Fintype.card (Vertex a m) = a * m ∧
      (∀ x : Vertex a m, naturalLabel x < a * m) ∧
      Function.Injective (naturalLabel : Vertex a m → ℕ) ∧
      (∀ ⦃x y : Vertex a m⦄, x < y → naturalLabel x < naturalLabel y) := by
  classical
  constructor
  · let e : Vertex a m ≃ Fin m × Fin a :=
      { toFun := fun x => (x.block, x.level)
        invFun := fun x => ⟨x.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_prod]
    simp [Nat.mul_comm]
  constructor
  · intro x
    have hblock : blockLabel x.block < m := by
      simp only [blockLabel, oddBlock, oddBlockCount]
      split_ifs with hx
      · exact lt_of_le_of_lt (Nat.div_le_self x.block.val 2) x.block.isLt
      · have hxmod := Nat.mod_lt x.block.val (by omega : 0 < 2)
        have hxdiv := Nat.div_add_mod x.block.val 2
        have hmdiv := Nat.div_add_mod (m + 1) 2
        have hmmod := Nat.mod_lt (m + 1) (by omega : 0 < 2)
        omega
    calc
      naturalLabel x < blockLabel x.block * a + a :=
        Nat.add_lt_add_left x.level.isLt _
      _ = (blockLabel x.block + 1) * a := by simp [Nat.add_mul]
      _ ≤ m * a := Nat.mul_le_mul_right a (Nat.succ_le_iff.mpr hblock)
      _ = a * m := Nat.mul_comm _ _
  constructor
  · intro x y hxy
    have hblock : blockLabel x.block = blockLabel y.block := by
      have h := congrArg (fun n => n / a) hxy
      have hxq : naturalLabel x / a = blockLabel x.block := by
        simp [naturalLabel, Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ ha,
          Nat.div_eq_of_lt x.level.isLt]
      have hyq : naturalLabel y / a = blockLabel y.block := by
        simp [naturalLabel, Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ ha,
          Nat.div_eq_of_lt y.level.isLt]
      exact hxq.symm.trans (h.trans hyq)
    have hlevel : x.level.val = y.level.val := by
      have h := congrArg (fun n => n % a) hxy
      simpa [naturalLabel, Nat.add_comm, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt x.level.isLt, Nat.mod_eq_of_lt y.level.isLt] using h
    have hblockIndex : x.block.val = y.block.val := by
      simp only [blockLabel, oddBlock, oddBlockCount] at hblock
      by_cases hx : x.block.val % 2 = 0 <;>
        by_cases hy : y.block.val % 2 = 0 <;> simp [hx, hy] at hblock
      all_goals
        have hxmod := Nat.mod_lt x.block.val (by omega : 0 < 2)
        have hymod := Nat.mod_lt y.block.val (by omega : 0 < 2)
        have hxdiv := Nat.div_add_mod x.block.val 2
        have hydiv := Nat.div_add_mod y.block.val 2
        have hmdiv := Nat.div_add_mod (m + 1) 2
        have hmmod := Nat.mod_lt (m + 1) (by omega : 0 < 2)
        omega
    exact Vertex.ext (Fin.ext hblockIndex) (Fin.ext hlevel)
  · intro x y hxy
    have hle : x ≤ y := hxy.le
    have hne : x ≠ y := hxy.ne
    rcases hle with hsame | hcross
    · simp only [naturalLabel]
      have hlevel : x.level.val < y.level.val := by
        have : x.level ≠ y.level := by
          intro h
          apply hne
          exact Vertex.ext hsame.1 h
        exact lt_of_le_of_ne (show x.level.val ≤ y.level.val from hsame.2)
          (fun h => this (Fin.ext h))
      rw [hsame.1]
      exact Nat.add_lt_add_left hlevel _
    · have hblock : blockLabel x.block < blockLabel y.block := by
        simp only [blockLabel, oddBlock, oddBlockCount]
        simp [hcross.1, hcross.2.1]
        have hxmod := Nat.mod_lt x.block.val (by omega : 0 < 2)
        have hxdiv := Nat.div_add_mod x.block.val 2
        have hmdiv := Nat.div_add_mod (m + 1) 2
        have hmmod := Nat.mod_lt (m + 1) (by omega : 0 < 2)
        omega
      calc
        naturalLabel x < blockLabel x.block * a + a :=
          Nat.add_lt_add_left x.level.isLt _
        _ = (blockLabel x.block + 1) * a := by simp [Nat.add_mul]
        _ ≤ blockLabel y.block * a :=
          Nat.mul_le_mul_right a (Nat.succ_le_iff.mpr hblock)
        _ ≤ naturalLabel y := Nat.le_add_right _ _

/-- Maximal chains are exactly full adjacent pairs, hence have `2 * a` elements and rank
`2 * a - 1`. -/
theorem literal_poset_maximal_chains (a m : ℕ) (ha : 0 < a) (hm : 1 < m) :
    (∀ c : Set (Vertex a m),
      IsMaxChain (· ≤ ·) c ↔ ∃ i : Fin (m - 1), c = adjacentPair i) ∧
    (∀ c : Set (Vertex a m), IsMaxChain (· ≤ ·) c →
      c.ncard = 2 * a ∧ c.ncard - 1 = 2 * a - 1) := by
  classical
  have comparable_blocks {x y : Vertex a m} (h : x ≤ y ∨ y ≤ x) :
      x.block.val = y.block.val ∨ x.block.val + 1 = y.block.val ∨
        y.block.val + 1 = x.block.val := by
    rcases h with hxy | hyx
    · rcases hxy with hsame | hcross
      · exact Or.inl (congrArg Fin.val hsame.1)
      · exact Or.inr hcross.2.2
    · rcases hyx with hsame | hcross
      · exact Or.inl (congrArg Fin.val hsame.1).symm
      · rcases hcross.2.2 with h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
  have pair_chain (i : Fin (m - 1)) :
      IsChain (fun x y : Vertex a m => x ≤ y) (adjacentPair (a := a) i) := by
    intro x hx y hy hxy
    change x.block.val = i.val ∨ x.block.val = i.val + 1 at hx
    change y.block.val = i.val ∨ y.block.val = i.val + 1 at hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · have hb : x.block = y.block := Fin.ext (hx.trans hy.symm)
      rcases le_total x.level y.level with h | h
      · exact Or.inl (Or.inl ⟨hb, h⟩)
      · exact Or.inr (Or.inl ⟨hb.symm, h⟩)
    · have himod := Nat.mod_lt i.val (by omega : 0 < 2)
      by_cases hi : i.val % 2 = 0
      · left
        right
        exact ⟨by simpa [oddBlock, hx] using hi,
          by simp [oddBlock, hy]; omega,
          by left; omega⟩
      · right
        right
        refine ⟨?_, ?_, ?_⟩
        · simp only [oddBlock, hy]
          omega
        · simpa [oddBlock, hx] using hi
        · right
          omega
    · have himod := Nat.mod_lt i.val (by omega : 0 < 2)
      by_cases hi : i.val % 2 = 0
      · right
        right
        exact ⟨by simpa [oddBlock, hy] using hi,
          by simp [oddBlock, hx]; omega,
          by left; omega⟩
      · left
        right
        refine ⟨?_, ?_, ?_⟩
        · simp only [oddBlock, hx]
          omega
        · simpa [oddBlock, hy] using hi
        · right
          omega
    · have hb : x.block = y.block := Fin.ext (hx.trans hy.symm)
      rcases le_total x.level y.level with h | h
      · exact Or.inl (Or.inl ⟨hb, h⟩)
      · exact Or.inr (Or.inl ⟨hb.symm, h⟩)
  have chain_contained (c : Set (Vertex a m)) (hc : IsChain (· ≤ ·) c) :
      ∃ i : Fin (m - 1), c ⊆ adjacentPair i := by
    by_cases hcne : c.Nonempty
    · obtain ⟨x, hx⟩ := hcne
      by_cases hleft : ∃ z ∈ c, z.block.val + 1 = x.block.val
      · obtain ⟨z, hz, hzleft⟩ := hleft
        let i : Fin (m - 1) := ⟨x.block.val - 1, by omega⟩
        refine ⟨i, ?_⟩
        intro y hy
        have hxy := comparable_blocks (hc.total hx hy)
        have hzy := comparable_blocks (hc.total hz hy)
        change y.block.val = i.val ∨ y.block.val = i.val + 1
        dsimp [i]
        omega
      · by_cases hright : x.block.val + 1 < m
        · let i : Fin (m - 1) := ⟨x.block.val, by omega⟩
          refine ⟨i, ?_⟩
          intro y hy
          have hxy := comparable_blocks (hc.total hx hy)
          change y.block.val = i.val ∨ y.block.val = i.val + 1
          dsimp [i]
          by_contra h
          push Not at h
          have : y.block.val + 1 = x.block.val := by omega
          exact hleft ⟨y, hy, this⟩
        · let i : Fin (m - 1) := ⟨m - 2, by omega⟩
          refine ⟨i, ?_⟩
          intro y hy
          have hxy := comparable_blocks (hc.total hx hy)
          change y.block.val = i.val ∨ y.block.val = i.val + 1
          dsimp [i]
          by_contra h
          push Not at h
          have : y.block.val + 1 = x.block.val := by omega
          exact hleft ⟨y, hy, this⟩
    · let i : Fin (m - 1) := ⟨0, by omega⟩
      refine ⟨i, ?_⟩
      simpa [Set.not_nonempty_iff_eq_empty.mp hcne]
  have pair_max (i : Fin (m - 1)) :
      IsMaxChain (fun x y : Vertex a m => x ≤ y) (adjacentPair (a := a) i) := by
    refine ⟨pair_chain i, ?_⟩
    intro c hc hsub
    obtain ⟨j, hj⟩ := chain_contained c hc
    have left_mem : (⟨⟨i.val, by omega⟩, ⟨0, ha⟩⟩ : Vertex a m) ∈ adjacentPair i :=
      Or.inl rfl
    have right_mem : (⟨⟨i.val + 1, by omega⟩, ⟨0, ha⟩⟩ : Vertex a m) ∈ adjacentPair i :=
      Or.inr rfl
    have hleft := hj (hsub left_mem)
    have hright := hj (hsub right_mem)
    change i.val = j.val ∨ i.val = j.val + 1 at hleft
    change i.val + 1 = j.val ∨ i.val + 1 = j.val + 1 at hright
    have hij : i = j := Fin.ext (by omega)
    subst j
    exact Set.Subset.antisymm hsub hj
  have pair_card (i : Fin (m - 1)) : (adjacentPair (a := a) i).ncard = 2 * a := by
    let left : Fin m := ⟨i.val, by omega⟩
    let right : Fin m := ⟨i.val + 1, by omega⟩
    let e : adjacentPair (a := a) i ≃ Sum (Fin a) (Fin a) :=
      { toFun := fun x => if hx : x.1.block.val = i.val then Sum.inl x.1.level
          else Sum.inr x.1.level
        invFun := fun x => match x with
          | Sum.inl k => ⟨⟨left, k⟩, Or.inl rfl⟩
          | Sum.inr k => ⟨⟨right, k⟩, Or.inr rfl⟩
        left_inv := by
          intro x
          apply Subtype.ext
          by_cases hx : x.1.block.val = i.val
          · simp [hx, left]
            exact Vertex.ext (Fin.ext hx.symm) rfl
          · have hxright : x.1.block.val = i.val + 1 := x.2.resolve_left hx
            simp [hx, right]
            exact Vertex.ext (Fin.ext hxright.symm) rfl
        right_inv := by
          intro x
          rcases x with k | k
          · simp [left]
          · simp [right] }
    rw [← Nat.card_coe_set_eq, Nat.card_congr e]
    simp
    omega
  constructor
  · intro c
    constructor
    · intro hc
      obtain ⟨i, hsub⟩ := chain_contained c hc.1
      exact ⟨i, hc.2 (pair_chain i) hsub⟩
    · rintro ⟨i, rfl⟩
      exact pair_max i
  · intro c hc
    obtain ⟨i, rfl⟩ := (show ∃ i, c = adjacentPair i from
      ((show IsMaxChain (· ≤ ·) c ↔ ∃ i, c = adjacentPair i by
        constructor
        · intro h
          obtain ⟨j, hsub⟩ := chain_contained c h.1
          exact ⟨j, h.2 (pair_chain j) hsub⟩
        · rintro ⟨j, rfl⟩
          exact pair_max j).mp hc))
    rw [pair_card]
    omega

end D5.S3.Combinatorics.Geometry.PathBlockGamma
