/- GID: D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Noncrossing refinement has more atoms than Tamari order from rank three. -/

import D5.S3.Combinatorics.Lattices.Tamari.MaximumFamilies
import Mathlib.Order.Partition.Finpartition

set_option autoImplicit false

/-! # Noncrossing refinement and its comparison with Tamari order -/

namespace D5.S3.Combinatorics.Lattices.Tamari

open Finset

noncomputable section

variable {n : ℕ}

abbrev Partitions (n : ℕ) := Finpartition (univ : Finset (Fin n))

/-- Two elements are in the same block of the partition. -/
def Shares (P : Partitions n) (x y : Fin n) : Prop := y ∈ P.part x

private theorem shares_refl (P : Partitions n) (x : Fin n) : Shares P x x :=
  P.mem_part (mem_univ x)

private theorem shares_iff_part_eq {P : Partitions n} {x y : Fin n} :
    Shares P x y ↔ P.part y = P.part x :=
  P.mem_part_iff_part_eq_part (mem_univ y) (mem_univ x)

private theorem shares_symm {P : Partitions n} {x y : Fin n} (h : Shares P x y) :
    Shares P y x := shares_iff_part_eq.mpr (shares_iff_part_eq.mp h).symm

private theorem partition_le_iff {P Q : Partitions n} :
    P ≤ Q ↔ ∀ x y, Shares P x y → Shares Q x y := by
  constructor
  · intro h x y hy
    obtain ⟨q, hq, hsub⟩ := h (P.part_mem.mpr (mem_univ x))
    have hq' := Q.part_eq_of_mem hq (hsub (P.mem_part (mem_univ x)))
    change y ∈ Q.part x
    rw [hq']
    exact hsub hy
  · intro h p hp
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hp
    refine ⟨Q.part x, Q.part_mem.mpr (mem_univ x), ?_⟩
    intro y hy
    apply h x y
    change y ∈ P.part x
    rwa [P.part_eq_of_mem hp hx]

/-- The source excludes four interleaving points in two distinct blocks. -/
def IsNoncrossing (P : Partitions n) : Prop :=
  ¬ ∃ a b c d : Fin n, a < b ∧ b < c ∧ c < d ∧
    Shares P a c ∧ Shares P b d ∧ ¬ Shares P a b

/-- Noncrossing partitions of the ordered set with `n` points, in refinement order. -/
abbrev NoncrossingPartitions (n : ℕ) := {P : Partitions n // IsNoncrossing P}

private theorem shares_bottom {x y : Fin n} : Shares (⊥ : Partitions n) x y ↔ x = y := by
  constructor
  · intro h
    obtain ⟨z, _, hz⟩ := Finpartition.mem_bot_iff.mp
      ((⊥ : Partitions n).part_mem.mpr (mem_univ x))
    have hx := shares_refl (⊥ : Partitions n) x
    change x ∈ (⊥ : Partitions n).part x at hx
    change y ∈ (⊥ : Partitions n).part x at h
    rw [← hz, mem_singleton] at hx h
    exact hx.trans h.symm
  · rintro rfl
    exact shares_refl _ _

private theorem shares_top (x y : Fin n) : Shares (⊤ : Partitions n) x y := by
  have h := Finpartition.parts_top_subset (univ : Finset (Fin n))
    ((⊤ : Partitions n).part_mem.mpr (mem_univ x))
  change y ∈ (⊤ : Partitions n).part x
  rw [mem_singleton.mp h]
  exact mem_univ y

instance ncOrderBot (n : ℕ) : OrderBot (NoncrossingPartitions n) where
  bot := ⟨⊥, by
    rintro ⟨a, b, c, _, hab, hbc, _, hac, _⟩
    exact (hab.trans hbc).ne (shares_bottom.mp hac)⟩
  bot_le _ := show (⊥ : Partitions n) ≤ _ from bot_le

instance ncOrderTop (n : ℕ) : OrderTop (NoncrossingPartitions n) where
  top := ⟨⊤, by
    rintro ⟨a, b, _, _, _, _, _, _, _, h⟩
    exact h (shares_top a b)⟩
  le_top _ := show _ ≤ (⊤ : Partitions n) from le_top

private theorem has_nonsingleton {P : Partitions n} (hP : P ≠ ⊥) :
    ∃ x y : Fin n, x ≠ y ∧ Shares P x y := by
  by_contra! h
  apply hP
  exact le_antisymm (partition_le_iff.mpr fun x y hxy => shares_bottom.mpr (Classical.byContradiction fun hne => h x y hne hxy)) bot_le

private def pairSetoid (x y : Fin n) : Setoid (Fin n) where
  r a b := a = b ∨ (a = x ∨ a = y) ∧ (b = x ∨ b = y)
  iseqv := ⟨fun _ => Or.inl rfl, by intro a b; tauto, by
    intro a b c hab hbc
    rcases hab with rfl | hab
    · exact hbc
    rcases hbc with rfl | hbc
    · exact Or.inr hab
    exact Or.inr ⟨hab.1, hbc.2⟩⟩

private def pairPartition (x y : Fin n) : Partitions n := by
  classical
  exact Finpartition.ofSetoid (pairSetoid x y)

private theorem shares_pair {x y a b : Fin n} :
    Shares (pairPartition x y) a b ↔ a = b ∨ (a = x ∨ a = y) ∧ (b = x ∨ b = y) := by
  classical
  exact Finpartition.mem_part_ofSetoid_iff_rel

private theorem pair_ne_bot {x y : Fin n} (hxy : x ≠ y) : pairPartition x y ≠ ⊥ := by
  intro h
  have h' : Shares (pairPartition x y) x y :=
    shares_pair.mpr (Or.inr ⟨Or.inl rfl, Or.inr rfl⟩)
  rw [h] at h'
  exact hxy (shares_bottom.mp h')

private theorem pair_le_of_shares {x y : Fin n} {P : Partitions n} (h : Shares P x y) :
    pairPartition x y ≤ P := by
  apply partition_le_iff.mpr
  intro a b hab
  rcases shares_pair.mp hab with rfl | ⟨rfl | rfl, rfl | rfl⟩
  · exact shares_refl _ _
  · exact shares_refl _ _
  · exact h
  · exact shares_symm h
  · exact shares_refl _ _

private theorem member_pair_eq {a b x y : Fin n} (hne : a ≠ b)
    (ha : a = x ∨ a = y) (hb : b = x ∨ b = y) :
    (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · contradiction
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · contradiction

private theorem noncrossing_pair (x y : Fin n) : IsNoncrossing (pairPartition x y) := by
  rintro ⟨a, b, c, d, hab, hbc, hcd, hac, hbd, _⟩
  have h₁ := (shares_pair.mp hac).resolve_left (hab.trans hbc).ne
  have h₂ := (shares_pair.mp hbd).resolve_left (hbc.trans hcd).ne
  rcases member_pair_eq (hab.trans hbc).ne h₁.1 h₁.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h₂.1.elim (fun he => hab.ne he.symm) hbc.ne
  · exact h₂.1.elim hbc.ne (fun he => hab.ne he.symm)

private def pairNC (x y : Fin n) : NoncrossingPartitions n :=
  ⟨pairPartition x y, noncrossing_pair x y⟩

private theorem pairNC_isAtom {x y : Fin n} (hxy : x ≠ y) : IsAtom (pairNC x y) := by
  apply isAtom_iff_le_of_ge.mpr
  refine ⟨fun h => pair_ne_bot hxy (congrArg Subtype.val h), ?_⟩
  intro P hP hle
  have hP' : P.val ≠ ⊥ := fun he => hP (Subtype.ext he)
  obtain ⟨a, b, hab, hsh⟩ := has_nonsingleton hP'
  have hp : Shares (pairPartition x y) a b :=
    (partition_le_iff.mp (show P.val ≤ pairPartition x y from hle)) a b hsh
  rcases (shares_pair.mp hp).resolve_left hab with ⟨ha, hb⟩
  rcases member_pair_eq hab ha hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact pair_le_of_shares hsh
  · exact pair_le_of_shares (shares_symm hsh)

private theorem pairNC_eq_only {x y a b : Fin n} (hxy : x ≠ y) (h : pairNC x y = pairNC a b) :
    (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  have hbase : Shares (pairPartition x y) x y :=
    shares_pair.mpr (Or.inr ⟨Or.inl rfl, Or.inr rfl⟩)
  have he : pairPartition x y = pairPartition a b := congrArg Subtype.val h
  have hh : Shares (pairPartition a b) x y := he ▸ hbase
  obtain ⟨ha, hb⟩ := (shares_pair.mp hh).resolve_left hxy
  exact member_pair_eq hxy ha hb

/-- For `n ≥ 3` there are at least `n` atoms. Use the star at point zero and one extra pair. -/
private theorem nc_atom_card_ge (n : ℕ) (hn : 3 ≤ n) :
    n ≤ Nat.card {P : NoncrossingPartitions n // IsAtom P} := by
  let x : Fin n := ⟨0, by omega⟩
  let y : Fin n := ⟨1, by omega⟩
  let z : Fin n := ⟨2, by omega⟩
  have hxy : x ≠ y := by intro h; have := congrArg Fin.val h; change 0 = 1 at this; omega
  have hxz : x ≠ z := by intro h; have := congrArg Fin.val h; change 0 = 2 at this; omega
  have hyz : y ≠ z := by intro h; have := congrArg Fin.val h; change 1 = 2 at this; omega
  let f (i : Fin n) : {P : NoncrossingPartitions n // IsAtom P} :=
    if h : i = x then ⟨pairNC y z, pairNC_isAtom hyz⟩
    else ⟨pairNC x i, pairNC_isAtom (Ne.symm h)⟩
  have f_at (i : Fin n) (hi : i = x) : (f i).val = pairNC y z := by
    unfold f
    rw [dite_eq_left hi]
  have f_else (i : Fin n) (hi : i ≠ x) : (f i).val = pairNC x i := by
    unfold f
    rw [dite_eq_right hi]
  refine (Nat.card_fin n).symm.trans_le (Nat.card_le_card_of_injective f ?_)
  intro i j h
  have he := congrArg Subtype.val h
  by_cases hi : i = x <;> by_cases hj : j = x
  · exact hi.trans hj.symm
  · rw [f_at i hi, f_else j hj] at he
    exact ((pairNC_eq_only (Ne.symm hj) he.symm).elim
      (fun h' => hxy h'.1) (fun h' => hxz h'.1)).elim
  · rw [f_else i hi, f_at j hj] at he
    exact ((pairNC_eq_only (Ne.symm hi) he).elim
      (fun h' => hxy h'.1) (fun h' => hxz h'.1)).elim
  · rw [f_else i hi, f_else j hj] at he
    exact (pairNC_eq_only (Ne.symm hi) he).elim And.right (fun h' => (hj h'.1.symm).elim)

theorem no_tamari_noncrossing_iso (n : ℕ) (hn : 3 ≤ n) :
    ¬ Nonempty (Trees n ≃o NoncrossingPartitions n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rintro ⟨e⟩
  have h₁ := tamari_atom_card_le k
  have h₂ := nc_atom_card_ge (k + 1) hn
  rw [← orderIso_atomCard e] at h₂
  omega

theorem nc_one_subsingleton : Subsingleton (NoncrossingPartitions 1) := by
  refine ⟨fun P Q => Subtype.ext (le_antisymm ?_ ?_)⟩ <;>
    exact partition_le_iff.mpr (fun x y _ => (Subsingleton.elim x y) ▸ shares_refl _ _)

theorem nc_two_bot_or_top (P : NoncrossingPartitions 2) : P = ⊥ ∨ P = ⊤ := by
  by_cases h : P = ⊥
  · exact Or.inl h
  · right
    apply Subtype.ext
    apply le_antisymm le_top
    obtain ⟨x, y, hxy, hs⟩ := has_nonsingleton
      (show P.val ≠ ⊥ from fun he => h (Subtype.ext he))
    apply partition_le_iff.mpr
    intro a b _
    by_cases h' : a = b
    · subst b
      exact shares_refl _ _
    have orient : (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
      fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;> simp_all
    rcases orient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hs
    · exact shares_symm hs

theorem nc_two_bot_ne_top : (⊥ : NoncrossingPartitions 2) ≠ ⊤ := by
  intro h
  have hs := shares_top (n := 2) 0 1
  have hp : (⊥ : Partitions 2) = ⊤ := congrArg Subtype.val h
  rw [← hp] at hs
  exact (by decide : (0 : Fin 2) ≠ 1) (shares_bottom.mp hs)

end

end D5.S3.Combinatorics.Lattices.Tamari
