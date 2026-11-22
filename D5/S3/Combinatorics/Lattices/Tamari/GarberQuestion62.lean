/- GID: D5/S3/Combinatorics/Lattices/Tamari/GarberQuestion62
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Lattices/Tamari/GarberQuestion62
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Maximum Boolean antichains have Tamari order with exact comparison boundaries. -/

/-
admission_basis: open-problem-resolution (#33263; prospective Proved)
Direct frozen dependencies: none.
proof_shape: result: content; escape_witness: maximum_noncrossing_iff
-/

import D5.S3.Combinatorics.Lattices.Tamari.NoncrossingRefinement
import D5.S3.Combinatorics.Lattices.Tamari.DyckHeight

/-!
# Garber et al., Question 6.2, first sentence

Julien Garber, Lina S. Goltermann, Daniel Horiatakis, Dennis König and Tal Gottesman,
*Counting Boolean Antichains* (2026), arXiv:2608.27126v2, §6, Question 6.2, p. 22.
https://arxiv.org/html/2608.27126v2#S6.Thmtheorem2

> Is the order on Boolean antichains of maximal size in the Tamari lattice equivalent to the Tamari
> order, the order on non-crossing partitions, or the order on Dyck paths?
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Lattices.Tamari

noncomputable section

private def finiteTreeEquiv (n : ℕ) : Trees n ≃ ↥(BinaryTree.treesOfNumNodesEq n) where
  toFun t := ⟨t.val, BinaryTree.mem_treesOfNumNodesEq.mpr t.property⟩
  invFun t := ⟨t.val, BinaryTree.mem_treesOfNumNodesEq.mp t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def dyckWordEquiv (n : ℕ) : DyckPaths n ≃ {p : DyckWord // p.semilength = n} where
  toFun p := ⟨p.val, p.property⟩
  invFun p := ⟨p.val, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem trees_card (n : ℕ) : Nat.card (Trees n) = catalan n := by
  rw [Nat.card_congr (finiteTreeEquiv n), Nat.card_eq_fintype_card, Fintype.card_coe,
    BinaryTree.treesOfNumNodesEq_card_eq_catalan]

private theorem dyckPaths_card (n : ℕ) : Nat.card (DyckPaths n) = catalan n := by
  rw [Nat.card_congr (dyckWordEquiv n), Nat.card_eq_fintype_card,
    DyckWord.card_dyckWord_semilength_eq_catalan]

private def onePointIso {α β : Type*} [Preorder α] [Preorder β] [Subsingleton α] [Subsingleton β]
    (a : α) (b : β) : α ≃o β where
  toEquiv :=
    { toFun := fun _ => b
      invFun := fun _ => a
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }
  map_rel_iff' := by
    intro x y
    have h : x = y := Subsingleton.elim _ _
    subst y
    exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩

private def twoPointMap {α : Type*} (a b : α) (i : Fin 2) : α :=
  if i = 0 then a else b

private theorem twoPointMap_injective {α : Type*} {a b : α} (hne : a ≠ b) :
    Function.Injective (twoPointMap a b) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [twoPointMap, hne, Ne.symm hne]

private def twoPointIso {α : Type*} [PartialOrder α] (a b : α) (hle : a ≤ b) (hne : a ≠ b)
    (hsurj : Function.Surjective (twoPointMap a b)) : Fin 2 ≃o α where
  toEquiv := Equiv.ofBijective _ ⟨twoPointMap_injective hne, hsurj⟩
  map_rel_iff' := by
    intro i j
    change twoPointMap a b i ≤ twoPointMap a b j ↔ i ≤ j
    have hnot : ¬ b ≤ a := fun h => hne (le_antisymm hle h)
    fin_cases i <;> fin_cases j <;> simp [twoPointMap, hle, hnot]

private theorem twoPointMap_surj_of_card {α : Type*} [Finite α] {a b : α}
    (hne : a ≠ b) (hc : Nat.card α = 2) : Function.Surjective (twoPointMap a b) :=
  ((twoPointMap_injective hne).bijective_of_nat_card_le
    (le_of_eq (hc.trans (Nat.card_fin 2).symm))).2

private def tamariTwo : Fin 2 ≃o Trees 2 := by
  have hcard := (trees_card 2).trans catalan_two
  let _ : Finite (Trees 2) := Finite.of_equiv _ (finiteTreeEquiv 2).symm
  have hne : (⊥ : Trees 2) ≠ ⊤ := by
    intro h
    let _ : Subsingleton (Trees 2) := ⟨fun a b => by
      have hap : a = ⊥ := le_antisymm (h.symm ▸ le_top) bot_le
      have hbp : b = ⊥ := le_antisymm (h.symm ▸ le_top) bot_le
      exact hap.trans hbp.symm⟩
    have h' := Nat.card_of_subsingleton (⊥ : Trees 2)
    omega
  exact twoPointIso ⊥ ⊤ bot_le hne (twoPointMap_surj_of_card hne hcard)

private def ncTwo : Fin 2 ≃o NoncrossingPartitions 2 :=
  twoPointIso ⊥ ⊤ bot_le nc_two_bot_ne_top (fun P => by
    rcases nc_two_bot_or_top P with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩)

private def dyckTwo : Fin 2 ≃o DyckPaths 2 := by
  let _ : Finite (DyckPaths 2) := Finite.of_equiv _ (dyckWordEquiv 2).symm
  exact twoPointIso (nearMountain 0) ⊤ le_top (near_ne_top 0)
    (twoPointMap_surj_of_card (near_ne_top 0) ((dyckPaths_card 2).trans catalan_two))

private def tamariNcOne : Trees 1 ≃o NoncrossingPartitions 1 := by
  let _ : Subsingleton (Trees 1) := (Nat.card_eq_one_iff_unique.mp
    ((trees_card 1).trans catalan_one)).1
  let _ : Subsingleton (NoncrossingPartitions 1) := nc_one_subsingleton
  exact onePointIso ⊤ ⊤

private def tamariDyckOne : Trees 1 ≃o DyckPaths 1 := by
  let _ : Subsingleton (Trees 1) := (Nat.card_eq_one_iff_unique.mp
    ((trees_card 1).trans catalan_one)).1
  let _ : Subsingleton (DyckPaths 1) := (Nat.card_eq_one_iff_unique.mp
    ((dyckPaths_card 1).trans catalan_one)).1
  exact onePointIso ⊤ ⊤

/-- Dyck paths equipped with the transported Tamari order, via the fixed-size
tree equivalence in Mathlib. -/
@[ext] structure TamariDyckPaths (n : ℕ) where
  path : DyckPaths n

private def dyckTreeEquiv (n : ℕ) : TamariDyckPaths n ≃ Trees n :=
  ({ toFun := TamariDyckPaths.path
     invFun := TamariDyckPaths.mk
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl } : TamariDyckPaths n ≃ DyckPaths n).trans
    ((dyckWordEquiv n).trans ((DyckWord.equivTreesOfNumNodesEq n).trans (finiteTreeEquiv n).symm))

instance tamariDyckOrder (n : ℕ) : PartialOrder (TamariDyckPaths n) :=
  PartialOrder.lift (dyckTreeEquiv n) (dyckTreeEquiv n).injective

private def tamariDyckIso (n : ℕ) : Trees n ≃o TamariDyckPaths n :=
  (show TamariDyckPaths n ≃o Trees n from
    { toEquiv := dyckTreeEquiv n, map_rel_iff' := Iff.rfl }).symm

private theorem maximum_noncrossing_iff (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (MaximumFamilies (Trees (n + 1)) n ≃o NoncrossingPartitions n) ↔ n ≤ 2 := by
  constructor
  · rintro ⟨e⟩
    by_contra! h
    exact no_tamari_noncrossing_iso n h ⟨(maximumTamariOrderIso n).symm.trans e⟩
  · intro h
    have cases : n = 1 ∨ n = 2 := by omega
    rcases cases with rfl | rfl
    · exact ⟨(maximumTamariOrderIso 1).trans tamariNcOne⟩
    · exact ⟨(maximumTamariOrderIso 2).trans (tamariTwo.symm.trans ncTwo)⟩

private theorem maximum_dyck_height_iff (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (MaximumFamilies (Trees (n + 1)) n ≃o DyckPaths n) ↔ n ≤ 2 := by
  constructor
  · rintro ⟨e⟩
    by_contra! h
    exact no_tamari_dyck_height_iso n h ⟨(maximumTamariOrderIso n).symm.trans e⟩
  · intro h
    have cases : n = 1 ∨ n = 2 := by omega
    rcases cases with rfl | rfl
    · exact ⟨(maximumTamariOrderIso 1).trans tamariDyckOne⟩
    · exact ⟨(maximumTamariOrderIso 2).trans (tamariTwo.symm.trans dyckTwo)⟩

/-- Garber et al., Question 6.2, first sentence, with the registered comparison orders. -/
theorem result (n : ℕ) (hn : 1 ≤ n) :
    IsGreatest {k : ℕ | ∃ C : Set (Trees (n + 1)), IsBooleanFamily C ∧ C.ncard = k} n ∧
    Nonempty (MaximumFamilies (Trees (n + 1)) n ≃o Trees n) ∧
    (Nonempty (MaximumFamilies (Trees (n + 1)) n ≃o NoncrossingPartitions n) ↔ n ≤ 2) ∧
    (Nonempty (MaximumFamilies (Trees (n + 1)) n ≃o DyckPaths n) ↔ n ≤ 2) ∧
    Nonempty (MaximumFamilies (Trees (n + 1)) n ≃o TamariDyckPaths n) :=
  ⟨maximumTamari_card n, ⟨maximumTamariOrderIso n⟩, maximum_noncrossing_iff n hn,
    maximum_dyck_height_iff n hn, ⟨(maximumTamariOrderIso n).trans (tamariDyckIso n)⟩⟩

end

end D5.S3.Combinatorics.Lattices.Tamari
