/- GID: D5/S3/Combinatorics/Partitions/RookLevelSelection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/RookLevelSelection
   mirror-E: none(waiver:nested-full-level-selection)
   anchors: []
   utility: none
   digest: Full rook selections in nested m-cell levels have the falling product count. -/

import D5.S3.Combinatorics.Partitions.RookClassNative

/-! The combination step for a level-total factorization: an upper occupied
    column removes exactly m cells from each lower level. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Partitions.RookLevelSelection
open scoped BigOperators

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The levels are indexed from top to bottom. Every column present above is
    completely filled, with m cells, in every lower level. -/
def NestedFull (m : ℕ) {N : ℕ} (L : Fin N → Finset (C × Fin m)) : Prop :=
  ∀ i j, i < j → ∀ x ∈ L i, ∀ r : Fin m, (x.1,r) ∈ L j

/-- One actual cell in every level, with distinct columns. -/
abbrev Selections (m : ℕ) {N : ℕ} (L : Fin N → Finset (C × Fin m)) :=
  {f : Fin N → C × Fin m // (∀ i, f i ∈ L i) ∧ Function.Injective (fun i => (f i).1)}

private def removeColumn (m N : ℕ) (L : Fin (N+1) → Finset (C × Fin m))
    (x : C × Fin m) (i : Fin N) : Finset (C × Fin m) :=
  L i.succ \ ({x.1} ×ˢ Finset.univ)

private theorem remove_nested (m N : ℕ) (L : Fin (N+1) → Finset (C × Fin m))
    (hL : NestedFull m L) (x : C × Fin m) : NestedFull m (removeColumn m N L x) := by
  intro i j hij y hy r
  obtain ⟨hy,hn⟩ := Finset.mem_sdiff.mp hy
  apply Finset.mem_sdiff.mpr
  refine ⟨hL i.succ j.succ (by simpa using hij) y hy r, ?_⟩
  intro h
  apply hn
  have he : y.1 = x.1 := Finset.mem_singleton.mp (Finset.mem_product.mp h).1
  exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr he,Finset.mem_univ _⟩

private theorem remove_card (m N : ℕ) (L : Fin (N+1) → Finset (C × Fin m))
    (hL : NestedFull m L) (x : ↥(L 0)) (i : Fin N) :
    (removeColumn m N L x.val i).card = (L i.succ).card - m := by
  have hs : {x.val.1} ×ˢ (Finset.univ : Finset (Fin m)) ⊆ L i.succ := by
    intro y hy
    have he := Finset.mem_singleton.mp (Finset.mem_product.mp hy).1
    simpa only [← he] using hL 0 i.succ (by simp) x.val x.property y.2
  rw [removeColumn, Finset.card_sdiff_of_subset hs]
  simp

private def split (m N : ℕ) (L : Fin (N+1) → Finset (C × Fin m)) :
    Selections m L ≃ ((x : ↥(L 0)) × Selections m (removeColumn m N L x.val)) where
  toFun f := ⟨⟨f.val 0,f.property.1 0⟩,⟨fun i => f.val i.succ, by
    constructor
    · intro i
      apply Finset.mem_sdiff.mpr
      refine ⟨f.property.1 i.succ, ?_⟩
      intro h
      have he := Finset.mem_singleton.mp (Finset.mem_product.mp h).1
      have hi := f.property.2 he
      have hn : i.succ ≠ 0 := Fin.succ_ne_zero i
      exact hn hi
    · intro i j hij
      exact Fin.succ_injective N (f.property.2 hij)⟩⟩
  invFun z := ⟨Fin.cons z.1.val z.2.val, by
    constructor
    · intro i
      cases i using Fin.cases with
      | zero => exact z.1.property
      | succ i => exact (Finset.mem_sdiff.mp (z.2.property.1 i)).1
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j =>
          exfalso
          have hn := (Finset.mem_sdiff.mp (z.2.property.1 j)).2
          apply hn
          exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr hij.symm,Finset.mem_univ _⟩
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          exfalso
          have hn := (Finset.mem_sdiff.mp (z.2.property.1 i)).2
          apply hn
          exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr hij,Finset.mem_univ _⟩
        | succ j =>
          exact congrArg Fin.succ (z.2.property.2 hij)⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    cases i using Fin.cases <;> rfl
  right_inv z := by
    rcases z with ⟨x,f⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Subtype.ext
    funext i
    rfl

/-- Exact full-selection count on any nested family of levels. The product is
    an ordinary natural count; truncated subtraction handles impossible choices. -/
theorem selections_count (m N : ℕ) (L : Fin N → Finset (C × Fin m))
    (hL : NestedFull m L) :
    Fintype.card (Selections m L) = ∏ i : Fin N, ((L i).card - m*i.val) := by
  classical
  induction N with
  | zero =>
    haveI : Unique (Selections m L) :=
      { default := ⟨fun i => Fin.elim0 i, by constructor <;> intro i <;> exact Fin.elim0 i⟩
        uniq := fun f => Subtype.ext (funext (fun i => Fin.elim0 i)) }
    simp
  | succ N ih =>
    rw [Fintype.card_congr (split m N L), Fintype.card_sigma]
    have hc (x : ↥(L 0)) : Fintype.card (Selections m (removeColumn m N L x.val)) =
        ∏ i : Fin N, ((L i.succ).card - m*(i.val+1)) := by
      rw [ih _ (remove_nested m N L hL x.val)]
      apply Finset.prod_congr rfl
      intro i _
      rw [remove_card m N L hL x i, Nat.sub_sub]
      congr 1
      ring
    simp_rw [hc]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
      Fin.prod_univ_succ]
    simp

end D5.S3.Combinatorics.Partitions.RookLevelSelection
