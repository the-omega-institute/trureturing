/- GID: D5/S1/Words/Permutations/OrderedBlockAllocations
   generality: G
   mirror-B: D5/B/S1/Words/Permutations/OrderedBlockAllocations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered allocations factor permutations and determine the first-block minimum mean. -/

/-
admission_basis: escape-witness
allocation_card_factorial: proof_shape: content; escape_witness: permutationFactorEquiv.
weighted_increasing_blocks: proof_shape: content; escape_witness: allocation_minimum_weight.
card_increasingOnBlocks: proof_shape: bind-only; escape_witness: none; consumer: countPoly_eval_descent.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21383.
Direct frozen dependencies: none.
-/

import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.GroupTheory.Perm.DomMulAct
open scoped Classical
namespace D5.S1.Words.Permutations.OrderedBlockAllocations

variable {α ι : Type} [Fintype α] [LinearOrder α] [Fintype ι] [DecidableEq ι]
@[reducible] def Allocation (c : α → ι) :=
  {f : α → ι // ∀ j, Fintype.card ({aFiber // f aFiber = j}) = Fintype.card ({aFiber // c aFiber = j})}
def IncreasingOnBlocks (c : α → ι) (π : Equiv.Perm α) : Prop :=
  ∀ a b, c a = c b → a < b → π a < π b
private noncomputable def fiberOrderIso (c : α → ι) (f : Allocation c) (j : ι) :
    {aFiber // c aFiber = j} ≃o {aFiber // f.1 aFiber = j} :=
  (monoEquivOfFin ({aFiber // c aFiber = j}) rfl).symm.trans
    (monoEquivOfFin ({aFiber // f.1 aFiber = j}) (f.2 j))

/-- Inverse of block extraction: sort each allocated block and concatenate along the source fibers. -/
private noncomputable def assemble (c : α → ι) (f : Allocation c) : Equiv.Perm α :=
  Equiv.ofFiberEquiv (fun j => (fiberOrderIso c f j).toEquiv)
@[simp] private theorem assemble_label (c : α → ι) (f : Allocation c) (a : α) :
    f.1 (assemble c f a) = c a :=
  Equiv.ofFiberEquiv_map _ _
private theorem assemble_apply (c : α → ι) (f : Allocation c) (a : α) {j : ι}
    (ha : c a = j) :
    assemble c f a = (fiberOrderIso c f j ⟨a, ha⟩).val := by
  subst j
  rfl
private theorem assemble_increasing (c : α → ι) (f : Allocation c) :
    IncreasingOnBlocks c (assemble c f) := by
  intro a b hab hlt
  let a' : {aFiber // c aFiber = (c a)} := ⟨a, rfl⟩
  let b' : {aFiber // c aFiber = (c a)} := ⟨b, hab.symm⟩
  rw [assemble_apply c f a rfl, assemble_apply c f b hab.symm]
  exact (fiberOrderIso c f (c a)).strictMono (show a' < b' from hlt)
private noncomputable def extract (c : α → ι) (π : Equiv.Perm α) : Allocation c :=
  ⟨fun a => c (π.symm a), fun j => Fintype.card_congr
    (π.symm.subtypeEquiv (p := fun a => c (π.symm a) = j)
      (q := fun a => c a = j) (fun _ => Iff.rfl))⟩
@[simp] private theorem extract_assemble (c : α → ι) (f : Allocation c) :
    extract c (assemble c f) = f := by
  apply Subtype.ext
  funext a
  change c ((assemble c f).symm a) = f.1 a
  simpa using (assemble_label c f ((assemble c f).symm a)).symm
private noncomputable def permFiberOrderIso (c : α → ι) (π : Equiv.Perm α)
    (hπ : IncreasingOnBlocks c π) (j : ι) : {aFiber // c aFiber = j} ≃o {aFiber // (extract c π).1 aFiber = j} :=
  { toEquiv := π.subtypeEquiv (p := fun a => c a = j)
      (q := fun a => (extract c π).1 a = j) (fun _ => by simp [extract])
    map_rel_iff' := by
      intro a b
      change π a.val ≤ π b.val ↔ a.val ≤ b.val
      constructor
      · intro hab
        by_contra h
        have hlt := hπ b a (b.2.trans a.2.symm) (lt_of_not_ge h)
        exact (not_lt_of_ge hab) hlt
      · intro hab
        rcases lt_or_eq_of_le hab with hlt | heq
        · exact (hπ a b (a.2.trans b.2.symm) hlt).le
        · simp [heq] }
@[simp] private theorem assemble_extract (c : α → ι) (π : Equiv.Perm α)
    (hπ : IncreasingOnBlocks c π) : assemble c (extract c π) = π := by
  ext a
  have h := Subsingleton.elim (fiberOrderIso c (extract c π) (c a))
    (permFiberOrderIso c π hπ (c a))
  exact congrArg (fun e : {aFiber // c aFiber = (c a)} ≃o {aFiber // (extract c π).1 aFiber = (c a)} =>
    (e ⟨a, rfl⟩).val) h

/-- Actual ordered block allocations, rather than a second copy of the permutation subtype. -/
private noncomputable def orderedBlockEquiv (c : α → ι) :
    {π : Equiv.Perm α // IncreasingOnBlocks c π} ≃ Allocation c where
  toFun p := extract c p.1
  invFun f := ⟨assemble c f, assemble_increasing c f⟩
  left_inv p := Subtype.ext (assemble_extract c p.1 p.2)
  right_inv f := extract_assemble c f

/-- Permutations internal to the prescribed source blocks. -/
@[reducible] private def InternalPerm (c : α → ι) :=
  {τ : Equiv.Perm α // ∀ a, c (τ a) = c a}
private noncomputable def internalPermEquiv (c : α → ι) :
    InternalPerm c ≃ (∀ j, Equiv.Perm ({aFiber // c aFiber = j})) :=
  ((Equiv.subtypeEquiv (DomMulAct.mk : Equiv.Perm α ≃ (Equiv.Perm α)ᵈᵐᵃ)
    (p := fun τ => ∀ a, c (τ a) = c a)
    (q := fun τ => τ ∈ MulAction.stabilizer (Equiv.Perm α)ᵈᵐᵃ c)
    (fun τ => by
      rw [DomMulAct.mem_stabilizer_iff]
      change (∀ a, c (τ a) = c a) ↔ (fun a => c (τ a)) = c
      exact funext_iff.symm)).trans MulOpposite.opEquiv).trans
        (DomMulAct.stabilizerMulEquiv c).toEquiv
private noncomputable def residual (c : α → ι) (π : Equiv.Perm α) : InternalPerm c :=
  ⟨π.trans (assemble c (extract c π)).symm, fun a => by
    have h := assemble_label c (extract c π) ((assemble c (extract c π)).symm (π a))
    simpa [extract] using h.symm⟩
private noncomputable def composeAllocation (c : α → ι) (f : Allocation c) (τ : InternalPerm c) :
    Equiv.Perm α := τ.1.trans (assemble c f)
@[simp] private theorem extract_composeAllocation (c : α → ι) (f : Allocation c)
    (τ : InternalPerm c) : extract c (composeAllocation c f τ) = f := by
  apply Subtype.ext
  funext a
  have hτ (x : α) : c (τ.1.symm x) = c x := by
    have h := τ.2 (τ.1.symm x)
    simpa using h.symm
  change c (τ.1.symm ((assemble c f).symm a)) = f.1 a
  rw [hτ]
  simpa using (assemble_label c f ((assemble c f).symm a)).symm

/-- Sorting forgets precisely one independent internal permutation per block. -/
private noncomputable def permutationFactorEquiv (c : α → ι) :
    Equiv.Perm α ≃ Allocation c × InternalPerm c where
  toFun π := (extract c π, residual c π)
  invFun x := composeAllocation c x.1 x.2
  left_inv π := by ext a; simp [composeAllocation, residual]
  right_inv x := by
    rcases x with ⟨f, τ⟩
    apply Prod.ext
    · exact extract_composeAllocation c f τ
    · apply Subtype.ext
      ext a
      change (assemble c (extract c (composeAllocation c f τ))).symm
        (assemble c f (τ.1 a)) = τ.1 a
      rw [extract_composeAllocation]
      exact (assemble c f).symm_apply_apply _
theorem allocation_card_factorial (c : α → ι) :
    Fintype.card (Allocation c) * (∏ j, (Fintype.card ({aFiber // c aFiber = j})).factorial) =
      (Fintype.card α).factorial := by
  have hi := Fintype.card_congr (internalPermEquiv c)
  simp only [Fintype.card_pi, Fintype.card_perm] at hi
  have h := Fintype.card_congr (permutationFactorEquiv c)
  rw [Fintype.card_perm, Fintype.card_prod, hi] at h
  exact h.symm

/-- The multinomial count is a consequence of the explicit permutation factorization. -/
private theorem sum_extract (c : α → ι) [Fintype (Allocation c)]
    [Fintype (InternalPerm c)] [Fintype (Equiv.Perm α)] (w : Allocation c → ℚ) :
    (∑ π : Equiv.Perm α, w (extract c π)) =
      (Fintype.card (InternalPerm c) : ℚ) * ∑ f : Allocation c, w f := by
  rw [← (permutationFactorEquiv c).symm.sum_comp]
  change (∑ x : Allocation c × InternalPerm c,
    w (extract c (composeAllocation c x.1 x.2))) = _
  simp only [extract_composeAllocation, Fintype.sum_prod_type, Finset.sum_const,
    nsmul_eq_mul]
  rw [← Finset.mul_sum, Finset.card_univ]

end D5.S1.Words.Permutations.OrderedBlockAllocations

namespace D5.S1.Words.Permutations.OrderedBlockAllocations
open Finset
private noncomputable def minPlus (T : Finset ℕ) : ℕ :=
  if h : T.Nonempty then T.min' h + 1 else 0
private theorem minPlus_tail_count {n : ℕ} {T : Finset ℕ}
    (hT : T ⊆ range n) (hne : T.Nonempty) :
    minPlus T = ∑ a ∈ range (n + 1), if T ⊆ Ico a n then 1 else 0 := by
  have hmin : T.min' hne < n := mem_range.mp (hT (min'_mem T hne))
  have hfilter : (range (n + 1)).filter (fun a => T ⊆ Ico a n) =
      range (T.min' hne + 1) := by
    ext a
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨ha, h⟩
      have := (mem_Ico.mp (h (min'_mem T hne))).1
      omega
    · intro ha
      refine ⟨by omega, ?_⟩
      intro x hx
      apply mem_Ico.mpr
      have hm := min'_le T x hx
      exact ⟨by omega, mem_range.mp (hT hx)⟩
  rw [← sum_filter, hfilter]
  simp [minPlus, hne]
private theorem subset_minimum_sum (n d : ℕ) (hd : 0 < d) :
    (∑ T ∈ (range n).powersetCard d, minPlus T) = (n + 1).choose (d + 1) := by
  calc
    (∑ T ∈ (range n).powersetCard d, minPlus T) =
        ∑ T ∈ (range n).powersetCard d,
          ∑ a ∈ range (n + 1), if T ⊆ Ico a n then 1 else 0 := by
      apply sum_congr rfl
      intro T hT
      obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hT
      apply minPlus_tail_count hsub
      exact card_pos.mp (hcard.symm ▸ hd)
    _ = ∑ a ∈ range (n + 1), ∑ T ∈ (range n).powersetCard d,
          if T ⊆ Ico a n then 1 else 0 := sum_comm
    _ = ∑ a ∈ range (n + 1), (n - a).choose d := by
      apply sum_congr rfl
      intro a ha
      have hfilter : ((range n).powersetCard d).filter (fun T => T ⊆ Ico a n) =
          (Ico a n).powersetCard d := by
        ext T
        simp only [mem_filter, mem_powersetCard]
        constructor
        · rintro ⟨⟨hsub, hcard⟩, h⟩
          exact ⟨h, hcard⟩
        · rintro ⟨h, hcard⟩
          exact ⟨⟨fun x hx => mem_range.mpr (mem_Ico.mp (h hx)).2, hcard⟩, h⟩
      rw [← sum_filter, hfilter]
      simp [card_powersetCard, Nat.card_Ico]
    _ = ∑ a ∈ range (n + 1), a.choose d := by
      simpa only [Nat.add_sub_cancel] using (sum_range_reflect (fun a => a.choose d) (n + 1))
    _ = ∑ a ∈ Icc d n, a.choose d := by
      symm
      apply sum_subset
      · intro a ha
        exact mem_range.mpr (by have := (mem_Icc.mp ha).2; omega)
      · intro a ha hnot
        have hn := mem_range.mp ha
        have hlt : a < d := by
          by_contra h
          exact hnot (mem_Icc.mpr ⟨by omega, by omega⟩)
        exact Nat.choose_eq_zero_of_lt hlt
    _ = (n + 1).choose (d + 1) := Nat.sum_Icc_choose n d

end D5.S1.Words.Permutations.OrderedBlockAllocations
namespace D5.S1.Words.Permutations.OrderedBlockAllocations
open Finset

variable {α : Type} [Fintype α] [LinearOrder α]
private theorem card_selectedSet (c : α → Bool) :
    ((univ.filter (fun a => c a = true))).card = Fintype.card ({aFiber // c aFiber = true}) := by
  simp [Fintype.card_subtype]
private theorem card_falseFiber (c : α → Bool) :
    Fintype.card ({aFiber // c aFiber = false}) = Fintype.card α - ((univ.filter (fun a => c a = true))).card := by
  simpa only [Bool.eq_false_eq_not_eq_true, Fintype.card_subtype] using
    (Fintype.card_subtype_compl (fun a => c a = true))
@[simp] private theorem selectedSet_boolOfSet (s : Finset α) : (univ.filter (fun a => ((fun a => decide (a ∈ s))) a = true)) = s := by
  simpa only [decide_eq_true_eq] using (Finset.filter_univ_mem s)
private theorem boolOfSet_selectedSet (c : α → Bool) : (fun a => decide (a ∈ ((univ.filter (fun a => c a = true))))) = c := by
  funext a
  simp
private noncomputable def boolAllocationOfSet (c : α → Bool)
    (s : {s : Finset α // s.card = ((univ.filter (fun a => c a = true))).card}) : Allocation c :=
  ⟨(fun a => decide (a ∈ s.1)), by
    intro j
    cases j
    · rw [card_falseFiber, card_falseFiber, selectedSet_boolOfSet, s.2]
    · rw [← card_selectedSet, ← card_selectedSet, selectedSet_boolOfSet, s.2]⟩
private noncomputable def boolAllocationEquiv (c : α → Bool) :
    Allocation c ≃ {s : Finset α // s.card = ((univ.filter (fun a => c a = true))).card} where
  toFun f := ⟨(univ.filter (fun a => f.1 a = true)), by rw [card_selectedSet, f.2, ← card_selectedSet]⟩
  invFun := boolAllocationOfSet c
  left_inv f := Subtype.ext (boolOfSet_selectedSet f.1)
  right_inv s := Subtype.ext (selectedSet_boolOfSet s.1)

/-- The image of a block, in natural-number letter coordinates starting at zero. -/
private def natFiber {n : ℕ} {ι : Type} [DecidableEq ι] (f : Fin n → ι) (j : ι) : Finset ℕ :=
  (univ.filter (fun a => f a = j)).image Fin.val
@[simp] private theorem mem_natFiber {n : ℕ} {ι : Type} [DecidableEq ι]
    (f : Fin n → ι) (j : ι) (a : ℕ) :
    a ∈ natFiber f j ↔ ∃ h : a < n, f ⟨a, h⟩ = j := by
  simp only [natFiber, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x.isLt, hx⟩
  · rintro ⟨h, hh⟩; exact ⟨⟨a, h⟩, hh, rfl⟩
private noncomputable def finsetNatEquiv (n d : ℕ) :
    {s : Finset (Fin n) // s.card = d} ≃ ↥((range n).powersetCard d) where
  toFun s := ⟨s.1.image Fin.val, mem_powersetCard.mpr ⟨by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
    exact mem_range.mpr x.isLt,
    by simpa only [card_image_of_injective _ Fin.val_injective] using s.2⟩⟩
  invFun s := ⟨univ.filter (fun x : Fin n => x.val ∈ s.1), by
    have he : (univ.filter (fun x : Fin n => x.val ∈ s.1)).image Fin.val = s.1 := by
      ext a
      simp only [mem_image, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro ha
        exact ⟨⟨a, mem_range.mp ((mem_powersetCard.mp s.2).1 ha)⟩, ha, rfl⟩
    have hc := congrArg Finset.card he
    rw [card_image_of_injective _ Fin.val_injective] at hc
    exact hc.trans (mem_powersetCard.mp s.2).2⟩
  left_inv s := by
    apply Subtype.ext
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨b, hb, he⟩
      exact Fin.val_injective he ▸ hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  right_inv s := by
    apply Subtype.ext
    ext a
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro ha
      exact ⟨⟨a, mem_range.mp ((mem_powersetCard.mp s.2).1 ha)⟩, ha, rfl⟩
private theorem boolAllocation_minimum_sum {n : ℕ} (c : Fin n → Bool)
    (hd : 0 < ((univ.filter (fun a => c a = true))).card) :
    (∑ f : Allocation c, minPlus (natFiber f.1 true)) =
      (n + 1).choose (((univ.filter (fun a => c a = true))).card + 1) := by
  let e := (boolAllocationEquiv c).trans (finsetNatEquiv n ((univ.filter (fun a => c a = true))).card)
  have he (f : Allocation c) : (e f).1 = natFiber f.1 true := rfl
  calc
    _ = ∑ T : ↥((range n).powersetCard ((univ.filter (fun a => c a = true))).card), minPlus T.1 :=
      Fintype.sum_equiv e
        (fun f : Allocation c => minPlus (natFiber f.1 true))
        (fun s : ↥((range n).powersetCard ((univ.filter (fun a => c a = true))).card) => minPlus s.1)
        (fun f => congrArg minPlus (he f).symm)
    _ = ∑ T ∈ (range n).powersetCard ((univ.filter (fun a => c a = true))).card, minPlus T := by
      exact Finset.sum_coe_sort _ _
    _ = _ := subset_minimum_sum n ((univ.filter (fun a => c a = true))).card hd
private theorem boolAllocation_card {n : ℕ} (c : Fin n → Bool) :
    Fintype.card (Allocation c) = n.choose ((univ.filter (fun a => c a = true))).card := by
  let e := (boolAllocationEquiv c).trans (finsetNatEquiv n ((univ.filter (fun a => c a = true))).card)
  simpa using Fintype.card_congr e

/-- Refining other blocks leaves the distribution of the chosen block's minimum unchanged. -/
private theorem allocation_minimum_weight {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Fin n → ι) (j : ι) (hd : 0 < Fintype.card ({aFiber // c aFiber = j})) :
    ((Fintype.card ({aFiber // c aFiber = j}) + 1 : ℕ) : ℚ) *
      (∑ f : Allocation c, (minPlus (natFiber f.1 j) : ℚ)) =
      (n + 1 : ℚ) * Fintype.card (Allocation c) := by
  let b : Fin n → Bool := fun a => decide (c a = j)
  let d := Fintype.card ({aFiber // c aFiber = j})
  have hb : ((univ.filter (fun a => b a = true))).card = d := by
    rw [card_selectedSet]
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun a => by simp [b])
  have hdc : 0 < ((univ.filter (fun a => b a = true))).card := by simpa [hb] using hd
  have hfiber (π : Equiv.Perm (Fin n)) :
      natFiber (extract c π).1 j = natFiber (extract b π).1 true := by
    ext a
    simp [mem_natFiber, extract, b]
  have hsum :
      (Fintype.card (InternalPerm c) : ℚ) *
        (∑ f : Allocation c, (minPlus (natFiber f.1 j) : ℚ)) =
      (Fintype.card (InternalPerm b) : ℚ) * ((n + 1).choose (d + 1) : ℚ) := by
    rw [← sum_extract c (fun f => (minPlus (natFiber f.1 j) : ℚ))]
    simp_rw [hfiber]
    change (∑ π : Equiv.Perm (Fin n),
      (fun f : Allocation b => (minPlus (natFiber f.1 true) : ℚ)) (extract b π)) = _
    have hsumb := sum_extract b (fun f : Allocation b => (minPlus (natFiber f.1 true) : ℚ))
    change (∑ π, (minPlus (natFiber (extract b π).1 true) : ℚ)) = _
    calc
      _ = (Fintype.card (InternalPerm b) : ℚ) *
          ∑ f : Allocation b, (minPlus (natFiber f.1 true) : ℚ) := hsumb
      _ = _ := by
        have hm := boolAllocation_minimum_sum b hdc
        rw [hb] at hm
        have hmQ : (∑ f : Allocation b, (minPlus (natFiber f.1 true) : ℚ)) =
            ((n + 1).choose (d + 1) : ℚ) := by exact_mod_cast hm
        rw [hmQ]
  have hcount : (Fintype.card (InternalPerm c) : ℚ) * Fintype.card (Allocation c) =
      (Fintype.card (InternalPerm b) : ℚ) * (n.choose d : ℚ) := by
    have hc := Fintype.card_congr (permutationFactorEquiv c)
    have hb' := Fintype.card_congr (permutationFactorEquiv b)
    rw [Fintype.card_prod] at hc hb'
    rw [boolAllocation_card, hb] at hb'
    have he := hc.symm.trans hb'
    have he' : Fintype.card (InternalPerm c) * Fintype.card (Allocation c) =
        Fintype.card (InternalPerm b) * n.choose d := by simpa only [mul_comm] using he
    exact_mod_cast he'
  have hchoose : ((d + 1 : ℕ) : ℚ) * ((n + 1).choose (d + 1) : ℚ) =
      (n + 1 : ℚ) * (n.choose d : ℚ) := by
    exact_mod_cast (by simpa only [mul_comm] using (Nat.add_one_mul_choose_eq n d).symm)
  have hfac : (Fintype.card (InternalPerm c) : ℚ) ≠ 0 := by
    letI : Nonempty (InternalPerm c) := ⟨⟨Equiv.refl _, fun _ => rfl⟩⟩
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (InternalPerm c) ≠ 0)
  apply mul_left_cancel₀ hfac
  calc
    (Fintype.card (InternalPerm c) : ℚ) *
        (((Fintype.card ({aFiber // c aFiber = j}) + 1 : ℕ) : ℚ) *
          (∑ f : Allocation c, (minPlus (natFiber f.1 j) : ℚ))) =
        ((d + 1 : ℕ) : ℚ) *
          ((Fintype.card (InternalPerm c) : ℚ) *
            ∑ f : Allocation c, (minPlus (natFiber f.1 j) : ℚ)) := by ring
    _ = ((d + 1 : ℕ) : ℚ) *
        ((Fintype.card (InternalPerm b) : ℚ) * ((n + 1).choose (d + 1) : ℚ)) := by rw [hsum]
    _ = (Fintype.card (InternalPerm b) : ℚ) * ((n + 1 : ℚ) * (n.choose d : ℚ)) := by
      calc
        _ = (Fintype.card (InternalPerm b) : ℚ) *
            (((d + 1 : ℕ) : ℚ) * ((n + 1).choose (d + 1) : ℚ)) := by ring
        _ = _ := by rw [hchoose]
    _ = (n + 1 : ℚ) *
        ((Fintype.card (InternalPerm c) : ℚ) * Fintype.card (Allocation c)) := by
      rw [hcount]; ring
    _ = (Fintype.card (InternalPerm c) : ℚ) *
        ((n + 1 : ℚ) * Fintype.card (Allocation c)) := by ring

end D5.S1.Words.Permutations.OrderedBlockAllocations

namespace D5.S1.Words.Permutations.OrderedBlockAllocations
open Finset
private theorem firstLetter_eq_block_minimum {n : ℕ} (hn : 0 < n) {ι : Type}
    [Fintype ι] [DecidableEq ι] (c : Fin n → ι) (π : Equiv.Perm (Fin n))
    (hπ : IncreasingOnBlocks c π) :
    (if h : 0 < n then (π ⟨0, h⟩).val + 1 else 0) = minPlus (natFiber (extract c π).1 (c ⟨0, hn⟩)) := by
  let z : Fin n := ⟨0, hn⟩
  let T := natFiber (extract c π).1 (c z)
  have hm : (π z).val ∈ T := by
    apply (mem_natFiber _ _ _).mpr
    exact ⟨(π z).isLt, by simp [extract]⟩
  have hne : T.Nonempty := ⟨_, hm⟩
  have hmin : T.min' hne = (π z).val := by
    apply le_antisymm (min'_le _ _ hm)
    apply le_min'
    intro a ha
    obtain ⟨ha, hh⟩ := (mem_natFiber _ _ _).mp ha
    let x : Fin n := ⟨a, ha⟩
    let y := π.symm x
    have hy : c y = c z := hh
    have hle : π z ≤ π y := by
      by_cases he : z = y
      · exact le_of_eq (congrArg π he)
      · apply le_of_lt
        exact hπ z y hy.symm (lt_of_le_of_ne (show z ≤ y from Nat.zero_le y.val) he)
    have hpy : π y = x := π.apply_symm_apply x
    rw [hpy] at hle
    exact hle
  rw [dif_pos hn]
  change (π z).val + 1 = minPlus T
  simp [minPlus, hne, hmin]
theorem weighted_increasing_blocks {n : ℕ} (hn : 0 < n) {ι : Type}
    [Fintype ι] [DecidableEq ι] (c : Fin n → ι) :
    ((Fintype.card ({aFiber // c aFiber = (c ⟨0, hn⟩)}) + 1 : ℕ) : ℚ) *
      (∑ p : {π : Equiv.Perm (Fin n) // IncreasingOnBlocks c π}, ((if h : 0 < n then (p.1 ⟨0, h⟩).val + 1 else 0 : ℕ) : ℚ)) =
      (n + 1 : ℚ) * Fintype.card {π : Equiv.Perm (Fin n) // IncreasingOnBlocks c π} := by
  let e := orderedBlockEquiv c
  have hs :
      (∑ p : {π : Equiv.Perm (Fin n) // IncreasingOnBlocks c π}, ((if h : 0 < n then (p.1 ⟨0, h⟩).val + 1 else 0 : ℕ) : ℚ)) =
        ∑ f : Allocation c, (minPlus (natFiber f.1 (c ⟨0, hn⟩)) : ℚ) := by
    apply Fintype.sum_equiv e
    intro p
    change ((if h : 0 < n then (p.1 ⟨0, h⟩).val + 1 else 0 : ℕ) : ℚ) =
      (minPlus (natFiber (extract c p.1).1 (c ⟨0, hn⟩)) : ℚ)
    exact congrArg (fun t : ℕ => (t : ℚ)) (firstLetter_eq_block_minimum hn c p.1 p.2)
  rw [hs, Fintype.card_congr e]
  apply allocation_minimum_weight
  letI : Nonempty ({aFiber // c aFiber = (c ⟨0, hn⟩)}) := ⟨⟨⟨0, hn⟩, rfl⟩⟩
  exact Fintype.card_pos

end D5.S1.Words.Permutations.OrderedBlockAllocations

namespace D5.S1.Words.Permutations.OrderedBlockAllocations
variable {α ι : Type} [Fintype α] [LinearOrder α] [Fintype ι] [DecidableEq ι]
theorem card_increasingOnBlocks (c : α → ι) :
    Fintype.card {π : Equiv.Perm α // IncreasingOnBlocks c π} = Fintype.card (Allocation c) :=
  Fintype.card_congr (orderedBlockEquiv c)
end D5.S1.Words.Permutations.OrderedBlockAllocations
