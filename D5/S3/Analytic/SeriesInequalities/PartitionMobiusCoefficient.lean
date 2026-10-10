/- GID: D5/S3/Analytic/SeriesInequalities/PartitionMobiusCoefficient
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/PartitionMobiusCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite partition Mobius coefficients and moment-cumulant inversion. -/

import D5.S3.Analytic.SeriesInequalities.PartitionMobiusInversion
import Mathlib.Data.Finset.Grade
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Analytic.SeriesInequalities.PartitionMobiusCoefficient

attribute [local instance] Classical.propDecidable
open Finset

local notation "blockUnion" => (Finset.biUnion · id)
local notation "weight" => (fun k : ℕ => (-1 : ℤ) ^ (k - 1) * (Nat.factorial (k - 1) : ℤ))

variable {α : Type*} [DecidableEq α] {s : Finset α}

private lemma block_union_subset (P : Finpartition s) {U : Finset (Finset α)}
    (hU : U ⊆ P.parts) : blockUnion U ⊆ s := by
  exact biUnion_subset.mpr fun b hb => P.subset (hU hb)

/-- A union of whole disjoint nonempty blocks remembers exactly which blocks were used. -/
private lemma block_subset_block_union_iff (P : Finpartition s) {U : Finset (Finset α)}
    (hU : U ⊆ P.parts) {b : Finset α} (hb : b ∈ P.parts) :
    b ⊆ blockUnion U ↔ b ∈ U := by
  classical
  let t : Finset P.parts := P.parts.attach.filter (fun c => c.1 ∈ U)
  have ht : t ⊆ P.parts.attach := filter_subset _ _
  have h := P.supIndep.attach.le_sup_iff ht (mem_attach _ ⟨b, hb⟩)
    (fun c => P.ne_empty c.2)
  have hu : t.sup (fun c => c.1) = U.biUnion id := by
    ext x
    simp only [t, mem_sup, mem_filter, mem_attach, true_and, mem_biUnion,
      Subtype.exists, exists_prop]
    constructor
    · rintro ⟨c, _, hcU, hxc⟩
      exact ⟨c, hcU, hxc⟩
    · rintro ⟨c, hcU, hxc⟩
      exact ⟨c, hU hcU, hcU, hxc⟩
  simpa [hu, t] using h

private lemma block_union_injective (P : Finpartition s) {U V : Finset (Finset α)}
    (hU : U ⊆ P.parts) (hV : V ⊆ P.parts)
    (h : blockUnion U = blockUnion V) : U = V := by
  ext b
  by_cases hb : b ∈ P.parts
  · rw [← block_subset_block_union_iff P hU hb, ← block_subset_block_union_iff P hV hb, h]
  · exact iff_of_false (fun hu => hb (hU hu)) (fun hv => hb (hV hv))

private lemma block_union_nonempty (P : Finpartition s) {U : Finset (Finset α)}
    (hU : U ⊆ P.parts) (hne : U.Nonempty) : (blockUnion U).Nonempty := by
  obtain ⟨b, hb⟩ := hne
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts (hU hb)
  exact ⟨x, mem_biUnion.mpr ⟨b, hb, hx⟩⟩

/-- Flatten a partition of the actual blocks into a coarsening of the original partition. -/
private def coarsen (P : Finpartition s) (Q : Finpartition P.parts) : Finpartition s := by
  refine Finpartition.ofExistsUnique (Q.parts.image blockUnion) ?_ ?_ ?_
  · intro b hb
    obtain ⟨U, hU, rfl⟩ := mem_image.mp hb
    exact block_union_subset P (Q.subset hU)
  · intro x hx
    obtain ⟨b, hb, hxb⟩ := P.exists_mem hx
    obtain ⟨U, hU, hbU⟩ := Q.exists_mem hb
    refine ⟨blockUnion U, ⟨mem_image.mpr ⟨U, hU, rfl⟩,
      mem_biUnion.mpr ⟨b, hbU, hxb⟩⟩, ?_⟩
    rintro v ⟨hv, hxv⟩
    obtain ⟨V, hV, rfl⟩ := mem_image.mp hv
    obtain ⟨c, hcV, hxc⟩ := mem_biUnion.mp hxv
    have hcb : c = b := P.eq_of_mem_parts (Q.subset hV hcV) hb hxc hxb
    have hVU : V = U := Q.eq_of_mem_parts hV hU (hcb ▸ hcV) hbU
    exact congrArg blockUnion hVU
  · intro h
    obtain ⟨U, hU, hzero⟩ := mem_image.mp h
    exact (block_union_nonempty P (Q.subset hU) (Q.nonempty_of_mem_parts hU)).ne_empty hzero

@[simp] private lemma coarsen_parts (P : Finpartition s) (Q : Finpartition P.parts) :
    (coarsen P Q).parts = Q.parts.image blockUnion := rfl

private lemma le_coarsen (P : Finpartition s) (Q : Finpartition P.parts) : P ≤ coarsen P Q := by
  intro b hb
  obtain ⟨U, hU, hbU⟩ := Q.exists_mem hb
  exact ⟨blockUnion U, mem_image.mpr ⟨U, hU, rfl⟩,
    (block_subset_block_union_iff P (Q.subset hU) hb).mpr hbU⟩

private lemma coarsen_card (P : Finpartition s) (Q : Finpartition P.parts) :
    (coarsen P Q).parts.card = Q.parts.card := by
  rw [coarsen_parts]
  apply card_image_iff.mpr
  intro U hU V hV h
  exact block_union_injective P (Q.subset hU) (Q.subset hV) h

private def blockGroup (P : Finpartition s) (b : Finset α) : Finset (Finset α) :=
  P.parts.filter (fun c => c ⊆ b)

private lemma block_group_subset (P : Finpartition s) (b : Finset α) :
    blockGroup P b ⊆ P.parts := filter_subset _ _

private lemma block_group_union (P : Finpartition s) {U : Finset (Finset α)}
    (hU : U ⊆ P.parts) : blockGroup P (blockUnion U) = U := by
  ext b
  simp only [blockGroup, mem_filter]
  exact ⟨fun h => (block_subset_block_union_iff P hU h.1).mp h.2,
    fun h => ⟨hU h, (block_subset_block_union_iff P hU (hU h)).mpr h⟩⟩

private lemma block_union_group (P R : Finpartition s) (hPR : P ≤ R)
    {b : Finset α} (hb : b ∈ R.parts) : blockUnion (blockGroup P b) = b := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc, hxc⟩ := mem_biUnion.mp hx
    exact (mem_filter.mp hc).2 hxc
  · intro hx
    obtain ⟨c, hc, hxc⟩ := P.exists_mem (R.subset hb hx)
    obtain ⟨d, hd, hcd⟩ := hPR hc
    have hdb : d = b := R.eq_of_mem_parts hd hb (hcd hxc) hx
    exact mem_biUnion.mpr ⟨c, mem_filter.mpr ⟨hc, hdb ▸ hcd⟩, hxc⟩

private lemma block_group_injective (P R : Finpartition s) (hPR : P ≤ R)
    {a b : Finset α} (ha : a ∈ R.parts) (hb : b ∈ R.parts)
    (h : blockGroup P a = blockGroup P b) : a = b := by
  rw [← block_union_group P R hPR ha, ← block_union_group P R hPR hb, h]

private lemma block_group_nonempty (P R : Finpartition s) (hPR : P ≤ R)
    {b : Finset α} (hb : b ∈ R.parts) : (blockGroup P b).Nonempty := by
  apply nonempty_iff_ne_empty.mpr
  intro h
  have heq := block_union_group P R hPR hb
  rw [h] at heq
  exact R.ne_empty hb heq.symm

/-- Recover, for each coarse block, the collection of original blocks that it contains. -/
private def uncoarsen (P R : Finpartition s) (hPR : P ≤ R) : Finpartition P.parts := by
  refine Finpartition.ofExistsUnique (R.parts.image (blockGroup P)) ?_ ?_ ?_
  · intro U hU
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hU
    exact block_group_subset P b
  · intro c hc
    obtain ⟨b, hb, hcb⟩ := hPR hc
    refine ⟨blockGroup P b, ⟨mem_image.mpr ⟨b, hb, rfl⟩,
      mem_filter.mpr ⟨hc, hcb⟩⟩, ?_⟩
    rintro V ⟨hV, hcV⟩
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hV
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hc
    have hdb : d = b := R.eq_of_mem_parts hd hb ((mem_filter.mp hcV).2 hx) (hcb hx)
    exact congrArg (blockGroup P) hdb
  · intro h
    obtain ⟨b, hb, heq⟩ := mem_image.mp h
    exact (block_group_nonempty P R hPR hb).ne_empty heq

@[simp] private lemma uncoarsen_parts (P R : Finpartition s) (hPR : P ≤ R) :
    (uncoarsen P R hPR).parts = R.parts.image (blockGroup P) := rfl

private lemma coarsen_uncoarsen (P R : Finpartition s) (hPR : P ≤ R) :
    coarsen P (uncoarsen P R hPR) = R := by
  apply Finpartition.ext
  rw [coarsen_parts, uncoarsen_parts, image_image]
  calc
    _ = R.parts.image id := image_congr fun b hb => block_union_group P R hPR hb
    _ = _ := image_id

private lemma uncoarsen_coarsen (P : Finpartition s) (Q : Finpartition P.parts) :
    uncoarsen P (coarsen P Q) (le_coarsen P Q) = Q := by
  apply Finpartition.ext
  rw [uncoarsen_parts, coarsen_parts, image_image]
  calc
    _ = Q.parts.image id := image_congr fun U hU => block_group_union P (Q.subset hU)
    _ = _ := image_id

/-- The block-union construction is a bijection, not merely a way to make some coarsenings. -/
private def coarseningEquiv (P : Finpartition s) :
    Finpartition P.parts ≃ {R : Finpartition s // P ≤ R} where
  toFun Q := ⟨coarsen P Q, le_coarsen P Q⟩
  invFun R := uncoarsen P R.1 R.2
  left_inv := uncoarsen_coarsen P
  right_inv R := Subtype.ext (coarsen_uncoarsen P R.1 R.2)

/-- Every block-count weighted coarsening sum is a sum over literal partitions of the blocks. -/
private theorem sum_coarsenings (P : Finpartition s) (w : ℕ → ℤ) :
    (∑ R : {R : Finpartition s // P ≤ R}, w R.1.parts.card) =
      ∑ Q : Finpartition P.parts, w Q.parts.card := by
  classical
  symm
  apply Fintype.sum_equiv (coarseningEquiv P)
  intro Q
  exact congrArg w (coarsen_card P Q).symm

variable {a : α}

private lemma choice_subset (P : Finpartition s) {b : Finset α}
    (hb : b ∈ insert ∅ P.parts) : b ⊆ s := by
  rcases mem_insert.mp hb with rfl | hb
  · exact empty_subset _
  · exact P.subset hb

/-- Insert a new point either as its own block (empty choice) or into a chosen old block. -/
private def insertPoint (P : Finpartition s) (ha : a ∉ s) (b : Finset α)
    (hb : b ∈ insert ∅ P.parts) : Finpartition (insert a s) := by
  have hold (c : Finset α) (hc : c ∈ P.parts) : a ∉ c := fun h => ha (P.subset hc h)
  refine Finpartition.ofExistsUnique (insert (insert a b) (P.parts.erase b)) ?_ ?_ ?_
  · intro c hc
    rcases mem_insert.mp hc with rfl | hc
    · exact insert_subset_insert _ (choice_subset P hb)
    · exact (P.subset (mem_erase.mp hc).2).trans (subset_insert _ _)
  · intro x hx
    by_cases hxa : x = a
    · subst x
      refine ⟨insert a b, ⟨mem_insert_self _ _, mem_insert_self _ _⟩, ?_⟩
      rintro c ⟨hc, hac⟩
      rcases mem_insert.mp hc with h | hc
      · exact h
      · exact (hold c (mem_erase.mp hc).2 hac).elim
    · have hxs := (mem_insert.mp hx).resolve_left hxa
      obtain ⟨c, hc, hxc⟩ := P.exists_mem hxs
      by_cases hcb : c = b
      · subst c
        refine ⟨insert a b, ⟨mem_insert_self _ _, mem_insert_of_mem hxc⟩, ?_⟩
        rintro d ⟨hd, hxd⟩
        rcases mem_insert.mp hd with h | hd
        · exact h
        · exact ((mem_erase.mp hd).1 (P.eq_of_mem_parts (mem_erase.mp hd).2 hc hxd hxc)).elim
      · refine ⟨c, ⟨mem_insert_of_mem (mem_erase.mpr ⟨hcb, hc⟩), hxc⟩, ?_⟩
        rintro d ⟨hd, hxd⟩
        rcases mem_insert.mp hd with rfl | hd
        · have hxb : x ∈ b := (mem_insert.mp hxd).resolve_left hxa
          have hbP : b ∈ P.parts := (mem_insert.mp hb).resolve_left (by
            intro hb0; simp [hb0] at hxb)
          exact (hcb (P.eq_of_mem_parts hc hbP hxc hxb)).elim
        · exact P.eq_of_mem_parts (mem_erase.mp hd).2 hc hxd hxc
  · intro h
    rcases mem_insert.mp h with h | h
    · exact (insert_nonempty a b).ne_empty h.symm
    · exact P.empty_notMem_parts (mem_erase.mp h).2

@[simp] private lemma insert_point_parts (P : Finpartition s) (ha : a ∉ s)
    (b : Finset α) (hb : b ∈ insert ∅ P.parts) :
    (insertPoint P ha b hb).parts = insert (insert a b) (P.parts.erase b) := rfl

private lemma insert_point_part (P : Finpartition s) (ha : a ∉ s)
    (b : Finset α) (hb : b ∈ insert ∅ P.parts) :
    (insertPoint P ha b hb).part a = insert a b := by
  exact (insertPoint P ha b hb).part_eq_of_mem (mem_insert_self _ _) (mem_insert_self _ _)

private def erasePoint (R : Finpartition (insert a s)) (ha : a ∉ s) : Finpartition s :=
  (R.avoid {a}).copy (by
    change (insert a s) \ {a} = s
    rw [sdiff_singleton_eq_erase, erase_insert ha])

@[simp] private lemma erase_point_parts (R : Finpartition (insert a s)) (ha : a ∉ s) :
    (erasePoint R ha).parts = (R.parts.image (fun b => b.erase a)).erase ∅ := by
  simp [erasePoint, Finpartition.avoid, Finpartition.ofErase, Finpartition.copy,
    sdiff_singleton_eq_erase]

private lemma erase_point_insertPoint (P : Finpartition s) (ha : a ∉ s)
    (b : Finset α) (hb : b ∈ insert ∅ P.parts) :
    erasePoint (insertPoint P ha b hb) ha = P := by
  apply Finpartition.ext
  rw [erase_point_parts, insert_point_parts, image_insert]
  have hab : a ∉ b := fun h => ha (choice_subset P hb h)
  rw [erase_insert hab]
  have himage : (P.parts.erase b).image (fun c => c.erase a) = P.parts.erase b := by
    calc
      _ = (P.parts.erase b).image id := image_congr fun c hc =>
        erase_eq_of_notMem (fun h => ha (P.subset (mem_erase.mp hc).2 h))
      _ = _ := image_id
  rw [himage]
  rcases mem_insert.mp hb with rfl | hb
  · simp [P.empty_notMem_parts]
  · rw [insert_erase hb, erase_eq_of_notMem P.empty_notMem_parts]

private lemma erased_part_choice (R : Finpartition (insert a s)) (ha : a ∉ s) :
    (R.part a).erase a ∈ insert ∅ (erasePoint R ha).parts := by
  by_cases hzero : (R.part a).erase a = ∅
  · exact mem_insert.mpr (Or.inl hzero)
  · apply mem_insert_of_mem
    rw [erase_point_parts]
    exact mem_erase.mpr ⟨hzero, mem_image.mpr
      ⟨R.part a, R.part_mem.mpr (mem_insert_self _ _), rfl⟩⟩

private lemma insert_point_erasePoint (R : Finpartition (insert a s)) (ha : a ∉ s) :
    insertPoint (erasePoint R ha) ha ((R.part a).erase a) (erased_part_choice R ha) = R := by
  apply Finpartition.ext
  rw [insert_point_parts, erase_point_parts,
    insert_erase (R.mem_part_self.mpr (mem_insert_self _ _))]
  have hpart : R.part a ∈ R.parts := R.part_mem.mpr (mem_insert_self _ _)
  have haP : a ∈ R.part a := R.mem_part_self.mpr (mem_insert_self _ _)
  have hold (c : Finset α) (hc : c ∈ R.parts) (hne : c ≠ R.part a) : a ∉ c := by
    intro hac
    exact hne (R.eq_of_mem_parts hc hpart hac haP)
  ext c
  constructor
  · intro hc
    rcases mem_insert.mp hc with rfl | hc
    · exact hpart
    · obtain ⟨hcne, hc⟩ := mem_erase.mp hc
      obtain ⟨_, hc⟩ := mem_erase.mp hc
      obtain ⟨d, hd, rfl⟩ := mem_image.mp hc
      have hne : d ≠ R.part a := fun h => hcne (congrArg (fun t => t.erase a) h)
      simpa [erase_eq_of_notMem (hold d hd hne)] using hd
  · intro hc
    by_cases hcp : c = R.part a
    · exact mem_insert.mpr (Or.inl hcp)
    · apply mem_insert_of_mem
      have hac := hold c hc hcp
      have hchosen : c ≠ (R.part a).erase a := by
        intro h
        obtain ⟨x, hx⟩ := R.nonempty_of_mem_parts hc
        have hxP : x ∈ R.part a := mem_of_mem_erase (h ▸ hx)
        exact hcp (R.eq_of_mem_parts hc hpart hx hxP)
      refine mem_erase.mpr ⟨hchosen, mem_erase.mpr ⟨R.ne_empty hc, ?_⟩⟩
      exact mem_image.mpr ⟨c, hc, erase_eq_of_notMem hac⟩

private def insertionEquiv (s : Finset α) (a : α) (ha : a ∉ s) :
    (Σ P : Finpartition s, {b : Finset α // b ∈ insert ∅ P.parts}) ≃
      Finpartition (insert a s) where
  toFun C := insertPoint C.1 ha C.2.1 C.2.2
  invFun R := ⟨erasePoint R ha, ⟨(R.part a).erase a, erased_part_choice R ha⟩⟩
  left_inv C := by
    rcases C with ⟨P, b, hb⟩
    dsimp only
    have hab : a ∉ b := fun h => ha (choice_subset P hb h)
    apply Sigma.ext (erase_point_insertPoint P ha b hb)
    apply (Subtype.heq_iff_coe_eq (by
      intro x
      change x ∈ insert ∅ (erasePoint (insertPoint P ha b hb) ha).parts ↔
        x ∈ insert ∅ P.parts
      rw [erase_point_insertPoint])).mpr
    change ((insertPoint P ha b hb).part a).erase a = b
    rw [insert_point_part, erase_insert hab]
  right_inv R := insert_point_erasePoint R ha

private lemma insert_point_card (P : Finpartition s) (ha : a ∉ s)
    (b : Finset α) (hb : b ∈ insert ∅ P.parts) :
    (insertPoint P ha b hb).parts.card = if b = ∅ then P.parts.card + 1 else P.parts.card := by
  have hnew : insert a b ∉ P.parts.erase b := by
    intro h
    exact ha (P.subset (mem_erase.mp h).2 (mem_insert_self _ _))
  rw [insert_point_parts, card_insert_of_notMem hnew]
  by_cases hb0 : b = ∅
  · simp [hb0, P.empty_notMem_parts]
  · rw [if_neg hb0, card_erase_of_mem ((mem_insert.mp hb).resolve_left hb0)]
    have : 0 < P.parts.card := card_pos.mpr ⟨b, (mem_insert.mp hb).resolve_left hb0⟩
    omega

private lemma weight_cancel (k : ℕ) (hk : 0 < k) :
    weight (k + 1) + k * weight k = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_succ, pow_succ]
  ring

private theorem partition_sum_insert (s : Finset α) (a : α) (ha : a ∉ s) (w : ℕ → ℤ) :
    (∑ Q : Finpartition (insert a s), w Q.parts.card) =
      ∑ P : Finpartition s, (w (P.parts.card + 1) + P.parts.card * w P.parts.card) := by
  rw [← (insertionEquiv s a ha).sum_comp, Fintype.sum_sigma]
  apply sum_congr rfl
  intro P hP
  change (∑ b : {b : Finset α // b ∈ insert ∅ P.parts},
    w (insertPoint P ha b.1 b.2).parts.card) = _
  simp_rw [insert_point_card]
  rw [sum_coe_sort (insert ∅ P.parts)
    (fun b : Finset α => w (if b = ∅ then P.parts.card + 1 else P.parts.card)),
    sum_insert P.empty_notMem_parts]
  congr 1
  calc
    _ = ∑ b ∈ P.parts, w P.parts.card := by
      apply sum_congr rfl
      intro b hb
      rw [if_neg (P.ne_empty hb)]
    _ = _ := by simp

private theorem partition_weight_sum_zero (s : Finset α) (a : α)
    (ha : a ∉ s) (hs : s.Nonempty) :
    (∑ Q : Finpartition (insert a s), weight Q.parts.card) = 0 := by
  rw [partition_sum_insert s a ha weight]
  apply sum_eq_zero
  intro P hP
  exact weight_cancel P.parts.card (card_pos.mpr (P.parts_nonempty hs.ne_empty))

private lemma partition_weight_sum_singleton (a : α) :
    (∑ Q : Finpartition ({a} : Finset α), weight Q.parts.card) = 1 := by
  letI := (isAtom_singleton a).uniqueFinpartition (P := (⊤ : Finpartition ({a} : Finset α)))
  have hp (P : Finpartition ({a} : Finset α)) : P.parts.card = 1 := by
    have hlo : 0 < P.parts.card := card_pos.mpr
      (P.parts_nonempty (singleton_nonempty a).ne_empty)
    have hhi := P.card_parts_le_card
    simp only [card_singleton] at hhi
    omega
  rw [Fintype.sum_unique]
  simp [hp]

private theorem partition_weight_sum (s : Finset α) (hs : s.Nonempty) :
    (∑ Q : Finpartition s, weight Q.parts.card) = if s.card = 1 then 1 else 0 := by
  obtain ⟨a, ha⟩ := hs
  by_cases he : (s.erase a).Nonempty
  · have hc : s.card ≠ 1 := by
      have := card_pos.mpr he
      rw [card_erase_of_mem ha] at this
      omega
    have h := partition_weight_sum_zero (s.erase a) a (notMem_erase a s) he
    rw [insert_erase ha] at h
    simpa [hc] using h
  · have he0 : s.erase a = ∅ := not_nonempty_iff_eq_empty.mp he
    have hs : s = {a} := by
      simpa [he0] using (insert_erase ha).symm
    subst s
    simpa using partition_weight_sum_singleton a

private lemma top_parts (s : Finset α) (hs : s.Nonempty) :
    (⊤ : Finpartition s).parts = {s} := by
  change (if h : s = ∅ then (Finpartition.empty (Finset α)).copy h.symm
    else Finpartition.indiscrete h).parts = {s}
  rw [dif_neg hs.ne_empty]
  rfl

private lemma card_parts_one_iff_top (s : Finset α) (hs : s.Nonempty) (P : Finpartition s) :
    P.parts.card = 1 ↔ P = ⊤ := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := card_eq_one.mp h
    have hbs : b = s := by simpa [hb] using P.biUnion_parts
    apply Finpartition.ext
    rw [hb, hbs, top_parts s hs]
  · rintro rfl
    simp [top_parts s hs]

private theorem weighted_coarsening_cancellation (s : Finset α) (hs : s.Nonempty)
    (P : Finpartition s) :
    (∑ Q : {Q : Finpartition s // P ≤ Q}, weight Q.1.parts.card) =
      if P = ⊤ then 1 else 0 := by
  rw [sum_coarsenings P weight, partition_weight_sum P.parts (P.parts_nonempty hs.ne_empty)]
  simp only [card_parts_one_iff_top s hs]

variable {R : Type*} [CommRing R]

local instance {s : Finset α} : LocallyFiniteOrder (Finpartition s) :=
  Fintype.toLocallyFiniteOrder

theorem partition_mobius_coefficient (s : Finset α) (hs : s.Nonempty)
    (P : Finpartition s) :
    IncidenceAlgebra.mu R P ⊤ =
      (-1 : R) ^ (P.parts.card - 1) * ((P.parts.card - 1).factorial : R) := by
  have hsum (Q : Finpartition s) :
      (if Q = ⊤ then (1 : R) else 0) =
        ∑ T ∈ Ici Q, (-1 : R) ^ (T.parts.card - 1) * ((T.parts.card - 1).factorial : R) := by
    rw [sum_subtype (Ici Q) (fun _ => mem_Ici)]
    have h := congrArg (Int.castRingHom R) (weighted_coarsening_cancellation s hs Q)
    simpa using h.symm
  have h := IncidenceAlgebra.moebius_inversion_top
    (fun Q : Finpartition s =>
      (-1 : R) ^ (Q.parts.card - 1) * ((Q.parts.card - 1).factorial : R))
    (fun Q => if Q = ⊤ then (1 : R) else 0) hsum P
  simpa using h.symm

open D5.S3.Analytic.SeriesInequalities.PartitionMobiusInversion

theorem moment_cumulant_without_mu_assumption
    (A : Finset α) (hA : A.Nonempty) (moment cumulant : Finset α → R)
    (hrelation : ∀ P : Finpartition A,
      partitionProduct moment P =
        ∑ Q ∈ Finset.Iic P, partitionProduct cumulant Q) :
    cumulant A = ∑ P : Finpartition A,
      partitionMoebiusCoefficient P * partitionProduct moment P ∧
    moment A = ∑ P : Finpartition A, partitionProduct cumulant P := by
  apply partition_mobius_moment_cumulant_inversion A hA moment cumulant hrelation
  intro P
  exact partition_mobius_coefficient A hA P

end D5.S3.Analytic.SeriesInequalities.PartitionMobiusCoefficient
