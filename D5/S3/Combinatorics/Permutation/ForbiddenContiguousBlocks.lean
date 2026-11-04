/- GID: D5/S3/Combinatorics/Permutation/ForbiddenContiguousBlocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/ForbiddenContiguousBlocks
   mirror-E: none(waiver:symbolic-finite-family-proof)
   anchors: []
   utility: none
   digest: Exact contiguous-block compression and finite-family avoidance with overlap. -/

import D5.S3.Combinatorics.CircularWords.CircleBlockEquivalence
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic

/-!
The new inference is the exact transport between a literal linear block and
an arc after adjoining a fresh separator. The existing actual two-block
bijection then counts every forbidden event on the SAME original order space.
Finite double counting includes the equality boundary with positive overlap.
All parameters are arbitrary finite sets and indexed families, not a census.
Library reuse: DisjointBlockContraction, CircularOrderCount, anchorEquiv;
pinned Mathlib List/Finset/factorial and double-counting contracts.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Finset
open D5.S3.Combinatorics.CircularWords.DisjointBlockContraction
open D5.S3.Combinatorics.CircularWords.CircularOrderCount
open D5.S3.Combinatorics.CircularWords.CircleBlockEquivalence
open D5.S3.Combinatorics.CircularWords.CyclicInsertionGap

namespace D5.S3.Combinatorics.Permutation.ForbiddenContiguousBlocks

variable {α : Type*} [DecidableEq α]

/-- Exactly the elements of S, in some internal order, occupy one literal interval. -/
def Block (S : Finset α) (w : List α) : Prop :=
  ∃ p u v : List α, w = p ++ u ++ v ∧ u.Perm S.toList

private theorem remainder_perm {A S : Finset α} {u v : List α}
    (h : (u ++ v).Perm A.toList) (hu : u.Perm S.toList) :
    v.Perm (A \ S).toList := by
  have hn := List.nodup_append.mp (h.nodup_iff.mpr A.nodup_toList)
  apply (List.perm_ext_iff_of_nodup hn.2.1 (A \ S).nodup_toList).mpr
  intro x
  simp only [mem_toList, mem_sdiff]
  constructor
  · intro hx
    refine ⟨mem_toList.mp (h.mem_iff.mp (List.mem_append.mpr (Or.inr hx))), ?_⟩
    intro hs
    exact hn.2.2 x (hu.mem_iff.mpr (mem_toList.mpr hs)) x hx rfl
  · rintro ⟨ha, hs⟩
    rcases List.mem_append.mp (h.mem_iff.mpr (mem_toList.mpr ha)) with hx | hx
    · exact (hs (mem_toList.mp (hu.mem_iff.mp hx))).elim
    · exact hx

private theorem some_perm {A : Finset α} {w : List α} (hw : w.Perm A.toList) :
    (w.map some).Perm (A.image some).toList := by
  apply (List.perm_ext_iff_of_nodup
    ((hw.nodup_iff.mpr A.nodup_toList).map (Option.some_injective α))
    (A.image some).nodup_toList).mpr
  intro x
  simp [List.mem_map, hw.mem_iff, mem_image]

private theorem unsome_perm {A : Finset α} {w : List (Option α)}
    (hw : w.Perm (A.image some).toList) : (w.filterMap id).Perm A.toList := by
  have h := (hw.trans (some_perm (List.Perm.refl A.toList)).symm).filterMap id
  simpa using h

private theorem map_some_unsome {w : List (Option α)} (hn : none ∉ w) :
    (w.filterMap id).map some = w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    cases x with
    | none => exact (hn (by simp)).elim
    | some x =>
      have ht : none ∉ w := fun h => hn (List.mem_cons_of_mem _ h)
      simpa using congrArg (List.cons (some x)) (ih ht)

private def extended (A : Finset α) : Finset (Option α) := insert none (A.image some)

private theorem some_subset {A S : Finset α} (hs : S ⊆ A) :
    S.image some ⊆ extended A := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
  simp [extended, hs ha]

private theorem anchored_perm {A : Finset α} {w : List α} (hw : w.Perm A.toList) :
    (none :: w.map some).Perm (extended A).toList := by
  have hn : (none :: w.map some).Nodup := by
    simp only [List.nodup_cons]
    exact ⟨by simp, (hw.nodup_iff.mpr A.nodup_toList).map (Option.some_injective α)⟩
  apply (List.perm_ext_iff_of_nodup hn (extended A).nodup_toList).mpr
  intro x
  simp [extended, List.mem_map, hw.mem_iff, mem_image]

/-- The separator prevents a circular run from crossing the ends of the original word. -/
private theorem arc_iff_block {A S : Finset α} (hs : S ⊆ A)
    {w : List α} (hw : w.Perm A.toList) :
    Arc (extended A) (S.image some) (none :: w.map some : List (Option α)) ↔ Block S w := by
  constructor
  · rintro ⟨u, v, hu, hv, hc⟩
    have hnone : none ∈ v := hv.mem_iff.mpr (by simp [extended])
    obtain ⟨p, q, hvsplit⟩ := List.mem_iff_append.mp hnone
    have hroot : (none :: w.map some : List (Option α)) =
        (none :: (q ++ u ++ p) : Cycle (Option α)) := by
      rw [hc, hvsplit]
      have hrot := List.isRotated_append (l := u ++ p) (l' := none :: q)
      exact Cycle.coe_eq_coe.mpr (by simpa [List.append_assoc] using hrot)
    have he := anchored_coe_injective
      ((anchored_perm hw).nodup_iff.mpr (extended A).nodup_toList) hroot
    refine ⟨q.filterMap id, u.filterMap id, p.filterMap id, ?_, unsome_perm hu⟩
    have hh := congrArg (List.filterMap id) he
    simpa using hh
  · rintro ⟨p, u, v, rfl, hu⟩
    let r := v.map some ++ none :: p.map some
    have hrot : (none :: (p ++ u ++ v).map some : List (Option α)) =
        (u.map some ++ r : Cycle (Option α)) := by
      have h := List.isRotated_append (l := none :: p.map some)
        (l' := u.map some ++ v.map some)
      exact Cycle.coe_eq_coe.mpr (by simpa [r, List.map_append, List.append_assoc] using h)
    have hp : (u.map some ++ r).Perm (extended A).toList :=
      (Cycle.coe_eq_coe.mp hrot).perm.symm.trans (anchored_perm hw)
    exact ⟨u.map some, r, some_perm hu, remainder_perm hp (some_perm hu), hrot⟩

/-- Rooting at the separator and cutting at the block are actual inverse bijections. -/
private def linearCircleEquiv (A S : Finset α) (hs : S ⊆ A) :
    {w : List α // w ∈ (orders A).filter (Block S)} ≃
      {C : Cycle (Option α) // Arc (extended A) (S.image some) C} := by
  let f : {w : List α // w ∈ (orders A).filter (Block S)} →
      {C : Cycle (Option α) // Arc (extended A) (S.image some) C} := fun w =>
    ⟨(none :: w.val.map some : List (Option α)),
      (arc_iff_block hs (mem_orders.mp (mem_filter.mp w.property).1)).mpr
        (mem_filter.mp w.property).2⟩
  apply Equiv.ofBijective f
  constructor
  · intro w v he
    have hroot := congrArg Subtype.val he
    have hh := anchored_coe_injective
      ((anchored_perm (mem_orders.mp (mem_filter.mp w.property).1)).nodup_iff.mpr
        (extended A).nodup_toList) hroot
    exact Subtype.ext (List.map_injective_iff.mpr (Option.some_injective α) hh)
  · intro c
    obtain ⟨v, hv⟩ := (anchorEquiv (extended A) none (by simp [extended])).surjective
      ⟨c.val, arc_mem_circles (some_subset hs) c.property⟩
    have hroot : (none :: v.val : List (Option α)) = c.val := congrArg Subtype.val hv
    have hvp : v.val.Perm (A.image some).toList := by
      have h := mem_orders.mp v.property
      simpa [extended] using h
    have hn : none ∉ v.val := by
      intro h
      have := hvp.mem_iff.mp h
      simpa using this
    let w := v.val.filterMap id
    have hw : w.Perm A.toList := unsome_perm hvp
    have he : w.map some = v.val := map_some_unsome hn
    have harc : Arc (extended A) (S.image some)
        (none :: w.map some : List (Option α)) := by rw [he, hroot]; exact c.property
    refine ⟨⟨w, mem_filter.mpr ⟨mem_orders.mpr hw, (arc_iff_block hs hw).mp harc⟩⟩, ?_⟩
    apply Subtype.ext
    change (none :: w.map some : List (Option α)) = c.val
    rw [he, hroot]

/-- Exactly k! (n-k+1)! original permutations have the prescribed nonempty block.
The proof composes linearCircleEquiv with the existing actual twoBlockEquiv. -/
theorem block_card (A S : Finset α) (hs : S ⊆ A) (hne : S.Nonempty) :
    ((orders A).filter (Block S)).card = S.card.factorial *
      (A.card - S.card + 1).factorial := by
  have he := Nat.card_congr (linearCircleEquiv A S hs)
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at he
  have hsome : (S.image some).Nonempty := hne.image some
  have hcomp : (extended A \ S.image some).Nonempty := ⟨none, by simp [extended]⟩
  have hc := arc_card (extended A) (S.image some) (some_subset hs) hsome hcomp
  have hsc : (S.image some).card = S.card := card_image_of_injective _ (Option.some_injective α)
  have hac : (extended A).card = A.card + 1 := by
    simp [extended, card_image_of_injective _ (Option.some_injective α)]
  have hcc : (extended A \ S.image some).card = A.card - S.card + 1 := by
    rw [card_sdiff_of_subset (some_subset hs), hac, hsc]
    have := card_le_card hs
    omega
  exact he.trans (by simpa [hsc, hcc] using hc)

/-- An indexed finite forbidden family is avoidable below the first-moment bound,
or at equality when one actual order has two different forbidden incidences. -/
theorem exists_avoiding (A : Finset α) {ι : Type*} [Fintype ι]
    (H : ι → Finset α) (hs : ∀ i, H i ⊆ A) (hne : ∀ i, (H i).Nonempty)
    (hbound : (∑ i, (H i).card.factorial * (A.card - (H i).card + 1).factorial) <
        A.card.factorial ∨
      ((∑ i, (H i).card.factorial * (A.card - (H i).card + 1).factorial) ≤
        A.card.factorial ∧ ∃ w ∈ orders A, ∃ i j, i ≠ j ∧ Block (H i) w ∧ Block (H j) w)) :
    ∃ w ∈ orders A, ∀ i, ¬ Block (H i) w := by
  let b (w : List α) := (univ.filter (fun i => Block (H i) w)).card
  have hi : (∑ w ∈ orders A, b w) =
      ∑ i, (H i).card.factorial * (A.card - (H i).card + 1).factorial := by
    calc
      _ = ∑ i, ((orders A).filter (Block (H i))).card := by
        simpa [b, Finset.bipartiteAbove, Finset.bipartiteBelow] using
          (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
            (s := orders A) (t := univ) (fun (w : List α) (i : ι) => Block (H i) w))
      _ = _ := sum_congr rfl (fun i _ => block_card A (H i) (hs i) (hne i))
  by_contra hn
  have hb : ∀ w ∈ orders A, 1 ≤ b w := by
    intro w hw
    have he : ∃ i, Block (H i) w := by
      by_contra hh
      exact hn ⟨w, hw, not_exists.mp hh⟩
    obtain ⟨i, hi⟩ := he
    exact one_le_card.mpr ⟨i, by simp [b, hi]⟩
  have hlo : A.card.factorial ≤
      ∑ i, (H i).card.factorial * (A.card - (H i).card + 1).factorial := by
    rw [← hi, ← orders_card A]
    simpa using (sum_le_sum hb)
  rcases hbound with hlt | ⟨hle, w, hw, i, j, hij, hbi, hbj⟩
  · omega
  · have htwo : 1 < b w := one_lt_card.mpr
      ⟨i, by simp [b, hbi], j, by simp [b, hbj], hij⟩
    have hlt : A.card.factorial <
        ∑ i, (H i).card.factorial * (A.card - (H i).card + 1).factorial := by
      rw [← hi, ← orders_card A]
      simpa using (sum_lt_sum hb ⟨w, hw, htwo⟩)
    omega

private theorem erase_cons_perm (S : Finset α) {p : α} (hp : p ∈ S) :
    (p :: (S.erase p).toList).Perm S.toList := by
  apply (List.perm_ext_iff_of_nodup
    (List.nodup_cons.mpr ⟨by simp, (S.erase p).nodup_toList⟩) S.nodup_toList).mpr
  intro x
  by_cases h : x = p <;> simp_all

/-- Two original sets meeting in exactly one point can both be literal blocks
of the SAME actual permutation. This is an overlap witness, not an avoiding order. -/
theorem two_intersecting_blocks (A S T : Finset α) (hs : S ⊆ A) (ht : T ⊆ A)
    (p : α) (hinter : S ∩ T = {p}) :
    ∃ w ∈ orders A, Block S w ∧ Block T w := by
  have hp := mem_inter.mp (hinter.symm ▸ mem_singleton_self p)
  have hcross : ∀ x, x ∈ S → x ∈ T → x = p := by
    intro x hx hy
    exact mem_singleton.mp (hinter ▸ mem_inter.mpr ⟨hx, hy⟩)
  have he : (S ∪ T) \ S = T.erase p := by
    ext x
    simp only [mem_sdiff, mem_union, mem_erase]
    constructor
    · rintro ⟨hx, hn⟩
      exact ⟨by rintro rfl; exact hn hp.1, hx.resolve_left hn⟩
    · rintro ⟨hn, hx⟩
      exact ⟨Or.inr hx, fun h => hn (hcross x h hx)⟩
  have hS : ((S.erase p).toList ++ [p]).Perm S.toList :=
    List.perm_append_comm.trans (erase_cons_perm S hp.1)
  have hT := erase_cons_perm T hp.2
  have hst : (((S.erase p).toList ++ [p]) ++ (T.erase p).toList).Perm (S ∪ T).toList :=
    append_order subset_union_left hS (by simpa [he] using List.Perm.refl (T.erase p).toList)
  have hw := append_order (union_subset hs ht) hst
    (List.Perm.refl (A \ (S ∪ T)).toList)
  refine ⟨_, mem_orders.mpr hw, ?_, ?_⟩
  · exact ⟨[], (S.erase p).toList ++ [p],
      (T.erase p).toList ++ (A \ (S ∪ T)).toList, by simp [List.append_assoc], hS⟩
  · exact ⟨(S.erase p).toList, p :: (T.erase p).toList,
      (A \ (S ∪ T)).toList, by simp [List.append_assoc], hT⟩

end D5.S3.Combinatorics.Permutation.ForbiddenContiguousBlocks
