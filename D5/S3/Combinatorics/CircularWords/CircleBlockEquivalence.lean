/- GID: D5/S3/Combinatorics/CircularWords/CircleBlockEquivalence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CircularWords/CircleBlockEquivalence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.List.Cycle]
   utility: none
   digest: Contraction of one original-label run preserving disjoint circular arc events. -/

import D5.S3.Combinatorics.CircularWords.CircularOrderCount
import D5.S3.Combinatorics.CircularWords.CyclicInsertionGap

/-! A retained original label serves as marker; all other blocks stay on the same circle. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.CircularWords.CircleBlockEquivalence

open D5.S3.Combinatorics.CircularWords.DisjointBlockContraction
open D5.S3.Combinatorics.CircularWords.CircularOrderCount
open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
open D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
open Finset

universe u
variable {α : Type u} [DecidableEq α]
noncomputable section
open scoped Classical

private theorem anchor_tail_perm {A : Finset α} {a : α} {v : List α}
    (hp : (a::v).Perm A.toList) : v.Perm (A.erase a).toList := by
  have hn := hp.nodup_iff.mpr A.nodup_toList
  apply (List.perm_ext_iff_of_nodup hn.tail (A.erase a).nodup_toList).mpr
  intro x
  simp only [mem_toList, mem_erase]
  constructor
  · intro hx
    exact ⟨by rintro rfl; exact (List.nodup_cons.mp hn).1 hx,
      mem_toList.mp (hp.mem_iff.mp (List.mem_cons_of_mem a hx))⟩
  · rintro ⟨hne,hx⟩
    have hh := hp.mem_iff.mpr (mem_toList.mpr hx)
    exact (List.mem_cons.mp hh).resolve_left hne

private theorem anchor_cons_perm {A : Finset α} {a : α} (ha : a ∈ A)
    {v : List α} (hv : v.Perm (A.erase a).toList) : (a::v).Perm A.toList := by
  have hn : (a::v).Nodup := by
    refine List.nodup_cons.mpr ⟨?_,hv.nodup_iff.mpr (A.erase a).nodup_toList⟩
    intro h
    exact (mem_erase.mp (mem_toList.mp (hv.mem_iff.mp h))).1 rfl
  apply (List.perm_ext_iff_of_nodup hn A.nodup_toList).mpr
  intro x
  simp only [List.mem_cons, hv.mem_iff, mem_toList, mem_erase]
  exact ⟨fun h => h.elim (fun h => h ▸ ha) And.right,
    fun h => (em (x=a)).elim Or.inl (fun hn => Or.inr ⟨hn,h⟩)⟩

/-- Actual boundary-rooted orders enumerate precisely the oriented circles through the anchor. -/
noncomputable def anchorEquiv (A : Finset α) (a : α) (ha : a ∈ A) :
    {v : List α // v ∈ orders (A.erase a)} ≃ {C : Cycle α // C ∈ circles A} := by
  let F : {v : List α // v ∈ orders (A.erase a)} → {C : Cycle α // C ∈ circles A} :=
    fun v => ⟨(a::v.val : List α), mem_image.mpr
      ⟨a::v.val, mem_orders.mpr (anchor_cons_perm ha (mem_orders.mp v.property)),rfl⟩⟩
  apply Equiv.ofBijective F
  constructor
  · intro v w h
    apply Subtype.ext
    exact anchored_coe_injective
      ((anchor_cons_perm ha (mem_orders.mp v.property)).nodup_iff.mpr A.nodup_toList)
      (congrArg Subtype.val h)
  · rintro ⟨C,hC⟩
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hC
    have hp := mem_orders.mp hw
    obtain ⟨l,k,hk⟩ := List.mem_iff_append.mp (hp.mem_iff.mpr (mem_toList.mpr ha))
    have hr : (w : Cycle α) = (a::(k++l) : List α) := by
      rw [hk]
      exact Cycle.coe_eq_coe.mpr List.isRotated_append
    have hperm : (a::(k++l)).Perm A.toList :=
      (Cycle.coe_eq_coe.mp hr).perm.symm.trans hp
    refine ⟨⟨k++l,mem_orders.mpr (anchor_tail_perm hperm)⟩,?_⟩
    exact Subtype.ext hr.symm

/-- A Boolean restriction transports every prescribed arc in its original orientation. -/
theorem arc_restrict (p : α → Bool) {A S : Finset α} {C : Cycle α}
    (hC : Arc A S C) : Arc (A.filter (fun x => p x = true)) (S.filter (fun x => p x = true)) (restrict p C) := by
  have hp (B : Finset α) : (B.toList.filter p).Perm (B.filter (fun x => p x = true)).toList := by
    apply (List.perm_ext_iff_of_nodup (B.nodup_toList.filter p) (B.filter (fun x => p x = true)).nodup_toList).mpr
    simp
  obtain ⟨l,k,hl,hk,rfl⟩ := hC
  refine ⟨l.filter p,k.filter p,(hl.filter p).trans (hp S),?_,?_⟩
  · have he : (A \ S).filter (fun x => p x = true) = A.filter (fun x => p x = true) \ S.filter (fun x => p x = true) := by
      ext x
      cases hx : p x <;> simp [hx]
    simpa only [he] using (hk.filter p).trans (hp (A \ S))
  · change ((l++k).filter p : Cycle α) = _
    rw [List.filter_append]

/-- Contracting a run keeps one original label as its unique marker. -/
def contracted (A S : Finset α) (a : α) : Finset α := insert a (A \ S)

/-- Expand the marker back to the recorded actual internal order. -/
def inflate (a : α) (l : List α) : Cycle α → Cycle α :=
  expand (fun x => if x=a then l else [x])

private theorem inflate_list {a : α} {l v : List α} (hv : a ∉ v) :
    v.flatMap (fun x => if x=a then l else [x]) = v := by
  calc
    _ = v.flatMap (fun x => [x]) := by
      apply List.flatMap_congr
      intro x hx
      simp [show x ≠ a by rintro rfl; exact hv hx]
    _ = v := List.flatMap_singleton' v

/-- The boundary contraction and expansion are actual mutually inverse maps. -/
noncomputable def blockEquiv (A S : Finset α) (hS : S ⊆ A)
    (hs : S.Nonempty) (hv : (A \ S).Nonempty) (a : α) (ha : a ∈ S) :
    ({l : List α // l ∈ orders S} ×
      {C : Cycle α // C ∈ circles (contracted A S a)}) ≃
      {C : Cycle α // Arc A S C} := by
  have he : (contracted A S a).erase a = A \ S := by
    ext x
    simp only [contracted, mem_erase, mem_insert, mem_sdiff]
    constructor
    · rintro ⟨hne,he|hh⟩
      · exact False.elim (hne he)
      · exact hh
    · rintro hh
      exact ⟨by rintro rfl; exact hh.2 ha,Or.inr hh⟩
  let e : {v : List α // v ∈ orders (A \ S)} ≃
      {C : Cycle α // C ∈ circles (contracted A S a)} :=
    (Equiv.subtypeEquivRight (fun v => by rw [he])).trans
      (anchorEquiv (contracted A S a) a (by simp [contracted]))
  exact (Equiv.prodCongr (Equiv.refl _) e.symm).trans (twoBlockEquiv A S hS hs hv)

/-- The equivalence expands the unique marker, rather than replacing the event inventory. -/
theorem blockEquiv_expand (A S : Finset α) (hS : S ⊆ A)
    (hs : S.Nonempty) (hv : (A \ S).Nonempty) (a : α) (ha : a ∈ S)
    (z : {l : List α // l ∈ orders S} ×
      {C : Cycle α // C ∈ circles (contracted A S a)}) :
    (blockEquiv A S hS hs hv a ha z).val = inflate a z.1.val z.2.val := by
  let e := anchorEquiv (contracted A S a) a (by simp [contracted])
  let v := e.symm z.2
  have he : (a::v.val : List α) = z.2.val := congrArg Subtype.val (e.apply_symm_apply z.2)
  have hn : a ∉ v.val := by
    intro h
    exact (mem_erase.mp (mem_toList.mp ((mem_orders.mp v.property).mem_iff.mp h))).1 rfl
  change (z.1.val ++ v.val : List α) = inflate a z.1.val z.2.val
  rw [← he]
  change _ = ((a::v.val).flatMap (fun x => if x=a then z.1.val else [x]) : Cycle α)
  simp only [List.flatMap_cons, eq_self_iff_true, ite_true, inflate_list hn]

/-- Expansion preserves every disjoint prescribed arc on the same circle. -/
theorem arc_inflate {A S T : Finset α} (hS : S ⊆ A) (hT : T ⊆ A \ S)
    {a : α} (ha : a ∈ S) {l : List α} (hl : l.Perm S.toList)
    {C : Cycle α} (hC : Arc (contracted A S a) T C) : Arc A T (inflate a l C) := by
  obtain ⟨u,v,hu,hv,rfl⟩ := hC
  have hTa : a ∉ T := fun h => (mem_sdiff.mp (hT h)).2 ha
  have hua : a ∉ u := fun h => hTa (mem_toList.mp (hu.mem_iff.mp h))
  have hSA : S ⊆ A \ T := by
    intro x hx
    exact mem_sdiff.mpr ⟨hS hx,fun ht => (mem_sdiff.mp (hT ht)).2 hx⟩
  let R := (A \ T) \ S
  have hRa : a ∉ R := by simp [R,ha]
  have he : contracted A S a \ T = insert a R := by
    ext x
    simp only [contracted,R,mem_sdiff,mem_insert]
    constructor
    · rintro ⟨hxa|hx,hxt⟩
      · exact Or.inl hxa
      · exact Or.inr ⟨⟨hx.1,hxt⟩,hx.2⟩
    · rintro (rfl|hx)
      · exact ⟨Or.inl rfl,hTa⟩
      · exact ⟨Or.inr ⟨hx.1.1,hx.2⟩,hx.1.2⟩
  have hvp : v.Perm (a::R.toList) := by
    rw [he] at hv
    exact hv.trans (Finset.toList_insert hRa)
  have hflat : (v.flatMap (fun x => if x=a then l else [x])).Perm (A \ T).toList := by
    have hh := hvp.flatMap_right (fun x => if x=a then l else [x])
    simp only [List.flatMap_cons, eq_self_iff_true, ite_true,
      inflate_list (by simpa using hRa : a ∉ R.toList)] at hh
    exact hh.trans (append_order hSA hl (List.Perm.refl _))
  refine ⟨u, v.flatMap (fun x => if x=a then l else [x]),hu,hflat,?_⟩
  change ((u++v).flatMap (fun x => if x=a then l else [x]) : Cycle α) = _
  rw [List.flatMap_append, inflate_list hua]

/-- The retained head and unchanged residual letters recover the contracted circle. -/
theorem restrict_inflate {A S : Finset α} {a : α} (ha : a ∈ S)
    {l : List α} (hl : l.Perm S.toList) {C : Cycle α}
    (hC : C ∈ circles (contracted A S a)) :
    restrict (fun x => decide (x ∉ S ∨ x=a)) (inflate a l C) = C := by
  have hlfilter : l.filter (fun x => decide (x ∉ S ∨ x=a)) = [a] := by
    have he : l.filter (fun x => decide (x ∉ S ∨ x=a)) =
        l.filter (fun x => decide (x=a)) := by
      apply List.filter_congr
      intro x hx
      simp [mem_toList.mp (hl.mem_iff.mp hx)]
    rw [he, List.filter_eq, List.count_eq_one_of_mem
      (hl.nodup_iff.mpr S.nodup_toList) (hl.mem_iff.mpr (mem_toList.mpr ha))]
    rfl
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hC
  rw [inflate, restrict_expand]
  change ((w.flatMap (fun b => (if b=a then l else [b]).filter
    (fun x => decide (x ∉ S ∨ x=a))) : List α) : Cycle α) = (w : Cycle α)
  have hf : w.flatMap (fun b => (if b=a then l else [b]).filter
      (fun x => decide (x ∉ S ∨ x=a))) = w := by
    calc
      _ = w.flatMap (fun x => [x]) := by
        apply List.flatMap_congr
        intro x hx
        by_cases hxa : x=a
        · subst x
          simp only [ite_true]
          exact hlfilter
        · have hxA := mem_toList.mp ((mem_orders.mp hw).mem_iff.mp hx)
          have hxs : x ∉ S := (mem_sdiff.mp ((mem_insert.mp hxA).resolve_left hxa)).2
          simp [hxa,hxs]
      _ = w := List.flatMap_singleton' w
  rw [hf]

/-- Disjoint-arc membership is reflected as well as preserved by actual expansion. -/
theorem arc_inflate_iff {A S T : Finset α} (hS : S ⊆ A) (hT : T ⊆ A \ S)
    {a : α} (ha : a ∈ S) {l : List α} (hl : l.Perm S.toList)
    {C : Cycle α} (hC : C ∈ circles (contracted A S a)) :
    Arc A T (inflate a l C) ↔ Arc (contracted A S a) T C := by
  constructor
  · intro h
    have hh := arc_restrict (fun x => decide (x ∉ S ∨ x=a)) h
    rw [restrict_inflate ha hl hC] at hh
    have heA : A.filter (fun x => decide (x ∉ S ∨ x=a)) = contracted A S a := by
      ext x
      simp only [contracted,mem_filter,decide_eq_true_eq,mem_insert,mem_sdiff]
      constructor
      · rintro ⟨hx,hxs|hxa⟩
        · exact Or.inr ⟨hx,hxs⟩
        · exact Or.inl hxa
      · rintro (rfl|hx)
        · exact ⟨hS ha,Or.inr rfl⟩
        · exact ⟨hx.1,Or.inl hx.2⟩
    have heT : T.filter (fun x => decide (x ∉ S ∨ x=a)) = T := by
      ext x
      simp only [mem_filter,decide_eq_true_eq,and_iff_left_iff_imp]
      exact fun hx => Or.inl (mem_sdiff.mp (hT hx)).2
    simpa only [heA,heT] using hh
  · exact arc_inflate hS hT ha hl

end
end D5.S3.Combinatorics.CircularWords.CircleBlockEquivalence
