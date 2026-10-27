/- GID: D5/S3/Combinatorics/CircularWords/CircularOrderCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CircularWords/CircularOrderCount
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.List.Cycle]
   utility: none
   digest: Free rotation fibers normalize actual finite original-label order inventories. -/

import D5.S3.Combinatorics.CircularWords.DisjointBlockContraction

/-! Every circle is an actual oriented rotation class; no reversal quotient is taken. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.CircularWords.CircularOrderCount

open D5.S3.Combinatorics.CircularWords.DisjointBlockContraction
open Finset

universe u
variable {α : Type u} [DecidableEq α]

noncomputable section
open scoped Classical

private theorem circle_fiber {A : Finset α} {w : List α} (hw : w ∈ orders A) :
    (orders A).filter (fun (k : List α) => (k : Cycle α) = (w : Cycle α)) =
      w.cyclicPermutations.toFinset := by
  ext k
  simp only [mem_filter, List.mem_toFinset, List.mem_cyclicPermutations_iff]
  constructor
  · rintro ⟨_,h⟩
    exact Cycle.coe_eq_coe.mp h
  · intro h
    exact ⟨mem_orders.mpr (h.perm.trans (mem_orders.mp hw)), Cycle.coe_eq_coe.mpr h⟩

/-- Distinct original labels make every nonempty rotation fiber free of repetitions. -/
theorem circle_fiber_card (A : Finset α) (hA : A.Nonempty)
    (C : Cycle α) (hC : C ∈ circles A) :
    ((orders A).filter (fun (k : List α) => (k : Cycle α) = C)).card = A.card := by
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hC
  have hp := mem_orders.mp hw
  have hn : w.Nodup := hp.nodup_iff.mpr A.nodup_toList
  have hne : w ≠ [] := by
    apply List.length_pos_iff.mp
    rw [hp.length_eq, length_toList]
    exact hA.card_pos
  rw [circle_fiber hw, List.toFinset_card_of_nodup hn.cyclicPermutations,
    List.length_cyclicPermutations_of_ne_nil w hne, hp.length_eq, length_toList]

/-- The directed cyclic quotient has exactly (n-1)! elements. -/
theorem circles_card (A : Finset α) (hA : A.Nonempty) :
    (circles A).card = (A.card-1).factorial := by
  have hh : (orders A).card = (circles A).card * A.card := by
    calc
      (orders A).card = ∑ C ∈ circles A, ((orders A).filter
          (fun (k : List α) => (k : Cycle α) = C)).card :=
        card_eq_sum_card_image Cycle.ofList (orders A)
      _ = ∑ _C ∈ circles A, A.card :=
        sum_congr rfl (fun C hC => circle_fiber_card A hA C hC)
      _ = _ := by simp
  rw [orders_card] at hh
  have hf := Nat.mul_factorial_pred (Nat.ne_of_gt hA.card_pos)
  exact Nat.eq_of_mul_eq_mul_left hA.card_pos (by nlinarith [hf])

/-- A proper-arc witness really lies in the actual circle inventory. -/
theorem arc_mem_circles {A S : Finset α} (hS : S ⊆ A) {C : Cycle α}
    (h : Arc A S C) : C ∈ circles A := by
  obtain ⟨l,k,hl,hk,hC⟩ := h
  have hp := append_order hS hl hk
  exact mem_image.mpr ⟨l++k, mem_orders.mpr hp, hC.symm⟩

/-- The single-arc cardinal counts events on that very same finite circle space. -/
theorem arc_filter_card (A S : Finset α) (hS : S ⊆ A)
    (hs0 : S.Nonempty) (hv0 : (A \ S).Nonempty) :
    ((circles A).filter (Arc A S)).card = S.card.factorial * (A \ S).card.factorial := by
  let e : {C : Cycle α // C ∈ (circles A).filter (Arc A S)} ≃
      {C : Cycle α // Arc A S C} :=
    { toFun := fun C => ⟨C.val, (mem_filter.mp C.property).2⟩
      invFun := fun C => ⟨C.val, mem_filter.mpr ⟨arc_mem_circles hS C.property,C.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he := Nat.card_congr e
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at he
  exact he.trans (arc_card A S hS hs0 hv0)

/-- Every quotient event has exactly n original rooted words per circle. -/
theorem event_order_card (A : Finset α) (hA : A.Nonempty) (P : Cycle α → Prop) :
    ((orders A).filter (fun (w : List α) => P (w : Cycle α))).card =
      A.card * ((circles A).filter P).card := by
  have hi : ((orders A).filter (fun (w : List α) => P (w : Cycle α))).image Cycle.ofList =
      (circles A).filter P := by
    ext C
    simp only [mem_image,mem_filter,circles]
    constructor
    · rintro ⟨w,⟨hw,hp⟩,rfl⟩
      exact ⟨⟨w,hw,rfl⟩,hp⟩
    · rintro ⟨⟨w,hw,rfl⟩,hp⟩
      exact ⟨w,⟨hw,hp⟩,rfl⟩
  have hf (C : Cycle α) (hC : C ∈ (circles A).filter P) :
      (((orders A).filter (fun (w : List α) => P (w : Cycle α))).filter
        (fun (w : List α) => (w : Cycle α)=C)).card = A.card := by
    have he : ((orders A).filter (fun (w : List α) => P (w : Cycle α))).filter
        (fun (w : List α) => (w : Cycle α)=C) =
          (orders A).filter (fun (w : List α) => (w : Cycle α)=C) := by
      ext w
      simp only [mem_filter]
      constructor
      · exact fun h => ⟨h.1.1,h.2⟩
      · rintro ⟨hw,he⟩
        exact ⟨⟨hw,he ▸ (mem_filter.mp hC).2⟩,he⟩
    rw [he]
    exact circle_fiber_card A hA C (mem_filter.mp hC).1
  calc
    _ = ∑ C ∈ (circles A).filter P,
        (((orders A).filter (fun (w : List α) => P (w : Cycle α))).filter
          (fun (w : List α) => (w : Cycle α)=C)).card := by
      rw [←hi]
      exact card_eq_sum_card_image _ _
    _ = ∑ _C ∈ (circles A).filter P, A.card := sum_congr rfl hf
    _ = _ := by simp [Nat.mul_comm]


end
end D5.S3.Combinatorics.CircularWords.CircularOrderCount
