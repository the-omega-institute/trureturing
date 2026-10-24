/- GID: D5/S3/Combinatorics/CircularWords/CircleEventNormalization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CircularWords/CircleEventNormalization
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.List.Rotate]
   utility: none
   digest: Free-rotation normalization of actual finite circular event inventories. -/

import D5.S3.Combinatorics.CircularWords.CircularOrderCount

/-! Only predicates on the actual oriented rotation quotient are normalized. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.CircularWords.CircleEventNormalization

open D5.S3.Combinatorics.CircularWords.DisjointBlockContraction
open D5.S3.Combinatorics.CircularWords.CircularOrderCount
open Finset
open scoped Classical

universe u
variable {α : Type u} [DecidableEq α]

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

end D5.S3.Combinatorics.CircularWords.CircleEventNormalization
