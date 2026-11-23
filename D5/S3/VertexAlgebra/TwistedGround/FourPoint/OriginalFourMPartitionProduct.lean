/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPartitionProduct
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPartitionProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Products of independent correction endpoint partitions across punctures. -/

import D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickConvolution

/-! Independent positional partitions distribute over the puncture subwords,
with both sides of each partition keeping their induced order. -/

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMPartitionProduct

open AffineWickConvolution (partitions)

variable {X R : Type*} [CommSemiring R]

/-- A correction endpoint partition restricted to a selected subword. -/
def filterParts (p : X → Bool) (s : List X × List X) : List X × List X :=
  (s.1.filter p, s.2.filter p)

/-- Two independent subwords contribute the product of their finite sums
over endpoint partitions. -/
theorem partition_product (l : List X) (p : X → Bool) (f g : List X × List X → R) :
    ((partitions l).map fun s => f (filterParts p s) *
      g (filterParts (fun a => !p a) s)).sum =
      ((partitions (l.filter p)).map f).sum *
        ((partitions (l.filter fun a => !p a)).map g).sum := by
  induction l generalizing f g with
  | nil => simp [partitions, filterParts]
  | cons a l ih =>
    cases h : p a
    · simp only [partitions, List.map_append, List.map_map, List.sum_append, Function.comp_def,
        filterParts, List.filter_cons, h, Bool.false_eq_true, Bool.not_false, ite_false, ite_true]
      rw [mul_add, ← ih f (fun s => g (a :: s.1, s.2)),
        ← ih f (fun s => g (s.1, a :: s.2))]
      rfl
    · simp only [partitions, List.map_append, List.map_map, List.sum_append, Function.comp_def,
        filterParts, List.filter_cons, h, Bool.false_eq_true, Bool.not_true, ite_false, ite_true]
      rw [add_mul, ← ih (fun s => f (a :: s.1, s.2)) g,
        ← ih (fun s => f (s.1, a :: s.2)) g]
      rfl

/-- The sum over all correction endpoint partitions factors into the
per-puncture sums when each factor sees only its own subword. -/
theorem partition_products {S : Type*} [DecidableEq S]
    (slot : X → S) (s : Finset S) (l : List X)
    (hs : ∀ a ∈ l, slot a ∈ s) (F : S → List X × List X → R) :
    ((partitions l).map fun p => ∏ i ∈ s, F i (filterParts (fun a => decide (slot a = i)) p)).sum =
      ∏ i ∈ s, ((partitions (l.filter fun a => decide (slot a = i))).map (F i)).sum := by
  induction s using Finset.induction_on generalizing l with
  | empty =>
    cases l with
    | nil => simp [partitions]
    | cons a l => exact (Finset.notMem_empty (slot a) (hs a List.mem_cons_self)).elim
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    let p : X → Bool := fun a => decide (slot a = i)
    let G (w : List X × List X) :=
      ∏ j ∈ s, F j (filterParts (fun a => decide (slot a = j)) w)
    have hG (w : List X × List X) : G w = G (filterParts (fun a => !p a) w) := by
      unfold G
      apply Finset.prod_congr rfl
      intro j hj
      congr 1
      have he (w : List X) : w.filter (fun a => decide (slot a = j)) =
          (w.filter (fun a => !p a)).filter (fun a => decide (slot a = j)) := by
        rw [List.filter_filter]
        apply List.filter_congr
        intro a _
        by_cases ha : slot a = j
        · have hji : j ≠ i := fun he => hi (he ▸ hj)
          simp [p, ha, hji]
        · simp [ha]
      exact Prod.ext (he w.1) (he w.2)
    change ((partitions l).map fun w => F i (filterParts p w) * G w).sum = _
    have he : ((partitions l).map fun w => F i (filterParts p w) * G w).sum =
        ((partitions l).map fun w => F i (filterParts p w) * G (filterParts (fun a => !p a) w)).sum :=
      congrArg List.sum (List.map_congr_left fun w _ => congrArg (F i (filterParts p w) * ·) (hG w))
    rw [he, partition_product l p (F i) G]
    have hc : ∀ a ∈ l.filter (fun a => !p a), slot a ∈ s := by
      intro a ha
      have h := List.mem_filter.mp ha
      exact (Finset.mem_insert.mp (hs a h.1)).resolve_left (by simpa [p] using h.2)
    unfold G
    rw [ih _ hc]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    congr 3
    rw [List.filter_filter]
    apply List.filter_congr
    intro a _
    by_cases ha : slot a = j
    · have hji : j ≠ i := fun he => hi (he ▸ hj)
      simp [p, ha, hji]
    · simp [ha]

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMPartitionProduct
