/- GID: D5/S3/Arith/GoldenResource/DivisorAssociationFiber
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/DivisorAssociationFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four-block association fibers have exact hidden-label intervals and a canonical quotient count. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.GoldenResource.DivisorAssociationFiber

open scoped BigOperators

/-- Independent exponents of the four arithmetic blocks. -/
abbrev Source := ℕ × ℕ × ℕ × ℕ

/-- The three observed association coordinates. -/
abbrev Position := ℕ × ℕ × ℕ

/-- A finite exponent box, allowing zero side lengths. -/
def box (A B C D : ℕ) : Finset Source :=
  Finset.range (A + 1) ×ˢ (Finset.range (B + 1) ×ˢ
    (Finset.range (C + 1) ×ˢ Finset.range (D + 1)))

/-- A joint first-and-third block contributes to both observed coordinates. -/
def q (s : Source) : Position := (s.1 + s.2.2.2, s.2.1, s.2.2.1 + s.2.2.2)

/-- Sources with exactly the prescribed observed position. -/
def fiber (A B C D : ℕ) (y : Position) : Finset Source :=
  (box A B C D).filter (fun s => q s = y)

/-- The smallest admissible hidden exponent; subtraction is natural subtraction. -/
def lower (A C : ℕ) (y : Position) : ℕ := max (y.1 - A) (y.2.2 - C)

/-- The largest admissible hidden exponent. -/
def upper (D : ℕ) (y : Position) : ℕ := min D (min y.1 y.2.2)

/-- The exact finite hidden-label interval, including the second-coordinate constraint. -/
def labels (A B C D : ℕ) (y : Position) : Finset ℕ :=
  if y.2.1 ≤ B then Finset.Icc (lower A C y) (upper D y) else ∅

/-- Restoring a source from a position and a valid hidden exponent. -/
def decode (y : Position) (k : ℕ) : Source := (y.1 - k, y.2.1, y.2.2 - k, k)

private theorem mem_fiber_iff (A B C D : ℕ) (y : Position) (s : Source) :
    s ∈ fiber A B C D y ↔
      s.1 ≤ A ∧ s.2.1 ≤ B ∧ s.2.2.1 ≤ C ∧ s.2.2.2 ≤ D ∧
        s.1 + s.2.2.2 = y.1 ∧ s.2.1 = y.2.1 ∧ s.2.2.1 + s.2.2.2 = y.2.2 := by
  rcases s with ⟨a, b, c, k⟩
  rcases y with ⟨u, v, w⟩
  simp only [fiber, box, q, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range, Prod.ext_iff]
  try dsimp at *
  omega

private theorem mem_labels_iff (A B C D : ℕ) (y : Position) (k : ℕ) :
    k ∈ labels A B C D y ↔
      y.2.1 ≤ B ∧ k ≤ D ∧ k ≤ y.1 ∧ k ≤ y.2.2 ∧
        y.1 - k ≤ A ∧ y.2.2 - k ≤ C := by
  rcases y with ⟨u, v, w⟩
  by_cases hv : v ≤ B
  · simp only [labels, hv, if_true, Finset.mem_Icc, lower, upper]
    simp only [max_le_iff, le_min_iff]
    try dsimp at *
    simp only [Nat.sub_le_iff_le_add, true_and]
    constructor
    · rintro ⟨⟨hA, hC⟩, hD, hu, hw⟩
      exact ⟨hD, hu, hw, by simpa [Nat.add_comm] using hA,
        by simpa [Nat.add_comm] using hC⟩
    · rintro ⟨hD, hu, hw, hA, hC⟩
      exact ⟨⟨by simpa [Nat.add_comm] using hA,
        by simpa [Nat.add_comm] using hC⟩, hD, hu, hw⟩
  · simp [labels, hv]

private theorem decode_mem_fiber (A B C D : ℕ) (y : Position) (k : ℕ)
    (hk : k ∈ labels A B C D y) : decode y k ∈ fiber A B C D y := by
  obtain ⟨hv, hD, hu, hw, hA, hC⟩ := (mem_labels_iff A B C D y k).mp hk
  rw [mem_fiber_iff]
  exact ⟨hA, hv, hC, hD, Nat.sub_add_cancel hu, rfl, Nat.sub_add_cancel hw⟩

private theorem label_mem (A B C D : ℕ) (y : Position) (s : Source)
    (hs : s ∈ fiber A B C D y) : s.2.2.2 ∈ labels A B C D y := by
  obtain ⟨hA, hB, hC, hD, hu, hv, hw⟩ := (mem_fiber_iff A B C D y s).mp hs
  rw [mem_labels_iff]
  try dsimp at *
  omega

private theorem decode_label (A B C D : ℕ) (y : Position) (s : Source)
    (hs : s ∈ fiber A B C D y) : decode y s.2.2.2 = s := by
  obtain ⟨hA, hB, hC, hD, hu, hv, hw⟩ := (mem_fiber_iff A B C D y s).mp hs
  rcases s with ⟨a, b, c, k⟩
  rcases y with ⟨u, v, w⟩
  simp only [decode, Prod.ext_iff]
  dsimp at hu hv hw
  rw [← hu, ← hv, ← hw]
  simp

/-- The hidden exponent parametrizes each entire source fiber, including empty fibers. -/
def fiberEquiv (A B C D : ℕ) (y : Position) :
    {s // s ∈ fiber A B C D y} ≃ {k // k ∈ labels A B C D y} where
  toFun s := ⟨s.val.2.2.2, label_mem A B C D y s.val s.property⟩
  invFun k := ⟨decode y k.val, decode_mem_fiber A B C D y k.val k.property⟩
  left_inv s := Subtype.ext (decode_label A B C D y s.val s.property)
  right_inv _k := rfl

/-- Every position's source multiplicity is an explicit interval length. -/
private theorem fiber_card (A B C D : ℕ) (y : Position) :
    (fiber A B C D y).card =
      if y.2.1 ≤ B then upper D y + 1 - lower A C y else 0 := by
  have h := Fintype.card_congr (fiberEquiv A B C D y)
  simp only [Fintype.card_coe] at h
  by_cases hv : y.2.1 ≤ B <;> simpa [labels, hv] using h

/-- A position has a source precisely when all interval and vertical constraints hold. -/
private theorem fiber_nonempty_iff (A B C D : ℕ) (y : Position) :
    (fiber A B C D y).Nonempty ↔ y.2.1 ≤ B ∧ lower A C y ≤ upper D y := by
  rw [← Finset.card_pos, fiber_card]
  by_cases hv : y.2.1 ≤ B <;> simp only [hv, if_true, if_false, true_and, false_and]
  · omega
  · simp

/-- The unique boundary representative has the greatest hidden exponent in its fiber. -/
def boundary (A B C D : ℕ) : Finset Source :=
  (box A B C D).filter (fun s => s.2.2.2 = D ∨ s.1 = 0 ∨ s.2.2.1 = 0)

private theorem mem_box_iff (A B C D : ℕ) (s : Source) :
    s ∈ box A B C D ↔
      s.1 ≤ A ∧ s.2.1 ≤ B ∧ s.2.2.1 ≤ C ∧ s.2.2.2 ≤ D := by
  rcases s with ⟨a, b, c, k⟩
  simp only [box, Finset.mem_product, Finset.mem_range]
  try dsimp at *
  omega

private theorem boundary_label (A B C D : ℕ) (s : Source)
    (hs : s ∈ boundary A B C D) : s.2.2.2 = upper D (q s) := by
  simp only [boundary, Finset.mem_filter, mem_box_iff] at hs
  simp only [upper, q]
  try dsimp at *
  omega

private theorem boundary_injective (A B C D : ℕ) :
    Set.InjOn q (boundary A B C D) := by
  intro s hs t ht hq
  have hlabel : s.2.2.2 = t.2.2.2 :=
    (boundary_label A B C D s hs).trans
      ((congrArg (upper D) hq).trans (boundary_label A B C D t ht).symm)
  simp only [q, Prod.ext_iff] at hq ⊢
  try dsimp at *
  omega

private theorem boundary_image (A B C D : ℕ) :
    (boundary A B C D).image q = (box A B C D).image q := by
  apply Finset.Subset.antisymm
  · exact Finset.image_subset_image (Finset.filter_subset _ _)
  · intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    have hsf : s ∈ fiber A B C D (q s) := Finset.mem_filter.mpr ⟨hs, rfl⟩
    have hnon : (fiber A B C D (q s)).Nonempty := ⟨s, hsf⟩
    obtain ⟨hv, hinterval⟩ := (fiber_nonempty_iff A B C D (q s)).mp hnon
    have hk : upper D (q s) ∈ labels A B C D (q s) := by
      simp only [labels, hv, if_true, Finset.mem_Icc]
      exact ⟨hinterval, le_rfl⟩
    have ht := decode_mem_fiber A B C D (q s) (upper D (q s)) hk
    have hqt : q (decode (q s) (upper D (q s))) = q s :=
      (Finset.mem_filter.mp ht).2
    refine Finset.mem_image.mpr ⟨decode (q s) (upper D (q s)), ?_, hqt⟩
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1, ?_⟩
    simp only [decode, upper, q]
    try dsimp at *
    omega

private theorem interior_eq (A B C D : ℕ) :
    (box A B C D).filter (fun s => ¬ (s.2.2.2 = D ∨ s.1 = 0 ∨ s.2.2.1 = 0)) =
      Finset.Icc 1 A ×ˢ (Finset.range (B + 1) ×ˢ
        (Finset.Icc 1 C ×ˢ Finset.range D)) := by
  ext s
  rcases s with ⟨a, b, c, k⟩
  simp only [Finset.mem_filter, mem_box_iff, Finset.mem_product,
    Finset.mem_Icc, Finset.mem_range]
  try dsimp at *
  omega

/-- Collapsing the diagonal association counts image points, rather than complete sources. -/
theorem image_card (A B C D : ℕ) :
    ((box A B C D).image q).card =
      (B + 1) * ((A + 1) * (C + 1) + D * (A + C + 1)) := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := box A B C D) (fun s : Source => s.2.2.2 = D ∨ s.1 = 0 ∨ s.2.2.1 = 0)
  rw [interior_eq] at hpartition
  have himage : ((box A B C D).image q).card = (boundary A B C D).card := by
    rw [← boundary_image]
    exact Finset.card_image_iff.mpr (boundary_injective A B C D)
  rw [himage]
  change (boundary A B C D).card + _ = _ at hpartition
  simp only [Finset.card_product, Nat.card_Icc, Finset.card_range,
    Nat.add_sub_cancel] at hpartition
  unfold box at hpartition
  simp only [Finset.card_product, Finset.card_range] at hpartition
  nlinarith [hpartition]

end D5.S3.Arith.GoldenResource.DivisorAssociationFiber
