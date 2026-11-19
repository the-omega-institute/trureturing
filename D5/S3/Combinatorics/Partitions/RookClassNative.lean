/- GID: D5/S3/Combinatorics/Partitions/RookClassNative
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/RookClassNative
   mirror-E: none(waiver:native-rook-class)
   anchors: []
   utility: none
   digest: Native m-level rook classes have finite carriers and a common normalized padding. -/

import D5.S3.Combinatorics.Partitions.BarreseSourceNormalization
import Mathlib.Data.Finset.Powerset

/-! Native finite cell-subset counts and the unrestricted normalized rook class. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Partitions.RookClassNative

open D5.S3.Combinatorics.Partitions.BarreseSourceNormalization

/-- Row coordinates increase upwards from the bottom; column coordinates increase
    from the right. Horizontal reflection changes no column conflict. -/
def cells (b : PositiveColumns) : Finset (ℕ × ℕ) :=
  (normalizedColumnsEquiv.symm b).cells

/-- Literal number of cells in the normalized source tuple. -/
def area (b : PositiveColumns) : ℕ := b.val.sum

private theorem cells_card (b : PositiveColumns) : (cells b).card = area b := by
  have h := congrArg Subtype.val (normalizedColumnsEquiv.apply_symm_apply b)
  change (normalizedColumnsEquiv.symm b).transpose.rowLens.reverse = b.val at h
  rw [area, ← h, List.sum_reverse, YoungDiagram.sum_rowLens_eq_card,
    YoungDiagram.card_transpose]
  rfl

/-- Two different occupied cells may share neither a column nor a bottom-aligned
    block of m rows. This is not the ordinary row-conflict condition when m > 1. -/
def Nonattacking (m : ℕ) (p : Finset (ℕ × ℕ)) : Prop :=
  (p : Set (ℕ × ℕ)).Pairwise fun x y => x.2 ≠ y.2 ∧ x.1 / m ≠ y.1 / m

/-- Actual k-cell subsets of the board, with each legal placement counted once. -/
def placements (m : ℕ) (b : PositiveColumns) (k : ℕ) : Finset (Finset (ℕ × ℕ)) := by
  classical
  exact ((cells b).powersetCard k).filter (Nonattacking m)

/-- The native m-level rook number, defined by a finite subset enumeration. -/
def rookCount (m : ℕ) (b : PositiveColumns) (k : ℕ) : ℕ :=
  (placements m b k).card

theorem rookCount_zero (m : ℕ) (b : PositiveColumns) : rookCount m b 0 = 1 := by
  classical
  have h : Nonattacking m ∅ := by simp [Nonattacking]
  rw [rookCount, placements, Finset.powersetCard_zero,
    Finset.filter_singleton]
  simp [h]

theorem rookCount_one (m : ℕ) (b : PositiveColumns) : rookCount m b 1 = area b := by
  classical
  rw [rookCount, placements, Finset.powersetCard_one]
  have h : ((cells b).map ⟨_, Finset.singleton_injective⟩).filter
      (Nonattacking m) = (cells b).map ⟨_, Finset.singleton_injective⟩ := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hp
    simp [Nonattacking]
  rw [h, Finset.card_map]
  exact cells_card b

theorem rookCount_eq_zero_of_area_lt (m : ℕ) (b : PositiveColumns) (k : ℕ)
    (hk : area b < k) : rookCount m b k = 0 := by
  have h : (cells b).powersetCard k = ∅ := by
    apply Finset.powersetCard_eq_empty.mpr
    simpa [cells_card] using hk
  simp [rookCount, placements, h]

/-- All rook numbers, including zero, are compared on the same normalized shapes. -/
def RookEquivalent (m : ℕ) (a b : PositiveColumns) : Prop :=
  ∀ k : ℕ, rookCount m a k = rookCount m b k

/-- A complete native rook vector needs only its positive indices through the
    common area. Equality at zero and all omitted higher indices is proved. -/
theorem rookEquivalent_iff (m : ℕ) (a b : PositiveColumns) :
    RookEquivalent m a b ↔ area a = area b ∧
      ∀ k ∈ Finset.Icc 1 (area b), rookCount m a k = rookCount m b k := by
  constructor
  · intro h
    exact ⟨by simpa only [rookCount_one] using h 1, fun k _ => h k⟩
  · rintro ⟨ha,h⟩ k
    by_cases hk : k = 0
    · subst k
      rw [rookCount_zero, rookCount_zero]
    by_cases hb : k ≤ area b
    · exact h k (Finset.mem_Icc.mpr ⟨by omega,hb⟩)
    · rw [rookCount_eq_zero_of_area_lt m b k (by omega),
        rookCount_eq_zero_of_area_lt m a k (by omega)]

/-- No width or height bound is built into the class carrier. -/
abbrev RookClass (m : ℕ) (b : PositiveColumns) :=
  {a : PositiveColumns // RookEquivalent m a b}

private theorem class_area (m : ℕ) (b : PositiveColumns) (a : RookClass m b) :
    area a.val = area b := by
  simpa only [rookCount_one] using a.property 1

private theorem cells_injective : Function.Injective cells := by
  intro a b h
  apply normalizedColumnsEquiv.symm.injective
  exact YoungDiagram.ext h

private theorem cell_bound (b : PositiveColumns) (x : ℕ × ℕ) (hx : x ∈ cells b) :
    x.1 < area b ∧ x.2 < area b := by
  have hr : Finset.range (x.1+1) ×ˢ ({x.2} : Finset ℕ) ⊆ cells b := by
    intro y hy
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hy
    have hj' := Finset.mem_singleton.mp hj
    exact (normalizedColumnsEquiv.symm b).up_left_mem
      (by simpa using (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
      (by omega) hx
  have hc : ({x.1} : Finset ℕ) ×ˢ Finset.range (x.2+1) ⊆ cells b := by
    intro y hy
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hy
    have hi' := Finset.mem_singleton.mp hi
    exact (normalizedColumnsEquiv.symm b).up_left_mem
      (by omega) (by simpa using (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))) hx
  have hr' := Finset.card_le_card hr
  have hc' := Finset.card_le_card hc
  simp only [Finset.card_product, Finset.card_range, Finset.card_singleton,
    mul_one, one_mul, cells_card] at hr' hc'
  omega

/-- Equal-area shapes are embedded in the powerset of the actual area-square.
    Finiteness is proved independently of Nat.card's convention for infinite types. -/
theorem rookClass_finite (m : ℕ) (b : PositiveColumns) : Finite (RookClass m b) := by
  let square := Finset.range (area b) ×ˢ Finset.range (area b)
  let f : RookClass m b → ↥square.powerset := fun a => ⟨cells a.val, by
    apply Finset.mem_powerset.mpr
    intro x hx
    have h := cell_bound a.val x hx
    rw [class_area m b a] at h
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr h.1, Finset.mem_range.mpr h.2⟩⟩
  apply Finite.of_injective f
  intro a a' h
  apply Subtype.ext
  exact cells_injective (congrArg Subtype.val h)

private theorem width_le_area (b : PositiveColumns) : b.val.length ≤ area b := by
  exact List.length_le_sum_of_one_le b.val (fun x hx => b.property.2 x hx)

/-- There is only one allowed padding at a fixed length; zeros are prepended. -/
def pad (N : ℕ) (b : PositiveColumns) : List ℕ :=
  List.replicate (N-b.val.length) 0 ++ b.val

/-- Every member of the unrestricted native class fits in every registered
    common length, with a genuine leading zero, including the empty board. -/
theorem class_padding (m : ℕ) (b : PositiveColumns) (N : ℕ)
    (hN : area b + 1 ≤ N) (a : RookClass m b) :
    a.val.val.length < N ∧ (pad N a.val).length = N ∧
      (pad N a.val).head? = some 0 ∧ (pad N a.val).sum = area b := by
  have hw := width_le_area a.val
  rw [class_area m b a] at hw
  have hl : a.val.val.length < N := by omega
  refine ⟨hl, ?_, ?_, ?_⟩
  · simp only [pad, List.length_append, List.length_replicate]
    omega
  · have hp : N - a.val.val.length = (N - a.val.val.length - 1) + 1 := by omega
    rw [pad, hp, List.replicate_succ, List.cons_append]
    rfl
  · simpa [pad, area] using class_area m b a

/-- The complete native finite interface used by class enumeration: finiteness,
    the exact finite rook-vector test, and every common padding length. -/
theorem native_interface (m : ℕ) (b : PositiveColumns) :
    Finite (RookClass m b) ∧
      (∀ a : PositiveColumns, RookEquivalent m a b ↔ area a = area b ∧
        ∀ k ∈ Finset.Icc 1 (area b), rookCount m a k = rookCount m b k) ∧
      (∀ (N : ℕ), area b + 1 ≤ N → ∀ a : RookClass m b,
        a.val.val.length < N ∧ (pad N a.val).length = N ∧
          (pad N a.val).head? = some 0 ∧ (pad N a.val).sum = area b) := by
  exact ⟨rookClass_finite m b, fun a => rookEquivalent_iff m a b,
    fun N hN a => class_padding m b N hN a⟩

end D5.S3.Combinatorics.Partitions.RookClassNative
