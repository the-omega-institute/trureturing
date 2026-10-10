/- GID: D5/S3/Combinatorics/ErdosUlam/SublatticeConstructions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ErdosUlam/SublatticeConstructions
   mirror-E: none(waiver:general-lattice-constructions)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Arithmetic progression diamonds and interval extensions enlarge monochromatic initialSegment families. -/

import D5.S3.Combinatorics.ErdosUlam.SublatticeDefs

namespace D5.S3.Combinatorics.ErdosUlam.SublatticeConstructions

open D5.S3.Combinatorics.ErdosUlam.SublatticeDefs
open Finset

private theorem prefix_family_closed (n : ℕ) (R : Finset ℕ) :
    ∀ A ∈ R.image (initialSegment n), ∀ B ∈ R.image (initialSegment n),
      A ∪ B ∈ R.image (initialSegment n) ∧ A ∩ B ∈ R.image (initialSegment n) := by
  intro A hA B hB
  obtain ⟨r, hr, rfl⟩ := mem_image.mp hA
  obtain ⟨s, hs, rfl⟩ := mem_image.mp hB
  rcases le_total r s with h | h
  · rw [union_eq_right.mpr (prefix_subset h), inter_eq_left.mpr (prefix_subset h)]
    exact ⟨mem_image.mpr ⟨s, hs, rfl⟩, mem_image.mpr ⟨r, hr, rfl⟩⟩
  · rw [union_comm, inter_comm, union_eq_right.mpr (prefix_subset h),
      inter_eq_left.mpr (prefix_subset h)]
    exact ⟨mem_image.mpr ⟨r, hr, rfl⟩, mem_image.mpr ⟨s, hs, rfl⟩⟩

/-- Consecutive equal-coloured ranks in arithmetic progression admit an extra member. -/
theorem diamond_sublattice (n a b c : ℕ) (g : ℕ → Bool) (color : Bool)
    (hab : a < b) (hbc : b < c) (hcn : c ≤ n) (hap : a + c = 2 * b)
    (ha : g a = color) (hb : g b = color) (hc : g c = color)
    (hgap : ∀ r, a < r → r < c → g r = color → r = b) :
    ∃ L : Finset (Finset (Fin n)), IsSublattice L ∧
      Monochromatic (fun A => g A.card) L ∧
      ((range (n + 1)).filter (fun r => g r = color)).card + 1 ≤ L.card := by
  classical
  let R := (range (n + 1)).filter (fun r => g r = color)
  let C := R.image (initialSegment n)
  let X := initialSegment n a ∪ (initialSegment n c \ initialSegment n b)
  have hrbound : ∀ r ∈ R, r ≤ n := by intro r hr; simp only [R, mem_filter, mem_range] at hr; omega
  have hR : ∀ r, r ≤ n → g r = color → r ∈ R := by
    intro r hr hg; simp [R, hg]; omega
  have hC : ∀ r, r ≤ n → g r = color → initialSegment n r ∈ C := by
    intro r hr hg; exact mem_image.mpr ⟨r, hR r hr hg, rfl⟩
  have hXcard : X.card = b := by
    have hd : Disjoint (initialSegment n a) (initialSegment n c \ initialSegment n b) := by
      apply disjoint_left.mpr
      intro i hi hj
      exact (mem_sdiff.mp hj).2 (prefix_subset (by omega : a ≤ b) hi)
    rw [show X = _ from rfl, card_union_of_disjoint hd,
      card_sdiff_of_subset (prefix_subset (by omega : b ≤ c)),
      prefix_card n a (by omega), prefix_card n c hcn, prefix_card n b (by omega)]
    omega
  have hXneq : X ≠ initialSegment n b := by
    intro he
    have hn : a < n := by omega
    have hi : (⟨a, hn⟩ : Fin n) ∈ initialSegment n b := by simp [initialSegment]; omega
    rw [← he] at hi
    simp only [X, mem_union, initialSegment, mem_filter, mem_univ, true_and, mem_sdiff] at hi
    omega
  have hXnot : X ∉ C := by
    intro hx
    obtain ⟨r, hr, he⟩ := mem_image.mp hx
    have hec := congrArg Finset.card he
    rw [prefix_card n r (hrbound r hr), hXcard] at hec
    exact hXneq (hec ▸ he.symm)
  have hlow : ∀ r, r ≤ a → initialSegment n r ⊆ X := by
    intro r hr i hi
    exact mem_union_left _ (prefix_subset hr hi)
  have hhigh : ∀ r, c ≤ r → X ⊆ initialSegment n r := by
    intro r hr i hi
    rcases mem_union.mp hi with hi | hi
    · exact prefix_subset (by omega : a ≤ r) hi
    · exact prefix_subset hr (mem_sdiff.mp hi).1
  have hmidU : X ∪ initialSegment n b = initialSegment n c := by
    ext i
    simp only [X, mem_union, mem_sdiff, initialSegment, mem_filter, mem_univ, true_and]
    omega
  have hmidI : X ∩ initialSegment n b = initialSegment n a := by
    ext i
    simp only [X, mem_inter, mem_union, mem_sdiff, initialSegment, mem_filter, mem_univ, true_and]
    omega
  have hcross : ∀ B ∈ C, X ∪ B ∈ insert X C ∧ X ∩ B ∈ insert X C := by
    intro B hB
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hB
    have hg : g r = color := (mem_filter.mp hr).2
    by_cases hlo : r ≤ a
    · rw [union_eq_left.mpr (hlow r hlo), inter_eq_right.mpr (hlow r hlo)]
      exact ⟨mem_insert_self _ _, mem_insert_of_mem (mem_image.mpr ⟨r, hr, rfl⟩)⟩
    by_cases hhi : c ≤ r
    · rw [union_eq_right.mpr (hhigh r hhi), inter_eq_left.mpr (hhigh r hhi)]
      exact ⟨mem_insert_of_mem (mem_image.mpr ⟨r, hr, rfl⟩), mem_insert_self _ _⟩
    have he : r = b := hgap r (by omega) (by omega) hg
    subst r
    rw [hmidU, hmidI]
    exact ⟨mem_insert_of_mem (hC c hcn hc), mem_insert_of_mem (hC a (by omega) ha)⟩
  refine ⟨insert X C, ?_, ?_, ?_⟩
  · refine ⟨⟨X, mem_insert_self _ _⟩, ?_⟩
    intro A hA B hB
    rcases mem_insert.mp hA with rfl | hA
    · rcases mem_insert.mp hB with rfl | hB
      · simp
      · exact hcross B hB
    · rcases mem_insert.mp hB with rfl | hB
      · simpa only [union_comm, inter_comm] using hcross A hA
      · obtain ⟨hu, hi⟩ := prefix_family_closed n R A hA B hB
        exact ⟨mem_insert_of_mem hu, mem_insert_of_mem hi⟩
  · refine ⟨color, ?_⟩
    intro A hA
    rcases mem_insert.mp hA with rfl | hA
    · simpa only [hXcard] using hb
    · obtain ⟨r, hr, rfl⟩ := mem_image.mp hA
      change g (initialSegment n r).card = color
      rw [prefix_card n r (hrbound r hr)]
      exact (mem_filter.mp hr).2
  · rw [card_insert_of_notMem hXnot]
    have hcard : C.card = R.card := by
      apply card_image_iff.mpr
      intro r hr s hs he
      have := congrArg Finset.card he
      simpa only [prefix_card n r (hrbound r hr), prefix_card n s (hrbound s hs)] using this
    simp only [hcard]
    exact le_rfl

/-- Translation into a Boolean interval preserves both lattice operations. -/
def intervalLift (n b k : ℕ) (h : b + k ≤ n) (A : Finset (Fin k)) : Finset (Fin n) :=
  initialSegment n b ∪ A.image (fun i => (⟨b + i.val, by omega⟩ : Fin n))

private theorem shift_injective (n b k : ℕ) (h : b + k ≤ n) :
    Function.Injective (fun i : Fin k => (⟨b + i.val, by omega⟩ : Fin n)) := by
  intro i j he
  apply Fin.ext
  have := congrArg Fin.val he
  simpa using this

private theorem intervalLift_bounds (n b k : ℕ) (h : b + k ≤ n) (A : Finset (Fin k)) :
    initialSegment n b ⊆ intervalLift n b k h A ∧
    intervalLift n b k h A ⊆ initialSegment n (b + k) := by
  constructor
  · exact subset_union_left
  · intro i hi
    rcases mem_union.mp hi with hi | hi
    · exact prefix_subset (by omega : b ≤ b + k) hi
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
      simp only [initialSegment, mem_filter, mem_univ, true_and]
      omega

private theorem intervalLift_card (n b k : ℕ) (h : b + k ≤ n) (A : Finset (Fin k)) :
    (intervalLift n b k h A).card = b + A.card := by
  unfold intervalLift
  rw [card_union_of_disjoint, prefix_card n b (by omega),
    card_image_of_injective _ (shift_injective n b k h)]
  apply disjoint_left.mpr
  intro i hi hj
  obtain ⟨j, hj, he⟩ := mem_image.mp hj
  simp only [initialSegment, mem_filter, mem_univ, true_and] at hi
  have heval := congrArg Fin.val he
  change b + j.val = i.val at heval
  omega

private theorem intervalLift_injective (n b k : ℕ) (h : b + k ≤ n) :
    Function.Injective (intervalLift n b k h) := by
  intro A B he
  ext i
  have hm := Finset.ext_iff.mp he (⟨b + i.val, by omega⟩ : Fin n)
  have hm' : (∃ a ∈ A, a.val = i.val) ↔ (∃ a ∈ B, a.val = i.val) := by
    simpa [intervalLift, initialSegment] using hm
  simpa only [Fin.val_inj, exists_eq_right] using hm'

/-- A monochromatic family in a Boolean interval gains every same-coloured prefix outside it. -/
theorem interval_sublattice (n b k : ℕ) (g : ℕ → Bool) (color : Bool)
    (h : b + k ≤ n) (L : Finset (Finset (Fin k))) (hL : IsSublattice L)
    (hmono : ∀ A ∈ L, g (b + A.card) = color)
    (hsize : ((range (k + 1)).filter (fun r => g (b + r) = color)).card + 1 ≤ L.card) :
    ∃ M : Finset (Finset (Fin n)), IsSublattice M ∧
      Monochromatic (fun A => g A.card) M ∧
      ((range (n + 1)).filter (fun r => g r = color)).card + 1 ≤ M.card := by
  classical
  let R := (range (n + 1)).filter (fun r => g r = color)
  let O := R.filter (fun r => r < b ∨ b + k < r)
  let W := R.filter (fun r => ¬ (r < b ∨ b + k < r))
  let C := O.image (initialSegment n)
  let J := L.image (intervalLift n b k h)
  have hrbound : ∀ r ∈ R, r ≤ n := by intro r hr; simp only [R, mem_filter, mem_range] at hr; omega
  have hobound : ∀ r ∈ O, r ≤ n := by intro r hr; exact hrbound r (mem_filter.mp hr).1
  have hJclosed : ∀ A ∈ J, ∀ B ∈ J, A ∪ B ∈ J ∧ A ∩ B ∈ J := by
    intro A hA B hB
    obtain ⟨A, hAL, rfl⟩ := mem_image.mp hA
    obtain ⟨B, hBL, rfl⟩ := mem_image.mp hB
    obtain ⟨hu, hi⟩ := hL.2 A hAL B hBL
    have huLift : intervalLift n b k h (A ∪ B) =
        intervalLift n b k h A ∪ intervalLift n b k h B := by
      simp only [intervalLift, image_union]
      ext i
      simp only [mem_union]
      tauto
    have hiLift : intervalLift n b k h (A ∩ B) =
        intervalLift n b k h A ∩ intervalLift n b k h B := by
      simp only [intervalLift, image_inter _ _ (shift_injective n b k h),
        union_inter_distrib_left]
    rw [← huLift, ← hiLift]
    exact ⟨mem_image.mpr ⟨_, hu, rfl⟩, mem_image.mpr ⟨_, hi, rfl⟩⟩
  have hcross : ∀ A ∈ J, ∀ B ∈ C, A ∪ B ∈ J ∪ C ∧ A ∩ B ∈ J ∪ C := by
    intro A hA B hB
    obtain ⟨A, hAL, rfl⟩ := mem_image.mp hA
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hB
    rcases (mem_filter.mp hr).2 with hlo | hhi
    · have hs : initialSegment n r ⊆ intervalLift n b k h A :=
        subset_trans (prefix_subset (by omega : r ≤ b)) (intervalLift_bounds n b k h A).1
      rw [union_eq_left.mpr hs, inter_eq_right.mpr hs]
      exact ⟨mem_union_left _ (mem_image.mpr ⟨_, hAL, rfl⟩),
        mem_union_right _ (mem_image.mpr ⟨_, hr, rfl⟩)⟩
    · have hs : intervalLift n b k h A ⊆ initialSegment n r :=
        subset_trans (intervalLift_bounds n b k h A).2 (prefix_subset (by omega : b + k ≤ r))
      rw [union_eq_right.mpr hs, inter_eq_left.mpr hs]
      exact ⟨mem_union_right _ (mem_image.mpr ⟨_, hr, rfl⟩),
        mem_union_left _ (mem_image.mpr ⟨_, hAL, rfl⟩)⟩
  have hJC : Disjoint J C := by
    apply disjoint_left.mpr
    intro A hA hC
    obtain ⟨B, hB, heB⟩ := mem_image.mp hA
    obtain ⟨r, hr, heR⟩ := mem_image.mp hC
    have he := congrArg Finset.card (heB.trans heR.symm)
    rw [intervalLift_card, prefix_card n r (hobound r hr)] at he
    have hBk : B.card ≤ k := by simpa using card_le_univ B
    have ho := (mem_filter.mp hr).2
    omega
  have hCcard : C.card = O.card := by
    apply card_image_iff.mpr
    intro r hr s hs he
    have := congrArg Finset.card he
    simpa only [prefix_card n r (hobound r hr), prefix_card n s (hobound s hs)] using this
  have hJcard : J.card = L.card := card_image_of_injective _ (intervalLift_injective n b k h)
  have hWcard : W.card = ((range (k + 1)).filter (fun r => g (b + r) = color)).card := by
    apply card_bij (fun r hr => r - b)
    · intro r hr
      simp only [W, R, mem_filter, mem_range, not_or, not_lt] at hr
      simp only [mem_filter, mem_range]
      refine ⟨by omega, ?_⟩
      have he : b + (r - b) = r := by omega
      simpa only [he] using hr.1.2
    · intro r hr s hs he
      simp only [W, R, mem_filter, mem_range, not_or, not_lt] at hr hs
      omega
    · intro r hr
      simp only [mem_filter, mem_range] at hr
      refine ⟨b + r, ?_, ?_⟩
      · simp only [W, R, mem_filter, mem_range, not_or, not_lt]
        exact ⟨⟨by omega, hr.2⟩, by omega, by omega⟩
      · omega
  have hpartition : O.card + W.card = R.card := card_filter_add_card_filter_not _
  refine ⟨J ∪ C, ?_, ?_, ?_⟩
  · constructor
    · obtain ⟨A, hA⟩ := hL.1
      exact ⟨_, mem_union_left _ (mem_image.mpr ⟨A, hA, rfl⟩)⟩
    · intro A hA B hB
      rcases mem_union.mp hA with hA | hA <;> rcases mem_union.mp hB with hB | hB
      · obtain ⟨hu, hi⟩ := hJclosed A hA B hB
        exact ⟨mem_union_left _ hu, mem_union_left _ hi⟩
      · exact hcross A hA B hB
      · simpa only [union_comm, inter_comm] using hcross B hB A hA
      · obtain ⟨hu, hi⟩ := prefix_family_closed n O A hA B hB
        exact ⟨mem_union_right _ hu, mem_union_right _ hi⟩
  · refine ⟨color, ?_⟩
    intro A hA
    rcases mem_union.mp hA with hA | hA
    · obtain ⟨A, hAL, rfl⟩ := mem_image.mp hA
      change g (intervalLift n b k h A).card = color
      rw [intervalLift_card]
      exact hmono A hAL
    · obtain ⟨r, hr, rfl⟩ := mem_image.mp hA
      change g (initialSegment n r).card = color
      rw [prefix_card n r (hobound r hr)]
      exact (mem_filter.mp (mem_filter.mp hr).1).2
  · rw [card_union_of_disjoint hJC, hJcard, hCcard]
    rw [← hWcard] at hsize
    change R.card + 1 ≤ L.card + O.card
    omega

end D5.S3.Combinatorics.ErdosUlam.SublatticeConstructions
