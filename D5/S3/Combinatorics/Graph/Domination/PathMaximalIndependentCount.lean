/- GID: D5/S3/Combinatorics/Graph/Domination/PathMaximalIndependentCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/PathMaximalIndependentCount
   mirror-E: none(waiver:unbounded-constructive-proof)
   anchors: []
   utility: none
   digest: Actual path independent dominating subsets split by inverse attachHead and tail maps. -/

module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic

/-! Paths use the actual labels `0,...,n-1`. Independence and closed domination
are retained separately in the local membership predicate. -/

@[expose] public section

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Domination.PathMaximalIndependentCount

open Finset

/-- A bounded independent dominating subset of the integer path. -/
def Valid (n : ℕ) (I : Finset ℕ) : Prop :=
  (∀ i ∈ I, i < n) ∧ (∀ i ∈ I, i + 1 ∉ I) ∧
    ∀ i < n, i ∈ I ∨ ∃ j ∈ I, i + 1 = j ∨ j + 1 = i

/-- The actual finite family, rather than a recursively defined surrogate count. -/
noncomputable def family (n : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (range n).powerset.filter
    (fun I => Maximal (SimpleGraph.pathGraph n).IsIndepSet {i : Fin n | i.val ∈ I})

/-- The number of actual independent dominating path subsets. -/
noncomputable def count (n : ℕ) : ℕ := (family n).card

/-- Insert the first selected vertex `t`, leaving one excluded neighbor before the tail. -/
def attachHead (t : ℕ) (I : Finset ℕ) : Finset ℕ :=
  insert t (I.image (fun i => i + (t + 2)))

/-- Read the tail in its original order, with labels shifted back to zero. -/
def tail (k : ℕ) (I : Finset ℕ) : Finset ℕ :=
  (I.filter (fun i => k ≤ i)).image (fun i => i - k)

@[simp] private theorem mem_prefix_shift (t : ℕ) (I : Finset ℕ) (i : ℕ) :
    i + (t + 2) ∈ attachHead t I ↔ i ∈ I := by
  have hne : i + (t + 2) ≠ t := by omega
  simp [attachHead, hne]

private theorem tail_prefix (t : ℕ) (I : Finset ℕ) : tail (t + 2) (attachHead t I) = I := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, he⟩ := mem_image.mp hi
    obtain ⟨hj, hjk⟩ := mem_filter.mp hj
    rcases mem_insert.mp hj with hjt | hj
    · omega
    · obtain ⟨l, hl, rfl⟩ := mem_image.mp hj
      have hli : l = i := by omega
      exact hli ▸ hl
  · intro hi
    apply mem_image.mpr
    refine ⟨i + (t + 2), mem_filter.mpr ⟨(mem_prefix_shift t I i).mpr hi, by omega⟩, ?_⟩
    omega

private theorem prefix_injective (t : ℕ) : Function.Injective (attachHead t) := by
  intro I J h
  have he := congrArg (tail (t + 2)) h
  simpa only [tail_prefix] using he

private theorem reconstruct_prefix (t : ℕ) (I : Finset ℕ)
    (hlow : ∀ i < t + 2, i ∈ I ↔ i = t) :
    attachHead t (tail (t + 2) I) = I := by
  ext i
  constructor
  · intro hi
    rcases mem_insert.mp hi with hit | hi
    · subst i
      exact (hlow t (by omega)).mpr rfl
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
      obtain ⟨l, hl, he⟩ := mem_image.mp hj
      obtain ⟨hl, hll⟩ := mem_filter.mp hl
      have hlj : l = j + (t + 2) := by omega
      exact hlj ▸ hl
  · intro hi
    by_cases hsmall : i < t + 2
    · exact mem_insert.mpr (Or.inl ((hlow i hsmall).mp hi))
    · apply mem_insert.mpr
      right
      apply mem_image.mpr
      refine ⟨i - (t + 2), mem_image.mpr ⟨i, mem_filter.mpr ⟨hi, by omega⟩, rfl⟩, ?_⟩
      omega

private theorem valid_prefix_iff (t n : ℕ) (ht : t ≤ 1) (I : Finset ℕ) :
    Valid (n + (t + 2)) (attachHead t I) ↔ Valid n I := by
  constructor
  · rintro ⟨hb, hi, hd⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i hI
      have h := hb (i + (t + 2)) ((mem_prefix_shift t I i).mpr hI)
      omega
    · intro i hI hI'
      have h := hi (i + (t + 2)) ((mem_prefix_shift t I i).mpr hI)
      apply h
      convert (mem_prefix_shift t I (i + 1)).mpr hI' using 1 <;> omega
    · intro i hin
      rcases hd (i + (t + 2)) (by omega) with h | ⟨j, hj, hji⟩
      · exact Or.inl ((mem_prefix_shift t I i).mp h)
      · rcases mem_insert.mp hj with hjt | hj
        · omega
        · obtain ⟨k, hk, rfl⟩ := mem_image.mp hj
          exact Or.inr ⟨k, hk, by omega⟩
  · rintro ⟨hb, hi, hd⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i hI
      rcases mem_insert.mp hI with hit | hI
      · omega
      · obtain ⟨j, hj, rfl⟩ := mem_image.mp hI
        have h := hb j hj
        omega
    · intro i hI hnext
      rcases mem_insert.mp hI with hit | hI
      · rcases mem_insert.mp hnext with hnext | hnext
        · omega
        · obtain ⟨j, hj, he⟩ := mem_image.mp hnext
          omega
      · obtain ⟨j, hj, rfl⟩ := mem_image.mp hI
        rcases mem_insert.mp hnext with hnext | hnext
        · omega
        · obtain ⟨k, hk, he⟩ := mem_image.mp hnext
          have hkj : k = j + 1 := by omega
          exact hi j hj (hkj ▸ hk)
    · intro i hin
      by_cases hsmall : i < t + 2
      · by_cases hit : i = t
        · exact Or.inl (mem_insert.mpr (Or.inl hit))
        · exact Or.inr ⟨t, mem_insert_self _ _, by omega⟩
      · have hlarge : t + 2 ≤ i := by omega
        have hik : i = (i - (t + 2)) + (t + 2) := by omega
        have hk : i - (t + 2) < n := by omega
        rcases hd (i - (t + 2)) hk with h | ⟨j, hj, hji⟩
        · left
          rw [hik]
          exact (mem_prefix_shift t I _).mpr h
        · right
          refine ⟨j + (t + 2), (mem_prefix_shift t I j).mpr hj, ?_⟩
          omega

private theorem valid_iff_native (n : ℕ) (I : Finset ℕ) :
    Valid n I ↔ (∀ i ∈ I, i < n) ∧
      Maximal (SimpleGraph.pathGraph n).IsIndepSet {i : Fin n | i.val ∈ I} := by
  classical
  constructor
  · rintro ⟨hb, hi, hd⟩
    refine ⟨hb, ?_, ?_⟩
    · intro x hx y hy hne hadj
      rcases SimpleGraph.pathGraph_adj.mp hadj with hxy | hyx
      · exact hi x.val hx (hxy.symm ▸ hy)
      · exact hi y.val hy (hyx.symm ▸ hx)
    · intro T hT hIT x hx
      rcases hd x.val x.isLt with h | ⟨j, hj, hji⟩
      · exact h
      · let y : Fin n := ⟨j, hb j hj⟩
        have hne : x ≠ y := by
          intro heq
          have hv := congrArg Fin.val heq
          dsimp [y] at hv
          omega
        exact False.elim (hT hx (hIT hj) hne (SimpleGraph.pathGraph_adj.mpr hji))
  · rintro ⟨hb, hI, hm⟩
    refine ⟨hb, ?_, ?_⟩
    · intro i hi hinext
      let x : Fin n := ⟨i, hb i hi⟩
      let y : Fin n := ⟨i + 1, hb (i + 1) hinext⟩
      have hne : x ≠ y := by
        intro heq
        have hv := congrArg Fin.val heq
        dsimp [x, y] at hv
        omega
      exact hI hi hinext hne (SimpleGraph.pathGraph_adj.mpr (Or.inl rfl))
    · intro i hin
      by_cases hi : i ∈ I
      · exact Or.inl hi
      · right
        by_contra hn
        let x : Fin n := ⟨i, hin⟩
        have hins : (SimpleGraph.pathGraph n).IsIndepSet
            (insert x {j : Fin n | j.val ∈ I}) := by
          apply hI.insert
          intro y hy hne
          constructor
          · intro hadj
            exact hn ⟨y.val, hy, SimpleGraph.pathGraph_adj.mp hadj⟩
          · intro hadj
            exact hn ⟨y.val, hy, SimpleGraph.pathGraph_adj.mp hadj.symm⟩
        have hmem := hm hins (Set.subset_insert _ _) (Set.mem_insert x _)
        exact hi hmem

@[simp] theorem mem_family (n : ℕ) (I : Finset ℕ) :
    I ∈ family n ↔ Valid n I := by
  classical
  simp only [family, mem_filter, mem_powerset]
  constructor
  · rintro ⟨hb, hm⟩
    exact (valid_iff_native n I).mpr ⟨fun i hi => mem_range.mp (hb hi), hm⟩
  · intro h
    have he := (valid_iff_native n I).mp h
    exact ⟨fun i hi => mem_range.mpr (he.1 i hi), he.2⟩

private theorem family_split (n : ℕ) :
    family (n + 3) = (family (n + 1)).image (attachHead 0) ∪ (family n).image (attachHead 1) := by
  classical
  ext I
  constructor
  · intro hI
    have hv := (mem_family _ _).mp hI
    by_cases hzero : 0 ∈ I
    · have hone : 1 ∉ I := hv.2.1 0 hzero
      have hl : ∀ i < 0 + 2, i ∈ I ↔ i = 0 := by
        intro i hi
        interval_cases i <;> simp_all
      have he := reconstruct_prefix 0 I hl
      apply mem_union.mpr
      left
      apply mem_image.mpr
      refine ⟨tail 2 I, (mem_family _ _).mpr ?_, he⟩
      apply (valid_prefix_iff 0 (n + 1) (by omega) _).mp
      simpa only [he, Nat.add_assoc] using hv
    · have hone : 1 ∈ I := by
        rcases hv.2.2 0 (by omega) with h | ⟨j, hj, hji⟩
        · exact False.elim (hzero h)
        · have hj1 : j = 1 := by omega
          exact hj1 ▸ hj
      have htwo : 2 ∉ I := hv.2.1 1 hone
      have hl : ∀ i < 1 + 2, i ∈ I ↔ i = 1 := by
        intro i hi
        interval_cases i <;> simp_all
      have he := reconstruct_prefix 1 I hl
      apply mem_union.mpr
      right
      apply mem_image.mpr
      refine ⟨tail 3 I, (mem_family _ _).mpr ?_, he⟩
      apply (valid_prefix_iff 1 n (by omega) _).mp
      simpa only [he] using hv
  · intro hI
    rcases mem_union.mp hI with hI | hI
    · obtain ⟨J, hJ, rfl⟩ := mem_image.mp hI
      apply (mem_family _ _).mpr
      simpa only [Nat.add_assoc] using
        (valid_prefix_iff 0 (n + 1) (by omega) J).mpr ((mem_family _ _).mp hJ)
    · obtain ⟨J, hJ, rfl⟩ := mem_image.mp hI
      exact (mem_family _ _).mpr
        ((valid_prefix_iff 1 n (by omega) J).mpr ((mem_family _ _).mp hJ))

/-- The Padovan recurrence is derived from two disjoint, invertible maps on actual subsets. -/
theorem count_recurrence (n : ℕ) : count (n + 3) = count (n + 1) + count n := by
  classical
  have hd : Disjoint ((family (n + 1)).image (attachHead 0)) ((family n).image (attachHead 1)) := by
    apply disjoint_left.mpr
    intro I hI hI'
    obtain ⟨J, hJ, hJI⟩ := mem_image.mp hI
    obtain ⟨K, hK, hKI⟩ := mem_image.mp hI'
    have hz : 0 ∈ attachHead 0 J := mem_insert_self _ _
    rw [hJI, ← hKI] at hz
    simp [attachHead] at hz
  unfold count
  rw [family_split, card_union_of_disjoint hd,
    card_image_of_injective _ (prefix_injective 0),
    card_image_of_injective _ (prefix_injective 1)]

theorem valid_singleton (n t : ℕ) (ht : t < n)
    (hd : ∀ i < n, i = t ∨ i + 1 = t ∨ t + 1 = i) : Valid n {t} := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    simpa only [mem_singleton.mp hi] using ht
  · intro i hi
    have he := mem_singleton.mp hi
    subst i
    simp
  · intro i hin
    rcases hd i hin with h | h
    · exact Or.inl (mem_singleton.mpr h)
    · exact Or.inr ⟨t, mem_singleton_self _, h⟩

private theorem family_zero : family 0 = {∅} := by
  classical
  ext I
  rw [mem_family, mem_singleton]
  constructor
  · intro h
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hh := h.1 i hi
    omega
  · rintro rfl
    simp [Valid]

private theorem family_one : family 1 = {{0}} := by
  classical
  ext I
  rw [mem_family, mem_singleton]
  constructor
  · intro h
    have hz : 0 ∈ I := by
      rcases h.2.2 0 (by omega) with hz | ⟨j, hj, hji⟩
      · exact hz
      · have hb := h.1 j hj
        omega
    ext i
    constructor
    · intro hi
      exact mem_singleton.mpr (by have hh := h.1 i hi; omega)
    · intro hi
      have he := mem_singleton.mp hi
      exact he ▸ hz
  · rintro rfl
    exact valid_singleton 1 0 (by omega) (by intro i hi; left; omega)

private theorem family_two : family 2 = {{0}, {1}} := by
  classical
  ext I
  rw [mem_family]
  constructor
  · intro h
    by_cases hz : 0 ∈ I
    · have hone : 1 ∉ I := h.2.1 0 hz
      have he : I = {0} := by
        ext i
        constructor
        · intro hi
          have hb := h.1 i hi
          have hzero : i = 0 := by
            by_contra hh
            have hi1 : i = 1 := by omega
            exact hone (hi1 ▸ hi)
          exact mem_singleton.mpr hzero
        · intro hi
          exact mem_singleton.mp hi ▸ hz
      simp [he]
    · have hone : 1 ∈ I := by
        rcases h.2.2 0 (by omega) with hi | ⟨j, hj, hji⟩
        · exact False.elim (hz hi)
        · have hj1 : j = 1 := by omega
          exact hj1 ▸ hj
      have he : I = {1} := by
        ext i
        constructor
        · intro hi
          have hb := h.1 i hi
          have hi1 : i = 1 := by
            by_contra hh
            have hi0 : i = 0 := by omega
            exact hz (hi0 ▸ hi)
          exact mem_singleton.mpr hi1
        · intro hi
          exact mem_singleton.mp hi ▸ hone
      simp [he]
  · intro h
    have hcases : I = {0} ∨ I = {1} := by simpa using h
    rcases hcases with rfl | rfl
    · exact valid_singleton 2 0 (by omega) (by intro i hi; omega)
    · exact valid_singleton 2 1 (by omega) (by intro i hi; omega)

/-- Initial values include the empty path, which is an auxiliary path only. -/
theorem count_initial : count 0 = 1 ∧ count 1 = 1 ∧ count 2 = 2 := by
  classical
  simp [count, family_zero, family_one, family_two]

end D5.S3.Combinatorics.Graph.Domination.PathMaximalIndependentCount
