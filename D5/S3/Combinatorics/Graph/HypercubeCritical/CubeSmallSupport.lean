/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CubeSmallSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CubeSmallSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Small Boolean cube sets admit singleton neighbors in dimension at least nine. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum

/-! Singleton neighbors for small vertex sets in actual Boolean cubes. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum

private def diff {n : Nat} (x z : Q n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ z i)

private theorem diff_flip {n : Nat} (x z : Q n) (i : Fin n) :
    diff (BalancedCriticalSpectrum.flip x i) z =
      if i ∈ diff x z then (diff x z).erase i else insert i (diff x z) := by
  split_ifs with hi
  · ext j
    simp only [diff, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    by_cases hji : j = i
    · subst j
      have hne : x i ≠ z i := (Finset.mem_filter.mp hi).2
      have heq : (!x i) = z i := by
        cases hx : x i <;> cases hz : z i <;> simp_all
      simp [BalancedCriticalSpectrum.flip, heq]
    · simp [BalancedCriticalSpectrum.flip, hji]
  · ext j
    simp only [diff, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    by_cases hji : j = i
    · subst j
      have heq : x i = z i := by simpa [diff] using hi
      have hne : (!x i) ≠ z i := by
        rw [← heq]
        cases x i <;> decide
      simp [BalancedCriticalSpectrum.flip, hne]
    · simp [BalancedCriticalSpectrum.flip, hji]

-- A second selected neighbor of a flipped vertex differs in exactly two coordinates.
private theorem diff_of_adj_flip {n : Nat} {x z : Q n} (hxz : x ≠ z)
    (i : Fin n) (ha : (hypercube n).Adj (BalancedCriticalSpectrum.flip x i) z) :
    i ∈ diff x z ∧ (diff x z).card = 2 := by
  have ha' : (diff (BalancedCriticalSpectrum.flip x i) z).card = 1 := ha
  have hpos : 0 < (diff x z).card := hammingDist_pos.mpr hxz
  by_cases hi : i ∈ diff x z
  · have hc := Finset.card_erase_add_one hi
    rw [diff_flip, ite_eq_left hi] at ha'
    exact ⟨hi, by omega⟩
  · rw [diff_flip, ite_eq_right hi, Finset.card_insert_of_notMem hi] at ha'
    omega

-- Without a singleton neighbor, distance-two differences cover every direction.
open Classical in
private theorem directions_covered {n : Nat} (S : Finset (Q n))
    (hno : ∀ y : Q n, (S.filter (fun z => (hypercube n).Adj y z)).card ≠ 1)
    {x : Q n} (hx : x ∈ S) :
    Finset.univ ⊆
      ((S.erase x).filter (fun z => (diff x z).card = 2)).biUnion (diff x) := by
  classical
  intro i _
  have hxadj : (hypercube n).Adj (BalancedCriticalSpectrum.flip x i) x := by
    simpa only [BalancedCriticalSpectrum.flip_flip] using
      flip_adj (BalancedCriticalSpectrum.flip x i) i
  have hxmem : x ∈ S.filter (fun z => (hypercube n).Adj (BalancedCriticalSpectrum.flip x i) z) :=
    Finset.mem_filter.mpr ⟨hx, hxadj⟩
  have hpos := Finset.card_pos.mpr ⟨x, hxmem⟩
  have hne := hno (BalancedCriticalSpectrum.flip x i)
  have htwo : 1 <
      (S.filter (fun z => (hypercube n).Adj (BalancedCriticalSpectrum.flip x i) z)).card := by
    omega
  obtain ⟨z, hz, hzx⟩ := Finset.exists_mem_ne htwo x
  obtain ⟨hzS, haz⟩ := Finset.mem_filter.mp hz
  obtain ⟨hi, hcard⟩ := diff_of_adj_flip (Ne.symm hzx) i haz
  exact Finset.mem_biUnion.mpr
    ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hzx, hzS⟩, hcard⟩, hi⟩

-- Equal two-coordinate differences at mutual distance at most two add at most
-- one coordinate outside either fixed difference.
private theorem card_sdiff_le_one {n : Nat} (x z w : Q n)
    (hz : (diff x z).card = 2) (hw : (diff x w).card = 2)
    (hzw : (diff z w).card ≤ 2) :
    (diff x w \ diff x z).card ≤ 1 := by
  have heq : (diff x z \ diff x w).card = (diff x w \ diff x z).card :=
    Finset.card_sdiff_eq_card_sdiff_iff.mpr (hz.trans hw.symm)
  have hsplit : diff z w = (diff x z \ diff x w) ∪ (diff x w \ diff x z) := by
    ext i
    cases hxi : x i <;> cases hzi : z i <;> cases hwi : w i <;>
      simp [diff, hxi, hzi, hwi]
  have hd : Disjoint (diff x z \ diff x w) (diff x w \ diff x z) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have hsum : (diff z w).card =
      (diff x z \ diff x w).card + (diff x w \ diff x z).card := by
    rw [hsplit, Finset.card_union_of_disjoint hd]
  omega

open Classical in
/-- A nonempty set of at most six actual cube vertices has a singleton neighbor
in every dimension at least nine, with no parity restriction on the set. -/
theorem exists_unique_neighbor_of_card_le_six {n : Nat} (hn : 9 ≤ n)
    (S : Finset (Q n)) (hS : S.Nonempty) (hcard : S.card ≤ 6) :
    ∃ y : Q n, (S.filter (fun x => (hypercube n).Adj y x)).card = 1 := by
  classical
  by_contra h
  have hno : ∀ y : Q n,
      (S.filter (fun x => (hypercube n).Adj y x)).card ≠ 1 := by
    intro y hy
    exact h ⟨y, hy⟩
  let T (x : Q n) : Finset (Q n) :=
    (S.erase x).filter (fun z => (diff x z).card = 2)
  have hcover (x : Q n) (hx : x ∈ S) :
      Finset.univ ⊆ (T x).biUnion (diff x) :=
    directions_covered S hno hx
  have hcount (x : Q n) (hx : x ∈ S) : n ≤ (T x).card * 2 := by
    calc
      n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ ((T x).biUnion (diff x)).card := Finset.card_le_card (hcover x hx)
      _ ≤ ∑ z ∈ T x, (diff x z).card := Finset.card_biUnion_le
      _ = (T x).card * 2 := Finset.sum_const_nat fun z hz =>
        (Finset.mem_filter.mp hz).2
  -- Omitting even one other vertex from T leaves at most four two-coordinate
  -- differences, which cannot cover nine directions.
  have hpair : ∀ x ∈ S, ∀ z ∈ S, x ≠ z → (diff x z).card = 2 := by
    intro x hx z hz hxz
    by_contra hbad
    have hsub : T x ⊆ (S.erase x).erase z := by
      intro w hw
      obtain ⟨hwE, hwd⟩ := Finset.mem_filter.mp hw
      refine Finset.mem_erase.mpr ⟨?_, hwE⟩
      intro hwz
      apply hbad
      simpa only [hwz] using hwd
    have hct := Finset.card_le_card hsub
    have hcx := Finset.card_erase_add_one hx
    have hzE : z ∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxz, hz⟩
    have hcz := Finset.card_erase_add_one hzE
    have hc := hcount x hx
    omega
  obtain ⟨x, hx⟩ := hS
  have hc := hcount x hx
  have hTpos : 0 < (T x).card := by omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hTpos
  obtain ⟨hzE, hxzcard⟩ := Finset.mem_filter.mp hz
  have hzS : z ∈ S := (Finset.mem_erase.mp hzE).2
  let A : Finset (Fin n) := diff x z
  have hA : A.card = 2 := hxzcard
  have hsmall : (T x).card ≤ 5 := by
    have hsub : T x ⊆ S.erase x := Finset.filter_subset _ _
    have hct := Finset.card_le_card hsub
    have hcx := Finset.card_erase_add_one hx
    omega
  have hout (w : Q n) (hw : w ∈ T x) : (diff x w \ A).card ≤ 1 := by
    obtain ⟨hwE, hxwcard⟩ := Finset.mem_filter.mp hw
    have hwS : w ∈ S := (Finset.mem_erase.mp hwE).2
    have hzw : (diff z w).card ≤ 2 := by
      by_cases he : z = w
      · subst w
        simp [diff]
      · exact (hpair z hzS w hwS he).le
    exact card_sdiff_le_one x z w hxzcard hxwcard hzw
  have hcover' : Finset.univ ⊆ A ∪ (T x).biUnion (fun w => diff x w \ A) := by
    intro i hi
    obtain ⟨w, hw, hiw⟩ := Finset.mem_biUnion.mp (hcover x hx hi)
    by_cases hiA : i ∈ A
    · exact Finset.mem_union.mpr (Or.inl hiA)
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_sdiff.mpr ⟨hiw, hiA⟩⟩))
  have hsum : (∑ w ∈ T x, (diff x w \ A).card) ≤ (T x).card := by
    calc
      (∑ w ∈ T x, (diff x w \ A).card) ≤ ∑ _w ∈ T x, 1 :=
        Finset.sum_le_sum hout
      _ = (T x).card := by simp
  have hnsmall : n ≤ 7 := by
    calc
      n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ (A ∪ (T x).biUnion (fun w => diff x w \ A)).card :=
        Finset.card_le_card hcover'
      _ ≤ A.card + ((T x).biUnion (fun w => diff x w \ A)).card :=
        Finset.card_union_le _ _
      _ ≤ A.card + ∑ w ∈ T x, (diff x w \ A).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
      _ ≤ 2 + (T x).card := by
        rw [hA]
        exact Nat.add_le_add_left hsum 2
      _ ≤ 7 := by omega
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
