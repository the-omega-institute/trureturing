/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CubeNineSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CubeNineSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Small cube supports without singleton neighbors are full nine-stars. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
import Batteries.Tactic.OpenPrivate

/-! Classification of small nine-cube supports with no singleton neighbor. -/

set_option autoImplicit false

noncomputable section


namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CubeNineSupport

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q)
open private diff diff_flip directions_covered from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport

abbrev Q9 := BalancedCriticalSpectrum.Q 9

open Classical in
private def twoNeighbors (S : Finset Q9) (x : Q9) : Finset Q9 :=
  (S.erase x).filter (fun z => (diff x z).card = 2)

open Classical in
private theorem diff_self {n : Nat} (x : Q n) : diff x x = ∅ := by
  classical
  ext i
  simp [diff]

open Classical in
private theorem diff_symm {n : Nat} (x y : Q n) : diff x y = diff y x := by
  classical
  ext i
  simp [diff, ne_comm]

open Classical in
private theorem diff_empty_iff {n : Nat} (x y : Q n) : diff x y = ∅ ↔ x = y := by
  classical
  constructor
  · intro h
    funext i
    by_contra hi
    have : i ∈ diff x y := by simp [diff, hi]
    rw [h] at this
    simp at this
  · rintro rfl
    exact diff_self x

open Classical in
private theorem diff_triangle {n : Nat} (x y z : Q n) :
    diff x y = (diff x z \ diff y z) ∪ (diff y z \ diff x z) := by
  classical
  ext i
  cases hx : x i <;> cases hy : y i <;> cases hz : z i <;>
    simp [diff, hx, hy, hz]

open Classical in
private theorem diff_triangle_card {n : Nat} (x y z : Q n) :
    (diff x y).card + 2 * (diff x z ∩ diff y z).card =
      (diff x z).card + (diff y z).card := by
  classical
  have hd : Disjoint (diff x z \ diff y z) (diff y z \ diff x z) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have hA := Finset.card_sdiff_add_card_inter (diff x z) (diff y z)
  have hB := Finset.card_sdiff_add_card_inter (diff y z) (diff x z)
  rw [Finset.inter_comm (diff y z) (diff x z)] at hB
  rw [diff_triangle x y z, Finset.card_union_of_disjoint hd]
  omega

open Classical in
private theorem mem_twoNeighbors {S : Finset Q9} {x z : Q9} :
    z ∈ twoNeighbors S x ↔ z ∈ S ∧ z ≠ x ∧ (diff x z).card = 2 := by
  classical
  simp [twoNeighbors, and_assoc, and_comm]

open Classical in
private theorem twoNeighbors_card_ge_five (S : Finset Q9)
    (hno : ∀ y : Q9, (S.filter (fun z => (hypercube 9).Adj y z)).card ≠ 1)
    {x : Q9} (hx : x ∈ S) : 5 ≤ (twoNeighbors S x).card := by
  classical
  have hcover : Finset.univ ⊆ (twoNeighbors S x).biUnion (diff x) :=
    directions_covered S hno hx
  have hsum : ∑ z ∈ twoNeighbors S x, (diff x z).card =
      2 * (twoNeighbors S x).card := by
    calc
      _ = ∑ _z ∈ twoNeighbors S x, 2 := by
        apply Finset.sum_congr rfl
        intro z hz
        exact (mem_twoNeighbors.mp hz).2.2
      _ = _ := by simp [Nat.mul_comm]
  have h := (Finset.card_le_card hcover).trans
    (Finset.card_biUnion_le (s := twoNeighbors S x) (t := diff x))
  rw [hsum] at h
  have hU : (Finset.univ : Finset (Fin 9)).card = 9 := by simp
  rw [hU] at h
  omega

open Classical in
private theorem common_two_subset_of_four {x y w : Q9}
    (hxy : (diff x y).card = 4)
    (hxw : (diff x w).card = 2) (hyw : (diff y w).card = 2) :
    diff x w ⊆ diff x y := by
  classical
  have hc := diff_triangle_card x y w
  have hzero : (diff x w ∩ diff y w).card = 0 := by omega
  have hempty := Finset.card_eq_zero.mp hzero
  intro i hi
  rw [diff_triangle x y w]
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_sdiff.mpr
  refine ⟨hi, ?_⟩
  intro hj
  have hij := Finset.mem_inter.mpr ⟨hi, hj⟩
  rw [hempty] at hij
  simp at hij

open Classical in
private theorem two_union_card_le (S : Finset Q9) (x : Q9)
    (T : Finset Q9) (hT : T ⊆ twoNeighbors S x) :
    (T.biUnion (diff x)).card ≤ 2 * T.card := by
  classical
  calc
    _ ≤ ∑ z ∈ T, (diff x z).card := Finset.card_biUnion_le
    _ = ∑ _z ∈ T, 2 := by
      apply Finset.sum_congr rfl
      intro z hz
      exact (mem_twoNeighbors.mp (hT hz)).2.2
    _ = _ := by simp [Nat.mul_comm]

open Classical in
private theorem exclusive_card_ge_three (S : Finset Q9)
    (hno : ∀ y : Q9, (S.filter (fun z => (hypercube 9).Adj y z)).card ≠ 1)
    {x y : Q9} (hx : x ∈ S) (hxy : (diff x y).card = 4) :
    3 ≤ (twoNeighbors S x \ twoNeighbors S y).card := by
  classical
  have hcover : Finset.univ \ diff x y ⊆
      (twoNeighbors S x \ twoNeighbors S y).biUnion (diff x) := by
    intro i hi
    obtain ⟨w, hw, hiw⟩ := Finset.mem_biUnion.mp
      (directions_covered S hno hx (Finset.mem_sdiff.mp hi).1)
    have hwx : w ∈ twoNeighbors S x := hw
    have hwn : w ∉ twoNeighbors S y := by
      intro hwy
      exact (Finset.mem_sdiff.mp hi).2
        (common_two_subset_of_four hxy (mem_twoNeighbors.mp hwx).2.2
          (mem_twoNeighbors.mp hwy).2.2 hiw)
    exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_sdiff.mpr ⟨hwx, hwn⟩, hiw⟩
  have houtside : (Finset.univ \ diff x y).card = 5 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, hxy]
  have hbound := (Finset.card_le_card hcover).trans
    (two_union_card_le S x _ (fun _ hz => (Finset.mem_sdiff.mp hz).1))
  rw [houtside] at hbound
  omega

open Classical in
private theorem pair_distance_two (S : Finset Q9) (hcard : S.card ≤ 9)
    (hno : ∀ y : Q9, (S.filter (fun z => (hypercube 9).Adj y z)).card ≠ 1)
    {x y : Q9} (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) :
    (diff x y).card = 2 := by
  classical
  by_contra htwo
  have hpos : 0 < (diff x y).card := by
    apply Finset.card_pos.mpr
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    exact hne ((diff_empty_iff x y).mp he)
  have hnx := twoNeighbors_card_ge_five S hno hx
  have hny := twoNeighbors_card_ge_five S hno hy
  have hsubset : twoNeighbors S x ∪ twoNeighbors S y ⊆ (S.erase x).erase y := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨hwS, hwx, hdist⟩ := mem_twoNeighbors.mp hw
      have hwy : w ≠ y := by
        intro he
        subst w
        exact htwo hdist
      exact Finset.mem_erase.mpr ⟨hwy, Finset.mem_erase.mpr ⟨hwx, hwS⟩⟩
    · obtain ⟨hwS, hwy, hdist⟩ := mem_twoNeighbors.mp hw
      have hwx : w ≠ x := by
        intro he
        subst w
        rw [diff_symm y x] at hdist
        exact htwo hdist
      exact Finset.mem_erase.mpr ⟨hwy, Finset.mem_erase.mpr ⟨hwx, hwS⟩⟩
  have hyerase : y ∈ S.erase x := Finset.mem_erase.mpr ⟨hne.symm, hy⟩
  have hsmall : (twoNeighbors S x ∪ twoNeighbors S y).card ≤ 7 := by
    have hle := Finset.card_le_card hsubset
    have he1 := Finset.card_erase_add_one hx
    have he2 := Finset.card_erase_add_one hyerase
    omega
  have hcount := Finset.card_union_add_card_inter (twoNeighbors S x) (twoNeighbors S y)
  by_cases hfour : (diff x y).card = 4
  · have hp := exclusive_card_ge_three S hno hx hfour
    have hyx : (diff y x).card = 4 := by rw [diff_symm y x]; exact hfour
    have hq := exclusive_card_ge_three S hno hy hyx
    have hpx := Finset.card_sdiff_add_card_inter (twoNeighbors S x) (twoNeighbors S y)
    have hqy := Finset.card_sdiff_add_card_inter (twoNeighbors S y) (twoNeighbors S x)
    rw [Finset.inter_comm (twoNeighbors S y) (twoNeighbors S x)] at hqy
    omega
  · have hempty : twoNeighbors S x ∩ twoNeighbors S y = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨hwx, hwy⟩ := Finset.mem_inter.mp hw
      have hcx := (mem_twoNeighbors.mp hwx).2.2
      have hcy := (mem_twoNeighbors.mp hwy).2.2
      have htri := diff_triangle_card x y w
      omega
    rw [hempty, Finset.card_empty] at hcount
    omega

open Classical in
private theorem pair_with_mem (A : Finset (Fin 9)) (hA : A.card = 2)
    {a : Fin 9} (ha : a ∈ A) : ∃ b, a ≠ b ∧ A = {a, b} := by
  classical
  obtain ⟨u, v, huv, hpair⟩ := Finset.card_eq_two.mp hA
  rw [hpair] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact ⟨v, huv, hpair⟩
  · exact ⟨u, huv.symm, by simpa [Finset.pair_comm] using hpair⟩

open Classical in
private theorem common_direction (T : Finset Q9) (f : Q9 → Finset (Fin 9))
    (hsize : ∀ z ∈ T, (f z).card = 2)
    (hmeet : ∀ z ∈ T, ∀ w ∈ T, (f z ∩ f w).Nonempty)
    (hcover : Finset.univ ⊆ T.biUnion f) :
    ∃ j : Fin 9, ∀ z ∈ T, j ∈ f z := by
  classical
  obtain ⟨A, hAT, _⟩ := Finset.mem_biUnion.mp (hcover (Finset.mem_univ (0 : Fin 9)))
  obtain ⟨a, b, hab, hA⟩ := Finset.card_eq_two.mp (hsize A hAT)
  by_cases ha : ∀ z ∈ T, a ∈ f z
  · exact ⟨a, ha⟩
  push Not at ha
  obtain ⟨B, hBT, haB⟩ := ha
  have hbB : b ∈ f B := by
    obtain ⟨i, hi⟩ := hmeet A hAT B hBT
    obtain ⟨hiA, hiB⟩ := Finset.mem_inter.mp hi
    rw [hA] at hiA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hiA
    rcases hiA with rfl | rfl
    · exact (haB hiB).elim
    · exact hiB
  obtain ⟨c, hbc, hB⟩ := pair_with_mem (f B) (hsize B hBT) hbB
  have hac : a ≠ c := by
    intro he
    apply haB
    rw [hB]
    simp [he]
  by_cases hb : ∀ z ∈ T, b ∈ f z
  · exact ⟨b, hb⟩
  push Not at hb
  obtain ⟨C, hCT, hbC⟩ := hb
  have haC : a ∈ f C := by
    obtain ⟨i, hi⟩ := hmeet A hAT C hCT
    obtain ⟨hiA, hiC⟩ := Finset.mem_inter.mp hi
    rw [hA] at hiA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hiA
    rcases hiA with rfl | rfl
    · exact hiC
    · exact (hbC hiC).elim
  obtain ⟨d, had, hC⟩ := pair_with_mem (f C) (hsize C hCT) haC
  have hbd : b ≠ d := by
    intro he
    apply hbC
    rw [hC]
    simp [he]
  have hdc : d = c := by
    obtain ⟨i, hi⟩ := hmeet B hBT C hCT
    simp only [Finset.mem_inter, hB, hC, Finset.mem_insert,
      Finset.mem_singleton] at hi
    rcases hi with ⟨(rfl | rfl), hiC⟩
    · rcases hiC with hba | hbd'
      · exact (hab hba.symm).elim
      · exact (hbd hbd').elim
    · rcases hiC with hca | hcd
      · exact (hac hca.symm).elim
      · exact hcd.symm
  subst d
  have htriangle : ∀ z ∈ T, f z ⊆ {a, b, c} := by
    intro z hz
    obtain ⟨u, v, huv, hpair⟩ := Finset.card_eq_two.mp (hsize z hz)
    obtain ⟨i, hi⟩ := hmeet z hz A hAT
    obtain ⟨j, hj⟩ := hmeet z hz B hBT
    obtain ⟨k, hk⟩ := hmeet z hz C hCT
    simp only [Finset.mem_inter, hpair, hA, hB, hC, Finset.mem_insert,
      Finset.mem_singleton] at hi hj hk
    intro t ht
    simp only [hpair, Finset.mem_insert, Finset.mem_singleton] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton]
    clear hsize hmeet hcover
    grind
  have hsub : (Finset.univ : Finset (Fin 9)) ⊆ {a, b, c} := by
    intro i hi
    obtain ⟨z, hz, hiz⟩ := Finset.mem_biUnion.mp (hcover hi)
    exact htriangle z hz hiz
  have hbound := (Finset.card_le_card hsub).trans Finset.card_le_three
  simp only [Finset.card_univ, Fintype.card_fin] at hbound
  omega

open Classical in
private theorem eq_neighbors_of_pair_distance_two
    (S : Finset (BalancedCriticalSpectrum.Q 9)) (hS : S.Nonempty)
    (hno : ∀ y : BalancedCriticalSpectrum.Q 9,
      (S.filter (fun x => (hypercube 9).Adj y x)).card ≠ 1)
    (hall : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → (diff x y).card = 2) :
    ∃ y : BalancedCriticalSpectrum.Q 9,
      S = Finset.univ.filter (fun x => (hypercube 9).Adj y x) := by
  classical
  obtain ⟨x, hx⟩ := hS
  let T := S.erase x
  have hsize : ∀ z ∈ T, (diff x z).card = 2 := by
    intro z hz
    obtain ⟨hzx, hzS⟩ := Finset.mem_erase.mp hz
    exact hall x hx z hzS hzx.symm
  have hcover : Finset.univ ⊆ T.biUnion (diff x) := by
    intro i hi
    obtain ⟨z, hz, hiz⟩ := Finset.mem_biUnion.mp (directions_covered S hno hx hi)
    have hzT : z ∈ T := by
      obtain ⟨hzS, hzx, _⟩ := mem_twoNeighbors.mp hz
      exact Finset.mem_erase.mpr ⟨hzx, hzS⟩
    exact Finset.mem_biUnion.mpr ⟨z, hzT, hiz⟩
  have hmeet : ∀ z ∈ T, ∀ w ∈ T, (diff x z ∩ diff x w).Nonempty := by
    intro z hz w hw
    have hzS := (Finset.mem_erase.mp hz).2
    have hwS := (Finset.mem_erase.mp hw).2
    have hdist : (diff z w).card ≤ 2 := by
      by_cases he : z = w
      · subst w
        simp [diff_self]
      · exact le_of_eq (hall z hzS w hwS he)
    have htri := diff_triangle_card z w x
    rw [diff_symm z x, diff_symm w x] at htri
    have hsz := hsize z hz
    have hsw := hsize w hw
    have hpos : 0 < (diff x z ∩ diff x w).card := by omega
    exact Finset.card_pos.mp hpos
  obtain ⟨j, hj⟩ := common_direction T (diff x) hsize hmeet hcover
  let center := BalancedCriticalSpectrum.flip x j
  have hsubset : S ⊆ Finset.univ.filter (fun z => (hypercube 9).Adj center z) := by
    intro z hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ z, ?_⟩
    by_cases he : z = x
    · subst z
      exact SimpleGraph.Adj.symm (BalancedCriticalSpectrum.flip_adj x j)
    · have hzT : z ∈ T := Finset.mem_erase.mpr ⟨he, hz⟩
      have hjz := hj z hzT
      have hsz := hsize z hzT
      have hec := Finset.card_erase_add_one hjz
      change (diff (BalancedCriticalSpectrum.flip x j) z).card = 1
      rw [diff_flip, ite_eq_left hjz]
      omega
  have hcoverErase : Finset.univ ⊆ insert j (T.biUnion (fun z => (diff x z).erase j)) := by
    intro i hi
    by_cases he : i = j
    · exact Finset.mem_insert.mpr (Or.inl he)
    · obtain ⟨z, hz, hiz⟩ := Finset.mem_biUnion.mp (hcover hi)
      exact Finset.mem_insert.mpr (Or.inr
        (Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_erase.mpr ⟨he, hiz⟩⟩))
  have hsum : ∑ z ∈ T, ((diff x z).erase j).card = T.card := by
    calc
      _ = ∑ _z ∈ T, 1 := by
        apply Finset.sum_congr rfl
        intro z hz
        have hsz := hsize z hz
        have hec := Finset.card_erase_add_one (hj z hz)
        omega
      _ = _ := by simp
  have herase := Finset.card_erase_add_one hx
  have hbi := Finset.card_biUnion_le (s := T) (t := fun z => (diff x z).erase j)
  rw [hsum] at hbi
  have hlow := (Finset.card_le_card hcoverErase).trans
    (Finset.card_insert_le j (T.biUnion (fun z => (diff x z).erase j)))
  have hU : (Finset.univ : Finset (Fin 9)).card = 9 := by simp
  rw [hU] at hlow
  have hTcard : T.card + 1 = S.card := herase
  have hneighbor : (Finset.univ.filter (fun z => (hypercube 9).Adj center z)).card = 9 := by
    rw [← SimpleGraph.neighborFinset_eq_filter,
      SimpleGraph.card_neighborFinset_eq_degree, (hypercube_regular 9).degree_eq]
  have hupper := Finset.card_le_card hsubset
  rw [hneighbor] at hupper
  have hScard : S.card = 9 := by omega
  refine ⟨center, Finset.eq_of_subset_of_card_le hsubset ?_⟩
  omega


open Classical in
theorem eq_neighbors_of_no_singleton
    (S : Finset (BalancedCriticalSpectrum.Q 9)) (hS : S.Nonempty) (hcard : S.card ≤ 9)
    (hno : ∀ y : BalancedCriticalSpectrum.Q 9,
      (S.filter (fun x => (hypercube 9).Adj y x)).card ≠ 1) :
    ∃ y : BalancedCriticalSpectrum.Q 9,
      S = Finset.univ.filter (fun x => (hypercube 9).Adj y x) := by
  apply eq_neighbors_of_pair_distance_two S hS hno
  intro x hx y hy hne
  exact pair_distance_two S hcard hno hx hy hne

end D5.S3.Combinatorics.Graph.HypercubeCritical.CubeNineSupport
