/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CubeTwelveSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CubeTwelveSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Single-parity supports of at most twelve vertices are full nine-stars. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CubeNineSupport
import Batteries.Tactic.OpenPrivate

/-! A classification of nonempty nine-cube supports of size at most twelve.
The parity assumption is stated as evenness of the actual Hamming difference
cardinalities. No auxiliary operator or certificate occurs in the statement. -/

set_option autoImplicit false

noncomputable section


namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CubeTwelveSupport

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open CubeNineSupport (Q9)
open private diff directions_covered from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private twoNeighbors mem_twoNeighbors diff_self diff_symm diff_empty_iff
  diff_triangle diff_triangle_card twoNeighbors_card_ge_five
  common_two_subset_of_four two_union_card_le common_direction
  eq_neighbors_of_pair_distance_two from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeNineSupport

-- Two disjoint five-point packs avoiding two distinguished points exhaust S.
open Classical in
private theorem pack (S P Q : Finset Q9) {x y : Q9}
    (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) (hcard : S.card ≤ 12)
    (hP : P ⊆ (S.erase x).erase y) (hQ : Q ⊆ (S.erase x).erase y)
    (hd : Disjoint P Q) (hp : 5 ≤ P.card) (hq : 5 ≤ Q.card) :
    P.card = 5 ∧ Q.card = 5 ∧ S = insert x (insert y (P ∪ Q)) := by
  have hsub : P ∪ Q ⊆ (S.erase x).erase y := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hP hz
    · exact hQ hz
  have hc := Finset.card_le_card hsub
  have he := Finset.card_erase_add_one hx
  have hyE : y ∈ S.erase x := Finset.mem_erase.mpr ⟨hne.symm, hy⟩
  have hf := Finset.card_erase_add_one hyE
  rw [Finset.card_union_of_disjoint hd] at hc
  have hpc : P.card = 5 := by omega
  have hqc : Q.card = 5 := by omega
  have heq : P ∪ Q = (S.erase x).erase y :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_union_of_disjoint hd]
      omega)
  refine ⟨hpc, hqc, ?_⟩
  rw [heq]
  ext z
  simp only [Finset.mem_insert, Finset.mem_erase]
  by_cases hzx : z = x <;> by_cases hzy : z = y <;> simp_all

open Classical in
private theorem neighbor_avoids (S : Finset Q9) {x y : Q9}
    (hxy : (diff x y).card ≠ 2) :
    twoNeighbors S x ⊆ (S.erase x).erase y := by
  intro z hz
  obtain ⟨hzS, hzx, hxz⟩ := mem_twoNeighbors.mp hz
  refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨hzx, hzS⟩⟩
  intro he
  subst z
  exact hxy hxz

open Classical in
private theorem small_growth {x z w : Q9}
    (hz : (diff x z).card = 2) (hw : (diff x w).card = 2)
    (hzw : (diff z w).card = 2) : (diff x w \ diff x z).card ≤ 1 := by
  have ht := diff_triangle_card z w x
  rw [diff_symm z x, diff_symm w x] at ht
  have hs := Finset.card_sdiff_add_card_inter (diff x w) (diff x z)
  rw [Finset.inter_comm (diff x w) (diff x z)] at hs
  omega

-- A far pair forces two five-point packs; local coverage then needs at most six
-- directions, contradicting the nine directions actually covered.
open Classical in
private theorem distance_le_four (S : Finset Q9) (hcard : S.card ≤ 12)
    (hno : ∀ v : Q9, (S.filter (fun z => (hypercube 9).Adj v z)).card ≠ 1)
    (heven : ∀ x ∈ S, ∀ y ∈ S, Even (diff x y).card)
    {x y : Q9} (hx : x ∈ S) (hy : y ∈ S) : (diff x y).card ≤ 4 := by
  by_contra hbad
  have hfar : 6 ≤ (diff x y).card := by
    obtain ⟨k, hk⟩ := heven x hx y hy
    omega
  have hbound : (diff x y).card ≤ 9 := by
    have := Finset.card_le_card (Finset.subset_univ (diff x y))
    simpa using this
  have hupper : (diff x y).card ≤ 8 := by
    obtain ⟨k, hk⟩ := heven x hx y hy
    omega
  have hne : x ≠ y := by
    intro he
    subst y
    simp [diff_self] at hfar
  let P := twoNeighbors S x
  let Q := twoNeighbors S y
  have hP : P ⊆ (S.erase x).erase y := neighbor_avoids S (by omega)
  have hQ : Q ⊆ (S.erase x).erase y := by
    intro z hz
    have hh := neighbor_avoids S (x := y) (y := x)
      (by rw [diff_symm y x]; omega) hz
    simpa only [Finset.mem_erase, and_left_comm] using hh
  have hd : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    have hp := (mem_twoNeighbors.mp hz).2.2
    have hq := (mem_twoNeighbors.mp hz').2.2
    have ht := diff_triangle_card x y z
    omega
  obtain ⟨hp, hq, hS⟩ := pack S P Q hx hy hne hcard hP hQ hd
    (twoNeighbors_card_ge_five S hno hx) (twoNeighbors_card_ge_five S hno hy)
  have hout : (Finset.univ \ diff x y).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨i, hi⟩ := hout
  obtain ⟨z, hz, hiz⟩ := Finset.mem_biUnion.mp
    (directions_covered S hno hx (Finset.mem_sdiff.mp hi).1)
  have hzP : z ∈ P := hz
  have hzS := (mem_twoNeighbors.mp hz).1
  have hxz := (mem_twoNeighbors.mp hz).2.2
  have hinter : (diff x z ∩ diff x y).card ≤ 1 := by
    have hle := Finset.card_le_card (Finset.inter_subset_left :
      diff x z ∩ diff x y ⊆ diff x z)
    by_contra hh
    have he : diff x z ∩ diff x y = diff x z :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have : i ∈ diff x z ∩ diff x y := by rw [he]; exact hiz
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp this).2
  have hzy : 6 ≤ (diff z y).card := by
    have ht := diff_triangle_card z y x
    rw [diff_symm z x, diff_symm y x] at ht
    omega
  have hzQ : z ∉ Q := by
    intro hh
    have hh' := (mem_twoNeighbors.mp hh).2.2
    rw [diff_symm y z] at hh'
    omega
  have hN : twoNeighbors S z = insert x (P.erase z) := by
    have hsub : twoNeighbors S z ⊆ insert x (P.erase z) := by
      intro w hw
      obtain ⟨hwS, hwz, hzw⟩ := mem_twoNeighbors.mp hw
      rw [hS] at hwS
      simp only [Finset.mem_insert, Finset.mem_union] at hwS
      rcases hwS with rfl | rfl | hwP | hwQ
      · simp
      · omega
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwz, hwP⟩)
      · have hyw := (mem_twoNeighbors.mp hwQ).2.2
        have ht := diff_triangle_card z y w
        omega
    have hcz := (Finset.card_erase_add_one hzP).trans hp
    have hcx : x ∉ P.erase z := by
      intro hh
      exact (mem_twoNeighbors.mp (Finset.mem_erase.mp hh).2).2.1 rfl
    have hc : (insert x (P.erase z)).card = 5 := by
      rw [Finset.card_insert_of_notMem hcx]
      omega
    exact Finset.eq_of_subset_of_card_le hsub (by
      rw [hc]
      exact twoNeighbors_card_ge_five S hno hzS)
  have hg : ∀ w ∈ P.erase z, (diff x w \ diff x z).card ≤ 1 := by
    intro w hw
    have hwP := (Finset.mem_erase.mp hw).2
    have hwz : w ∈ twoNeighbors S z := by rw [hN]; simp [hw]
    exact small_growth hxz (mem_twoNeighbors.mp hwP).2.2
      (mem_twoNeighbors.mp hwz).2.2
  have hcover : Finset.univ ⊆ diff x z ∪
      (P.erase z).biUnion (fun w => diff x w \ diff x z) := by
    intro j hj
    obtain ⟨w, hw, hjw⟩ := Finset.mem_biUnion.mp (directions_covered S hno hx hj)
    by_cases hjz : j ∈ diff x z
    · exact Finset.mem_union.mpr (Or.inl hjz)
    · have hwz : w ≠ z := by intro he; subst w; exact hjz hjw
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨w, Finset.mem_erase.mpr ⟨hwz, hw⟩, Finset.mem_sdiff.mpr ⟨hjw, hjz⟩⟩))
  have hsum : (∑ w ∈ P.erase z, (diff x w \ diff x z).card) ≤ (P.erase z).card := by
    calc
      _ ≤ ∑ _w ∈ P.erase z, 1 := Finset.sum_le_sum hg
      _ = _ := by simp
  have hcov := Finset.card_le_card hcover
  have hun := Finset.card_union_le (diff x z)
    ((P.erase z).biUnion (fun w => diff x w \ diff x z))
  have hbi := Finset.card_biUnion_le (s := P.erase z)
    (t := fun w => diff x w \ diff x z)
  have her := (Finset.card_erase_add_one hzP).trans hp
  simp only [Finset.card_univ, Fintype.card_fin] at hcov
  omega

-- Every exclusive distance-two point has one direction in D and one outside D.
open Classical in
private theorem exclusive_pair {x y z : Q9}
    (hxy : (diff x y).card = 4) (hxz : (diff x z).card = 2)
    (hyz : (diff y z).card ≤ 4) (hnot : (diff y z).card ≠ 2) :
    ∃ a p : Fin 9, a ∈ diff x y ∧ p ∉ diff x y ∧ diff x z = {a, p} := by
  have ht := diff_triangle_card y z x
  rw [diff_symm y x, diff_symm z x] at ht
  have hb := Finset.card_le_card (Finset.inter_subset_right :
    diff x y ∩ diff x z ⊆ diff x z)
  have hc : (diff x y ∩ diff x z).card = 1 := by omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
  have ham : a ∈ diff x y ∩ diff x z := by rw [ha]; simp
  obtain ⟨u, v, huv, huvEq⟩ := Finset.card_eq_two.mp hxz
  have haA := (Finset.mem_inter.mp ham).2
  rw [huvEq] at haA
  simp only [Finset.mem_insert, Finset.mem_singleton] at haA
  have hother : ∀ p ∈ diff x z, p ≠ a → p ∉ diff x y := by
    intro p hp hpa hpD
    have : p ∈ diff x y ∩ diff x z := Finset.mem_inter.mpr ⟨hpD, hp⟩
    rw [ha] at this
    exact hpa (Finset.mem_singleton.mp this)
  rcases haA with hau | hav
  · subst a
    exact ⟨u, v, (Finset.mem_inter.mp ham).1,
      hother v (by rw [huvEq]; simp) huv.symm, huvEq⟩
  · subst a
    exact ⟨v, u, (Finset.mem_inter.mp ham).1,
      hother u (by rw [huvEq]; simp) huv, by simpa [Finset.pair_comm] using huvEq⟩

open Classical in
private theorem diff_injective {x z w : Q9} (h : diff x z = diff x w) : z = w := by
  funext i
  have hi : (x i ≠ z i) ↔ (x i ≠ w i) := by
    simpa only [diff, Finset.mem_filter, Finset.mem_univ, true_and] using
      Finset.ext_iff.mp h i
  clear h
  cases hx : x i <;> cases hz : z i <;> cases hw : w i <;>
    simp_all [diff]

open Classical in
private theorem cross_six {x y z w : Q9} {a p q : Fin 9}
    (hD : (diff x y).card = 4) (ha : a ∈ diff x y)
    (hp : p ∉ diff x y) (hq : q ∉ diff x y) (hpq : p ≠ q)
    (hz : diff x z = {a, p}) (hw : diff y w = {a, q}) :
    (diff z w).card = 6 := by
  have hpa : p ≠ a := by intro he; subst p; exact hp ha
  have hqa : q ≠ a := by intro he; subst q; exact hq ha
  have he : diff z w = insert p (insert q (diff x y)) := by
    ext i
    have hiz := Finset.ext_iff.mp hz i
    have hiw := Finset.ext_iff.mp hw i
    have hia : i = a → x i ≠ y i := by intro he; subst i; simpa [diff] using ha
    have hip : i = p → x i = y i := by intro he; subst i; simpa [diff] using hp
    have hiq : i = q → x i = y i := by intro he; subst i; simpa [diff] using hq
    cases hx : x i <;> cases hy : y i <;> cases hzi : z i <;> cases hwi : w i <;>
      simp only [diff, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton, hx, hy, hzi, hwi] at * <;> grind
  rw [he, Finset.card_insert_of_notMem (by simp [hp, hpq]),
    Finset.card_insert_of_notMem hq, hD]

open Classical in
private theorem exclusive_card_ge_five (S : Finset Q9)
    (hno : ∀ v : Q9, (S.filter (fun z => (hypercube 9).Adj v z)).card ≠ 1)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, (diff x y).card ≤ 4)
    {x y : Q9} (hx : x ∈ S) (hy : y ∈ S) (hxy : (diff x y).card = 4) :
    5 ≤ (twoNeighbors S x \ twoNeighbors S y).card := by
  let P := twoNeighbors S x \ twoNeighbors S y
  have hpairs : ∀ z ∈ P, ∃ a p : Fin 9,
      a ∈ diff x y ∧ p ∉ diff x y ∧ diff x z = {a, p} := by
    intro z hz
    obtain ⟨hzx, hzy⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨hzS, _, hxz⟩ := mem_twoNeighbors.mp hzx
    apply exclusive_pair hxy hxz (hdiam y hy z hzS)
    intro hyz
    have hne : z ≠ y := by intro he; subst z; omega
    exact hzy (mem_twoNeighbors.mpr ⟨hzS, hne, hyz⟩)
  have hcover : Finset.univ \ diff x y ⊆ P.biUnion (fun z => diff x z \ diff x y) := by
    intro i hi
    obtain ⟨z, hz, hiz⟩ := Finset.mem_biUnion.mp
      (directions_covered S hno hx (Finset.mem_sdiff.mp hi).1)
    have hzy : z ∉ twoNeighbors S y := by
      intro hh
      exact (Finset.mem_sdiff.mp hi).2
        (common_two_subset_of_four hxy (mem_twoNeighbors.mp hz).2.2
          (mem_twoNeighbors.mp hh).2.2 hiz)
    exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_sdiff.mpr ⟨hz, hzy⟩,
      Finset.mem_sdiff.mpr ⟨hiz, (Finset.mem_sdiff.mp hi).2⟩⟩
  have hg : ∀ z ∈ P, (diff x z \ diff x y).card ≤ 1 := by
    intro z hz
    obtain ⟨a, p, ha, hp, he⟩ := hpairs z hz
    have hs : diff x z \ diff x y ⊆ {p} := by
      intro i hi
      obtain ⟨hiA, hiD⟩ := Finset.mem_sdiff.mp hi
      rw [he] at hiA
      simp only [Finset.mem_insert, Finset.mem_singleton] at hiA
      rcases hiA with rfl | rfl
      · exact (hiD ha).elim
      · simp
    simpa using Finset.card_le_card hs
  have hsum : (∑ z ∈ P, (diff x z \ diff x y).card) ≤ P.card := by
    calc
      _ ≤ ∑ _z ∈ P, 1 := Finset.sum_le_sum hg
      _ = _ := by simp
  have hc := (Finset.card_le_card hcover).trans
    (Finset.card_biUnion_le (s := P) (t := fun z => diff x z \ diff x y))
  have hout : (Finset.univ \ diff x y).card = 5 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [hxy]
  rw [hout] at hc
  exact hc.trans hsum

open Classical in
private theorem distance_ne_four (S : Finset Q9) (hcard : S.card ≤ 12)
    (hno : ∀ v : Q9, (S.filter (fun z => (hypercube 9).Adj v z)).card ≠ 1)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, (diff x y).card ≤ 4)
    {x y : Q9} (hx : x ∈ S) (hy : y ∈ S) : (diff x y).card ≠ 4 := by
  intro hxy
  have hyx : (diff y x).card = 4 := by rw [diff_symm y x]; exact hxy
  have hne : x ≠ y := by intro he; subst y; simp [diff_self] at hxy
  let P := twoNeighbors S x \ twoNeighbors S y
  let Q := twoNeighbors S y \ twoNeighbors S x
  have hP : P ⊆ (S.erase x).erase y := fun _ hz =>
    neighbor_avoids S (by omega) (Finset.mem_sdiff.mp hz).1
  have hQ : Q ⊆ (S.erase x).erase y := by
    intro z hz
    have hh := neighbor_avoids S (x := y) (y := x) (by omega)
      (Finset.mem_sdiff.mp hz).1
    simpa only [Finset.mem_erase, and_left_comm] using hh
  have hd : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact (Finset.mem_sdiff.mp hz).2 (Finset.mem_sdiff.mp hz').1
  obtain ⟨hp, hq, hS⟩ := pack S P Q hx hy hne hcard hP hQ hd
    (exclusive_card_ge_five S hno hdiam hx hy hxy)
    (exclusive_card_ge_five S hno hdiam hy hx hyx)
  have hNy : twoNeighbors S y = Q := by
    apply Finset.Subset.antisymm
    · intro z hz
      have hzS := (mem_twoNeighbors.mp hz).1
      have hzy := (mem_twoNeighbors.mp hz).2.1
      have hzx : z ≠ x := by intro he; subst z; have := (mem_twoNeighbors.mp hz).2.2; omega
      rw [hS] at hzS
      simp only [Finset.mem_insert, Finset.mem_union] at hzS
      rcases hzS with he | he | hh | hh
      · exact (hzx he).elim
      · exact (hzy he).elim
      · exact ((Finset.mem_sdiff.mp hh).2 hz).elim
      · exact hh
    · exact fun _ hz => (Finset.mem_sdiff.mp hz).1
  have hpairs : ∀ z : P, ∃ a p : Fin 9,
      a ∈ diff x y ∧ p ∉ diff x y ∧ diff x z = {a, p} := by
    intro z
    have hz := (mem_twoNeighbors.mp ((Finset.mem_sdiff.mp z.property).1))
    apply exclusive_pair hxy hz.2.2 (hdiam y hy z hz.1)
    intro hh
    exact (Finset.mem_sdiff.mp z.property).2
      (mem_twoNeighbors.mpr ⟨hz.1, by
        intro he
        have hc := hz.2.2
        rw [he] at hc
        omega, hh⟩)
  choose a p ha hpD hpair using hpairs
  have hinj : Function.Injective a := by
    intro z z' he
    by_contra hzz
    have hpp : p z ≠ p z' := by
      intro hh
      apply hzz
      apply Subtype.ext
      apply diff_injective (x := x)
      rw [hpair z, hpair z', he, hh]
    obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp
      (directions_covered S hno hy (Finset.mem_univ (a z)))
    have hwS := (mem_twoNeighbors.mp hw).1
    have hwQ : w ∈ Q := by rw [← hNy]; exact hw
    have hxwNot : (diff x w).card ≠ 2 := by
      intro hh
      exact (Finset.mem_sdiff.mp hwQ).2
        (mem_twoNeighbors.mpr ⟨hwS, by
          intro hew
          subst w
          have := (mem_twoNeighbors.mp hw).2.2
          omega, hh⟩)
    obtain ⟨b, q, hb, hqD, hwPair⟩ := exclusive_pair hyx
      (mem_twoNeighbors.mp hw).2.2 (hdiam x hx w hwS) hxwNot
    have hqD' : q ∉ diff x y := by rwa [diff_symm y x] at hqD
    have hab : a z = b := by
      rw [hwPair] at haw
      simp only [Finset.mem_insert, Finset.mem_singleton] at haw
      rcases haw with hh | hh
      · exact hh
      · exact (hqD' (hh ▸ ha z)).elim
    have hwPair' : diff y w = {a z, q} := by rw [hab]; exact hwPair
    have hcross : ∀ t : P, a t = a z → p t ≠ q → False := by
      intro t ht hpt
      have htpair : diff x t = {a z, p t} := by rw [← ht]; exact hpair t
      have hc := cross_six hxy (ha z) (hpD t) hqD' hpt htpair hwPair'
      have htS := (mem_twoNeighbors.mp (Finset.mem_sdiff.mp t.property).1).1
      have hle := hdiam t htS w hwS
      omega
    by_cases hzq : p z = q
    · exact hcross z' he.symm (by intro hh; exact hpp (hzq.trans hh.symm))
    · exact hcross z rfl hzq
  have himage : P.attach.image a ⊆ diff x y := by
    intro i hi
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hi
    exact ha z
  have hcount := Finset.card_le_card himage
  have hcount' : (P.attach.image a).card = P.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  rw [hcount', hxy, hp] at hcount
  omega

open Classical in
/-- A nonempty support of at most twelve nine-cube vertices, with even actual
Hamming distances and no singleton cube-neighbor, is a complete neighbor star. -/
theorem eq_neighbors_of_card_le_twelve
    (S : Finset Q9) (hS : S.Nonempty) (hcard : S.card ≤ 12)
    (hno : ∀ v : Q9, (S.filter (fun z => (hypercube 9).Adj v z)).card ≠ 1)
    (heven : ∀ x ∈ S, ∀ y ∈ S,
      Even (Finset.univ.filter (fun i : Fin 9 => x i ≠ y i)).card) :
    ∃ center : Q9, S = Finset.univ.filter (fun z => (hypercube 9).Adj center z) := by
  have he : ∀ x ∈ S, ∀ y ∈ S, Even (diff x y).card := heven
  have hdiam : ∀ x ∈ S, ∀ y ∈ S, (diff x y).card ≤ 4 := by
    intro x hx y hy
    exact distance_le_four S hcard hno he hx hy
  apply eq_neighbors_of_pair_distance_two S hS hno
  intro x hx y hy hne
  have hpos : 0 < (diff x y).card := by
    apply Finset.card_pos.mpr
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hh
    exact hne ((diff_empty_iff x y).mp hh)
  have hle := hdiam x hx y hy
  have hfour := distance_ne_four S hcard hno hdiam hx hy
  obtain ⟨k, hk⟩ := he x hx y hy
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.CubeTwelveSupport
