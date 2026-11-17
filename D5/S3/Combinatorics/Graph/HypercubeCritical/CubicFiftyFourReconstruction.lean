/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CubicFiftyFourReconstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CubicFiftyFourReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Every actual balanced cubic fifty-four vertex Q9 support is a whole-cube Gray image. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.HammingSeven
import D5.S3.Combinatorics.Graph.HypercubeCritical.NineteenPointSlice
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitSupportGap

/-! Actual neighborhoods force a thin coordinate half.
Signed covariance transports its reconstruction. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction

open SimpleGraph
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced IsSwitching flip_adj directionEdges direction_edge_count)
local notation "flip" => BalancedCriticalSpectrum.flip
open BalancedCubeLowerBound (coordinateSlice)
attribute [local instance] Classical.propDecidable

open private HammingSeven.ball ball_walk root_data third_subset_ball hamming_le_walk from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HammingSeven
open private second third mem_second root_not_second second_card third_witness
  second_side third_side first_third_disjoint third_parent_unique second_neighbor_inter from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyFourLayerRegularity
open private paritySide parity_union parity_bipartite coordinate_slice_degree_cases
  low_slice_card_eq_q parts_card sum_degrees_parts from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private cubeParity cubeParity_ne_of_adj huangMatrix from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private even_diff_of_parity_eq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitSupportGap

open private diff from D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private diff_triangle_card from D5.S3.Combinatorics.Graph.HypercubeCritical.CubeNineSupport

private def reindex (p : Fin 9 ≃ Fin 9) : Q 9 ≃ Q 9 where
  toFun x k := x (p.symm k)
  invFun x k := x (p k)
  left_inv x := by funext k; simp
  right_inv x := by funext k; simp

private lemma reindex_flip (p : Fin 9 ≃ Fin 9) (x : Q 9) (i : Fin 9) :
    reindex p (flip x i) = flip (reindex p x) (p i) := by
  funext k
  by_cases hk : k = p i
  · subst k; simp [reindex, BalancedCriticalSpectrum.flip]
  · have hi : p.symm k ≠ i := by intro h; exact hk (by simpa using congrArg p h)
    simp [reindex, BalancedCriticalSpectrum.flip, hk, hi]

private lemma reindex_adj (p : Fin 9 ≃ Fin 9) (x y : Q 9) :
    (hypercube 9).Adj (reindex p x) (reindex p y) ↔ (hypercube 9).Adj x y := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := adjacent_exists_flip h
    have he := reindex_flip p x (p.symm i)
    have : y = flip x (p.symm i) := (reindex p).injective (by simpa only [Equiv.apply_symm_apply] using hi.trans (by simpa only [Equiv.apply_symm_apply] using he.symm))
    rw [this]; exact flip_adj _ _
  · intro h
    obtain ⟨i, rfl⟩ := adjacent_exists_flip h
    rw [reindex_flip]; exact flip_adj _ _

private lemma reindex_regular {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (p : Fin 9 ≃ Fin 9) :
    ((hypercube 9).induce (C.image (reindex p) : Set (Q 9))).IsRegularOfDegree 3 := by
  let e : (C : Set (Q 9)) ≃ (C.image (reindex p) : Set (Q 9)) :=
    { toFun := fun x => ⟨reindex p x, Finset.mem_image.mpr ⟨x, x.property, rfl⟩⟩
      invFun := fun y => ⟨(reindex p).symm y, by
        obtain ⟨x,hx,he⟩ := Finset.mem_image.mp y.property
        simpa [← he] using hx⟩
      left_inv := by intro x; apply Subtype.ext; exact (reindex p).symm_apply_apply x
      right_inv := by intro y; apply Subtype.ext; exact (reindex p).apply_symm_apply y }
  let f : ((hypercube 9).induce (C : Set (Q 9))) ≃g
      ((hypercube 9).induce (C.image (reindex p) : Set (Q 9))) :=
    { toEquiv := e
      map_rel_iff' := by intro x y; exact reindex_adj p x y }
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  exact (f.degree_eq x).trans (hr.degree_eq x)

private lemma reindex_balanced {C : Finset (Q 9)} (hb : IsBalanced C)
    (p : Fin 9 ≃ Fin 9) : IsBalanced (C.image (reindex p)) := by
  let g := reindex p
  obtain ⟨theta,ht,he,_⟩ := HuangCubeCovariance.exists_signed_covariance g p (reindex_flip p)
  obtain ⟨s, hs⟩ := hb
  have hm (y : Q 9) : y ∈ C.image g ↔ g.symm y ∈ C := by
    constructor
    · rintro hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      simpa using hx
    · intro hy; exact Finset.mem_image.mpr ⟨g.symm y,hy,g.apply_symm_apply y⟩
  refine ⟨fun y => theta (g.symm y) * s (g.symm y), ?_, ?_⟩
  · intro y hy
    rcases ht (g.symm y) with h | h <;>
      rcases hs.1 _ ((hm y).mp hy) with h' | h' <;> simp [h,h']
  · intro x hx y hy hxy
    obtain ⟨j,hj⟩ := adjacent_exists_flip hxy
    let i := p.symm j
    have hy' : y = g (flip (g.symm x) i) := by
      rw [reindex_flip, g.apply_symm_apply]
      simpa [i] using hj
    have he' := he (g.symm x) i
    rw [g.apply_symm_apply] at he'
    have hys : flip (g.symm x) i ∈ C := by
      simpa [hy'] using (hm y).mp hy
    rw [hy']
    simp only [g.symm_apply_apply]
    rw [he', hs.2 _ ((hm x).mp hx) _ hys (flip_adj _ _)]
    ring

private lemma reindex_slice (C : Finset (Q 9)) (j : Fin 9) (b : Bool) :
    coordinateSlice (C.image (reindex (Equiv.swap j 0))) b =
      (C.filter (fun x => x j = b)).image (reindex (Equiv.swap j 0)) := by
  ext y
  simp only [coordinateSlice, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,h⟩
    exact ⟨x,⟨hx,by simpa [reindex] using h⟩,rfl⟩
  · rintro ⟨x,⟨hx,h⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,by simpa [reindex] using h⟩

private lemma half_odd {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hc : C.card = 54) (j : Fin 9) (b : Bool) :
    (C.filter (fun x => x j = b)).card % 2 = 1 := by
  let p := Equiv.swap j (0 : Fin 9)
  let T := C.image (reindex p)
  have hr' := reindex_regular hr p
  have hb' := reindex_balanced hb p
  let S := coordinateSlice T b
  let G := (hypercube 9).induce (S : Set (Q 9))
  have hd : ∀ v, G.degree v = 2 ∨ G.degree v = 3 := fun v =>
    coordinate_slice_degree_cases v.property hr'
  have hq := low_slice_card_eq_q (b := b) hr'
  have h6 : 6 * directionEdges T 0 = T.card := by
    simpa using direction_edge_count (d := 3) T hr' hb' 0
  have ht : T.card = 54 := by simpa [T,Finset.card_image_of_injective _ (reindex p).injective] using hc
  have hp := parts_card G hd Finset.univ
  have hs : 2 * (GirthSliceCounting.degreeTwo G Finset.univ).card +
      3 * (GirthSliceCounting.degreeThree G Finset.univ).card = 2 * G.edgeFinset.card := by
    rw [← sum_degrees_parts G hd Finset.univ]
    exact G.sum_degrees_eq_twice_card_edges
  have hN : Fintype.card (S : Set (Q 9)) = (C.filter (fun x => x j = b)).card := by
    rw [show Fintype.card (S : Set (Q 9)) = S.card by simp]
    dsimp [S,T,p]
    rw [reindex_slice,Finset.card_image_of_injective _ (reindex _).injective]
  change (GirthSliceCounting.degreeTwo G Finset.univ).card = directionEdges T 0 at hq
  rw [hq,Finset.card_univ,hN] at hp
  rw [hq] at hs
  simp only [ht] at h6
  omega

private lemma distance_parity (x y : Q 9) :
    hammingDist x y % 2 = 0 ↔ cubeParity x = cubeParity y := by
  letI : CharP Bool 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by decide)
  have he : ((hammingDist x y : ℕ) : Bool) = cubeParity x + cubeParity y := by
    rw [hammingDist, Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one]
    rw [Finset.sum_filter]
    unfold cubeParity
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> cases y i <;> decide
  constructor
  · intro h
    have hz := (CharP.cast_eq_zero_iff Bool 2 (hammingDist x y)).mpr (Nat.dvd_of_mod_eq_zero h)
    rw [he] at hz
    cases hx : cubeParity x <;> cases hy : cubeParity y <;> simp_all [Bool.add_eq_xor]
  · intro h
    exact Nat.mod_eq_zero_of_dvd (even_diff_of_parity_eq x y h).two_dvd

private lemma parity_cards {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hc : C.card = 54) (b : Bool) : (paritySide C b).card = 27 := by
  have hp := parity_bipartite C
  have hs := SimpleGraph.isBipartiteWith_sum_degrees_eq hp
  simp only [hr.degree_eq,Finset.sum_const,smul_eq_mul] at hs
  have hu := congrArg Finset.card (parity_union C)
  rw [Finset.card_union_of_disjoint (by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact Bool.false_ne_true ((Finset.mem_filter.mp hz).2.symm.trans
      (Finset.mem_filter.mp hz').2)),Finset.card_univ] at hu
  have ht : Fintype.card (C : Set (Q 9)) = 54 := by simpa using hc
  cases b <;> omega

private lemma second_distance {C : Finset (Q 9)} {x z : (C : Set (Q 9))}
    (hz : z ∈ second ((hypercube 9).induce (C : Set (Q 9))) x) :
    hammingDist x.val z.val = 2 := by
  obtain ⟨a,hxa,haz,hzx⟩ := mem_second.mp hz
  have h1 : hammingDist x.val a.val = 1 := hxa
  have h2 : hammingDist a.val z.val = 1 := haz
  have h3 := hammingDist_triangle x.val a.val z.val
  have he := distance_parity x.val z.val
  have hp := cubeParity_ne_of_adj hxa
  have hq := cubeParity_ne_of_adj haz
  have hsame : cubeParity x.val = cubeParity z.val := by
    cases hx : cubeParity x.val <;> cases ha : cubeParity a.val <;>
      cases hz : cubeParity z.val <;> simp_all
  have hmod := he.mpr hsame
  have hn : hammingDist x.val z.val ≠ 0 := fun h =>
    hzx (Subtype.ext ((hammingDist_eq_zero.mp h).symm))
  omega

private lemma third_distance {C : Finset (Q 9)} {x z : (C : Set (Q 9))}
    (hz : z ∈ third ((hypercube 9).induce (C : Set (Q 9))) x) :
    hammingDist x.val z.val = 3 := by
  obtain ⟨a,b,hxa,hab,hbz,_,_,hb,hn⟩ := third_witness hz
  have h2 := second_distance hb
  have h1 : hammingDist b.val z.val = 1 := hbz
  have hu := hammingDist_triangle x.val b.val z.val
  have hp := (distance_parity x.val b.val).mp (by omega)
  have hq := cubeParity_ne_of_adj hbz
  have hne : cubeParity x.val ≠ cubeParity z.val := by simpa [← hp] using hq
  have hm : hammingDist x.val z.val % 2 ≠ 0 := by
    simpa [distance_parity] using hne
  have hn1 : hammingDist x.val z.val ≠ 1 := fun h => hn (by
    exact ((hypercube 9).induce (C : Set (Q 9))).mem_neighborFinset _ _ |>.mpr h)
  omega

private lemma root_distance_sum {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hc : C.card = 54)
    (hdiam : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 6) (x : (C : Set (Q 9))) :
    (∑ y : (C : Set (Q 9)), hammingDist x.val y.val) ≤ 215 := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let N (k : ℕ) := Finset.univ.filter (fun y : (C : Set (Q 9)) => hammingDist x.val y.val = k)
  let F := (third G x).biUnion (fun z => G.neighborFinset z \ (HammingSeven.ball G x : Finset _))
  have hg := BalancedCubeGirth.eight_le_egirth C hb
  obtain ⟨h22,h12,hout⟩ := root_data (parity_bipartite C) hg hr.degree_eq x
  have h6 := second_card hg (hr.degree_eq x) (fun a _ => hr.degree_eq a)
  have hF : 8 ≤ F.card := by
    have hl (z : (C : Set (Q 9))) (hz : z ∈ third G x) :
        2 ≤ (F.bipartiteAbove G.Adj z).card := by
      rw [← hout z hz]
      apply Finset.card_le_card
      intro w hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨z,hz,hw⟩,
        (G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp hw).1⟩
    have hu (w : (C : Set (Q 9))) (_ : w ∈ F) :
        ((third G x).bipartiteBelow G.Adj w).card ≤ 3 := by
      calc
        _ ≤ (G.neighborFinset w).card := Finset.card_le_card (by
          intro z hz
          exact (G.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hz).2.symm)
        _ = 3 := by rw [G.card_neighborFinset_eq_degree,hr.degree_eq]
    have h := Finset.card_mul_le_card_mul G.Adj hl hu
    rw [h12] at h
    omega
  have hFsub : F ⊆ N 2 ∪ N 4 := by
    intro w hw
    obtain ⟨z,hz,hw⟩ := Finset.mem_biUnion.mp hw
    have hm := Finset.mem_sdiff.mp hw
    have hzw : G.Adj z w := (G.mem_neighborFinset _ _).mp hm.1
    have h3 := third_distance hz
    have h1 : hammingDist z.val w.val = 1 := hzw
    have hu := hammingDist_triangle x.val z.val w.val
    have hp := cubeParity_ne_of_adj hzw
    have hxp : cubeParity x.val ≠ cubeParity z.val := by
      intro he; have := (distance_parity x.val z.val).mpr he; omega
    have hsame : cubeParity x.val = cubeParity w.val := by
      cases hx : cubeParity x.val <;> cases hz : cubeParity z.val <;>
        cases hw : cubeParity w.val <;> simp_all
    have hmod := (distance_parity x.val w.val).mpr hsame
    have h0 : hammingDist x.val w.val ≠ 0 := by
      intro he
      have he' : w = x := Subtype.ext ((hammingDist_eq_zero.mp he).symm)
      exact hm.2 (by rw [he']; exact Finset.mem_union_left _ (Finset.mem_insert_self _ _))
    have : hammingDist x.val w.val = 2 ∨ hammingDist x.val w.val = 4 := by omega
    simpa [N] using this
  have hdis : Disjoint (second G x) F := by
    apply Finset.disjoint_left.mpr
    intro z hz hf
    obtain ⟨w,hw,hzw⟩ := Finset.mem_biUnion.mp hf
    exact (Finset.mem_sdiff.mp hzw).2
      (Finset.mem_union_left _ (Finset.mem_insert_of_mem hz))
  have h24 : 14 ≤ (N 2).card + (N 4).card := by
    have hsub : second G x ∪ F ⊆ N 2 ∪ N 4 := by
      apply Finset.union_subset
      · intro z hz
        exact Finset.mem_union_left _ (by simpa [N] using second_distance hz)
      · exact hFsub
    have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [Finset.card_union_of_disjoint hdis,h6] at h
    omega
  have h2 : 6 ≤ (N 2).card := by
    rw [← h6]
    exact Finset.card_le_card (by intro z hz; simpa [N] using second_distance hz)
  have h3 : 12 ≤ (N 3).card := by
    rw [← h12]
    exact Finset.card_le_card (by intro z hz; simpa [N] using third_distance hz)
  have h0 : (N 0).card = 1 := by
    have : N 0 = {x} := by ext y; simp only [N,Finset.mem_filter,Finset.mem_univ,true_and,
      hammingDist_eq_zero,Finset.mem_singleton,Subtype.ext_iff]; exact eq_comm
    simp [this]
  have h1 : (N 1).card = 3 := by
    have : N 1 = G.neighborFinset x := by
      ext y
      simp only [N,Finset.mem_filter,Finset.mem_univ,true_and,G.mem_neighborFinset]
      rfl
    rw [this,G.card_neighborFinset_eq_degree,hr.degree_eq]
  have hdist (y : (C : Set (Q 9))) : hammingDist x.val y.val ≤ 6 :=
    hdiam x.val x.property y.val y.property
  have hsum (f : ℕ → ℕ) : (∑ k ∈ Finset.range 7, (N k).card * f k) =
      ∑ y : (C : Set (Q 9)), f (hammingDist x.val y.val) := by
    simpa only [N,Finset.sum_const,smul_eq_mul] using
      Finset.sum_fiberwise_of_maps_to' (s := Finset.univ) (t := Finset.range 7)
        (g := fun y : (C : Set (Q 9)) => hammingDist x.val y.val)
        (fun y _ => Finset.mem_range.mpr (by have := hdist y; omega)) f
  have heven : ∑ y : (C : Set (Q 9)), (if hammingDist x.val y.val % 2 = 0 then 1 else 0) = 27 := by
    rw [← Finset.card_filter]
    have : (Finset.univ.filter (fun y : (C : Set (Q 9)) => hammingDist x.val y.val % 2 = 0)) =
        paritySide C (cubeParity x.val) := by
      ext y
      simp only [paritySide,Finset.mem_filter,Finset.mem_univ,true_and,distance_parity]
      exact eq_comm
    rw [this]; exact parity_cards hr hc _
  have hall := hsum (fun _ => 1)
  have he := hsum (fun k => if k % 2 = 0 then 1 else 0)
  have hd := hsum id
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.reduceMod,ite_true,
    Nat.mul_one,Nat.mul_zero,Nat.zero_add,Nat.add_zero,id_eq] at hall he hd
  simp only [Finset.sum_const,smul_eq_mul,Nat.mul_one,Finset.card_univ] at hall
  have hcard : Fintype.card (C : Set (Q 9)) = 54 := by simpa using hc
  rw [hcard] at hall
  rw [heven] at he
  omega

private lemma distance_double_count (C : Finset (Q 9)) :
    (∑ x ∈ C, ∑ y ∈ C, hammingDist x y) =
      2 * ∑ i : Fin 9, (C.filter (fun x => x i = false)).card *
        (C.filter (fun x => x i = true)).card := by
  have hd (x y : Q 9) : hammingDist x y = ∑ i : Fin 9, if x i ≠ y i then 1 else 0 := by
    exact Finset.card_filter _ _
  simp_rw [hd]
  calc
    _ = ∑ x ∈ C, ∑ i : Fin 9, ∑ y ∈ C, if x i ≠ y i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ i : Fin 9, ∑ x ∈ C, ∑ y ∈ C, if x i ≠ y i then 1 else 0 := Finset.sum_comm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hn : C.filter (fun x => ¬x i = false) = C.filter (fun x => x i = true) := by
        ext x; cases x i <;> simp
      have hm (x : Q 9) : (∑ y ∈ C, if x i ≠ y i then 1 else 0) =
          if x i = false then (C.filter (fun y => y i = true)).card
          else (C.filter (fun y => y i = false)).card := by
        rw [← Finset.card_filter]
        cases hx : x i
        · simp only [ite_true]
          congr 1; ext y; cases y i <;> simp
        · rw [ite_eq_right Bool.false_ne_true.symm]
          congr 1; ext y; cases y i <;> simp
      simp_rw [hm]
      rw [Finset.sum_ite]
      simp only [Finset.sum_const,smul_eq_mul,hn]
      ring

private lemma diameter_six_thin {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hc : C.card = 54)
    (hdiam : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 6) :
    ∃ j : Fin 9, ∃ b : Bool, (C.filter (fun x => x j = b)).card ≤ 17 := by
  by_contra hn
  have hlarge (j : Fin 9) (b : Bool) : 18 ≤ (C.filter (fun x => x j = b)).card := by
    by_contra h; exact hn ⟨j,b,by omega⟩
  have hprod (j : Fin 9) : 648 ≤ (C.filter (fun x => x j = false)).card *
      (C.filter (fun x => x j = true)).card := by
    have h := Finset.card_filter_add_card_filter_not (s := C) (fun x => x j = false)
    have hn : C.filter (fun x => ¬x j = false) = C.filter (fun x => x j = true) := by
      ext x; cases x j <;> simp
    rw [hn,hc] at h
    have ha := hlarge j false
    have hb := hlarge j true
    obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le ha
    obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le hb
    nlinarith [Nat.zero_le (u*v)]
  have hlo := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hprod j)
  have hhi : (∑ x ∈ C, ∑ y ∈ C, hammingDist x y) ≤ 11610 := by
    calc
      _ ≤ ∑ _x ∈ C, 215 := by
        apply Finset.sum_le_sum
        intro x hx
        simpa only [Finset.sum_finset_coe] using root_distance_sum hr hb hc hdiam ⟨x,hx⟩
      _ = _ := by simp [hc]
  rw [distance_double_count] at hhi
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hlo
  omega


private lemma ball_exit {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {x z w : V} (hz : z ∈ (HammingSeven.ball G x : Finset _))
    (hzw : G.Adj z w) (hw : w ∉ (HammingSeven.ball G x : Finset _)) : z ∈ third G x := by
  rcases Finset.mem_union.mp hz with hz | hz
  · rcases Finset.mem_insert.mp hz with rfl | hz
    · exact (hw (Finset.mem_union_right _ (Finset.mem_union_left _
        ((G.mem_neighborFinset _ _).mpr hzw)))).elim
    · by_cases hfirst : w ∈ G.neighborFinset x
      · exact (hw (Finset.mem_union_right _ (Finset.mem_union_left _ hfirst))).elim
      · exact (hw (third_subset_ball x (Finset.mem_biUnion.mpr
          ⟨z,hz,Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr hzw,hfirst⟩⟩))).elim
  · rcases Finset.mem_union.mp hz with hz | hz
    · have hs : w = x ∨ w ∈ second G x := by
        by_cases h : w = x
        · exact Or.inl h
        · exact Or.inr (mem_second.mpr ⟨z,(G.mem_neighborFinset _ _).mp hz,hzw,h⟩)
      exact (hw (Finset.mem_union_left _ (Finset.mem_insert.mpr hs))).elim
    · exact hz

private def incidences {V : Type*} [Fintype V] (G : SimpleGraph V) (A B : Finset V) : ℕ :=
  ∑ z ∈ A, (B.bipartiteAbove G.Adj z).card

private lemma incidences_symm {V : Type*} [Fintype V] (G : SimpleGraph V) (A B : Finset V) :
    incidences G A B = incidences G B A := by
  rw [incidences,Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  ext z
  rw [Finset.mem_bipartiteBelow,Finset.mem_bipartiteAbove]
  exact and_congr_right fun _ => G.adj_comm _ _

private lemma incidences_add {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B D : Finset V) (h : Disjoint B D) :
    incidences G A (B ∪ D) = incidences G A B + incidences G A D := by
  unfold incidences
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  change ((B ∪ D).filter _).card = _
  rw [Finset.filter_union,Finset.card_union_of_disjoint (h.mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  rfl

private lemma incidences_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hd : ∀ v, G.degree v = 3) (A B : Finset V) :
    incidences G A B ≤ 3 * A.card := by
  calc
    _ ≤ ∑ _z ∈ A, 3 := by
      apply Finset.sum_le_sum
      intro z _
      calc
        _ ≤ (G.neighborFinset z).card := Finset.card_le_card (by
          intro w hw; exact (G.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hw).2)
        _ = 3 := by rw [G.card_neighborFinset_eq_degree,hd]
    _ = _ := by simp [Nat.mul_comm]

private lemma ball_out {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V} (hp : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) (hd : ∀ v, G.degree v = 3) (x : V) :
    incidences G ((HammingSeven.ball G x : Finset _)) (Finset.univ \ (HammingSeven.ball G x : Finset _)) = 24 := by
  obtain ⟨_,h12,hout⟩ := root_data hp hg hd x
  have he (z : V) : (Finset.univ \ (HammingSeven.ball G x : Finset _)).bipartiteAbove G.Adj z =
      G.neighborFinset z \ (HammingSeven.ball G x : Finset _) := by
    ext w; simp [Finset.bipartiteAbove,and_comm]
  unfold incidences
  simp_rw [he]
  have hs : (∑ z ∈ third G x, (G.neighborFinset z \ (HammingSeven.ball G x : Finset _)).card) =
      ∑ z ∈ (HammingSeven.ball G x : Finset _), (G.neighborFinset z \ (HammingSeven.ball G x : Finset _)).card := by
    apply Finset.sum_subset (third_subset_ball x)
    intro z hz hn
    have : G.neighborFinset z \ (HammingSeven.ball G x : Finset _) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact hn (ball_exit hz ((G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp hw).1)
        (Finset.mem_sdiff.mp hw).2)
    simp [this]
  rw [← hs]
  have hh := Finset.sum_congr rfl hout
  rw [hh]
  simp [h12]

private lemma two_ball_cross {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hc : C.card = 54) (x y : (C : Set (Q 9)))
    (hxy : hammingDist x.val y.val = 7) :
    Disjoint ((HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) x : Finset _))
      ((HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) y : Finset _)) ∧
    9 ≤ incidences ((hypercube 9).induce (C : Set (Q 9)))
      ((HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) x : Finset _))
      ((HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) y : Finset _)) := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let A := (HammingSeven.ball G x : Finset _)
  let B := (HammingSeven.ball G y : Finset _)
  let O := Finset.univ \ (A ∪ B)
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨p,hp⟩ := ball_walk hz
    obtain ⟨q,hq⟩ := ball_walk hz'
    have h := hamming_le_walk (p.append q.reverse)
    simp only [Walk.length_append,Walk.length_reverse] at h
    omega
  refine ⟨hdis,?_⟩
  have hg := BalancedCubeGirth.eight_le_egirth C hb
  have hx22 := (root_data (parity_bipartite C) hg hr.degree_eq x).1
  have hy22 := (root_data (parity_bipartite C) hg hr.degree_eq y).1
  have hO : O.card = 10 := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (A ∪ B))
    rw [Finset.card_union_of_disjoint hdis,hx22,hy22,Finset.card_univ,
      show Fintype.card (C : Set (Q 9)) = 54 by simpa using hc] at h
    change O.card + (22 + 22) = 54 at h
    omega
  have hs (A B : Finset (C : Set (Q 9))) (hd : Disjoint A B) :
      Finset.univ \ A = B ∪ (Finset.univ \ (A ∪ B)) := by
    ext z
    have hh := Finset.disjoint_left.mp hd
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_union,not_or]
    tauto
  have hA := ball_out (parity_bipartite C) hg hr.degree_eq x
  have hB := ball_out (parity_bipartite C) hg hr.degree_eq y
  change incidences G A (Finset.univ \ A) = 24 at hA
  change incidences G B (Finset.univ \ B) = 24 at hB
  rw [hs A B hdis,incidences_add G A B O (by
    apply Finset.disjoint_left.mpr; intro z hz hz'; exact (Finset.mem_sdiff.mp hz').2 (Finset.mem_union_right _ hz))] at hA
  rw [hs B A hdis.symm] at hB
  rw [Finset.union_comm B A] at hB
  rw [incidences_add G B A O (by
    apply Finset.disjoint_left.mpr; intro z hz hz'; exact (Finset.mem_sdiff.mp hz').2 (Finset.mem_union_left _ hz)),
    incidences_symm G B A] at hB
  have hcap : incidences G A O + incidences G B O ≤ 30 := by
    rw [incidences_symm G A O,incidences_symm G B O,← incidences_add G O A B hdis]
    have h := incidences_bound G hr.degree_eq O (A ∪ B)
    omega
  change 9 ≤ incidences G A B
  omega


private lemma agree_of_near_geodesic {x y z : Q 9} {m : ℕ} (hxy : hammingDist x y = m)
    (hs : hammingDist x z + hammingDist y z ≤ m + 1) (i : Fin 9) (hi : x i = y i) :
    z i = x i := by
  by_contra hn
  have hm : i ∈ diff x z ∩ diff y z := by
    apply Finset.mem_inter.mpr
    constructor <;> simp only [diff,Finset.mem_filter,Finset.mem_univ,true_and]
    · exact Ne.symm hn
    · rw [← hi]; exact Ne.symm hn
  have hp := Finset.card_pos.mpr ⟨i,hm⟩
  have ht := diff_triangle_card x y z
  change hammingDist x y + 2 * (diff x z ∩ diff y z).card =
    hammingDist x z + hammingDist y z at ht
  omega

set_option maxHeartbeats 1000000 in
-- The actual layer filters and their incidence capacities elaborate together.
private lemma good_ball_count {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hc : C.card = 54) (x y : (C : Set (Q 9)))
    (hxy : hammingDist x.val y.val = 7) (T : Finset (Fin 9))
    (hT : ∀ i ∈ T, x.val i = y.val i) :
    12 ≤ ((HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) x : Finset _).filter
      (fun z => ∀ i ∈ T, z.val i = x.val i)).card := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let A : Finset _ := HammingSeven.ball G x
  let B : Finset _ := HammingSeven.ball G y
  let good := fun z : (C : Set (Q 9)) => ∀ i ∈ T, z.val i = x.val i
  let L := (third G x).filter good
  let S := (second G x).filter good
  have hg := BalancedCubeGirth.eight_le_egirth C hb
  have hd := HammingSeven.hamming_distance_le_seven hr hb hc
  obtain ⟨hdis,hcross⟩ := two_ball_cross hr hb hc x y hxy
  have hcrosspoint {z w : (C : Set (Q 9))} (hz : z ∈ A) (hw : w ∈ B) (hzw : G.Adj z w) :
      good z := by
    obtain ⟨p,hp⟩ := ball_walk hz
    obtain ⟨q,hq⟩ := ball_walk hw
    have ha := hamming_le_walk p
    have hb := hamming_le_walk q
    have he : hammingDist w.val z.val = 1 := hzw.symm
    have ht := hammingDist_triangle y.val w.val z.val
    exact fun i hi => agree_of_near_geodesic hxy (by omega) i (hT i hi)
  have hLsub : L ⊆ A := fun z hz => third_subset_ball x (Finset.mem_filter.mp hz).1
  have heq : incidences G A B = incidences G L B := by
    symm
    apply Finset.sum_subset hLsub
    intro z hz hn
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hm := Finset.mem_filter.mp hw
    have hwa : w ∉ A := fun h => Finset.disjoint_left.mp hdis h hm.1
    exact hn (Finset.mem_filter.mpr ⟨ball_exit hz hm.2 hwa,hcrosspoint hz hm.1 hm.2⟩)
  have hL : 5 ≤ L.card := by
    have hu : incidences G L B ≤ 2 * L.card := by
      calc
        _ ≤ ∑ _z ∈ L, 2 := by
          apply Finset.sum_le_sum
          intro z hz
          have hzt := (Finset.mem_filter.mp hz).1
          have hout := (root_data (parity_bipartite C) hg hr.degree_eq x).2.2 z hzt
          rw [← hout]
          apply Finset.card_le_card
          intro w hw
          have hm := Finset.mem_filter.mp hw
          exact Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr hm.2,
            fun h => Finset.disjoint_left.mp hdis h hm.1⟩
        _ = _ := by simp [Nat.mul_comm]
    change 9 ≤ incidences G A B at hcross
    rw [heq] at hcross
    omega
  have hS : 3 ≤ S.card := by
    have hl (z : (C : Set (Q 9))) (hz : z ∈ L) : 1 ≤ (S.bipartiteAbove G.Adj z).card := by
      obtain ⟨a,b,hxa,hab,hbz,_,_,hb,_⟩ := third_witness (Finset.mem_filter.mp hz).1
      have hbg : good b := by
        have h2 := second_distance hb
        have h3 := third_distance (Finset.mem_filter.mp hz).1
        have he : hammingDist z.val b.val = 1 := hbz.symm
        intro i hi
        exact agree_of_near_geodesic h3 (by omega) i ((Finset.mem_filter.mp hz).2 i hi).symm
      exact Finset.one_le_card.mpr ⟨b,Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hb,hbg⟩,hbz.symm⟩⟩
    have hu (b : (C : Set (Q 9))) (hb : b ∈ S) : (L.bipartiteBelow G.Adj b).card ≤ 2 := by
      have hbs := (Finset.mem_filter.mp hb).1
      have hc := Finset.card_sdiff_add_card_inter (G.neighborFinset b) (G.neighborFinset x)
      have hi : (G.neighborFinset b ∩ G.neighborFinset x).card = 1 :=
        second_neighbor_inter hg hbs
      rw [G.card_neighborFinset_eq_degree,hr.degree_eq,hi] at hc
      have hs : L.bipartiteBelow G.Adj b ⊆ G.neighborFinset b \ G.neighborFinset x := by
        intro z hz
        have hm := Finset.mem_filter.mp hz
        exact Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr hm.2.symm,
          fun hz' => Finset.disjoint_left.mp (first_third_disjoint x) hz'
            (Finset.mem_filter.mp hm.1).1⟩
      have hh := Finset.card_le_card hs
      omega
    have hh := Finset.card_mul_le_card_mul G.Adj hl hu
    omega
  have hfirst : ∀ z ∈ G.neighborFinset x, good z := by
    intro z hz i hi
    have ha : hammingDist x.val z.val = 1 := (G.mem_neighborFinset _ _).mp hz
    have hb : hammingDist y.val z.val ≤ 7 := hd y.val y.property z.val z.property
    exact agree_of_near_geodesic hxy (by omega) i (hT i hi)
  have he : A.filter good = insert x S ∪ (G.neighborFinset x ∪ L) := by
    ext z
    simp only [A,HammingSeven.ball,Finset.mem_filter,Finset.mem_union,Finset.mem_insert,S,L]
    have hx : good x := by intro i _; rfl
    have hn := hfirst z
    tauto
  have hsep : Disjoint (insert x S) (G.neighborFinset x ∪ L) := by
    apply Finset.disjoint_left.mpr
    intro z hz hw
    have hzdist : hammingDist x.val z.val = 0 ∨ hammingDist x.val z.val = 2 := by
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Or.inl (hammingDist_self _)
      · exact Or.inr (second_distance (Finset.mem_filter.mp hz).1)
    have hwdist : hammingDist x.val z.val = 1 ∨ hammingDist x.val z.val = 3 := by
      rcases Finset.mem_union.mp hw with hw | hw
      · exact Or.inl ((G.mem_neighborFinset _ _).mp hw)
      · exact Or.inr (third_distance (Finset.mem_filter.mp hw).1)
    omega
  change 12 ≤ (A.filter good).card
  rw [he,Finset.card_union_of_disjoint hsep,
    Finset.card_insert_of_notMem (fun hx => root_not_second x (Finset.mem_filter.mp hx).1),
    Finset.card_union_of_disjoint ((first_third_disjoint x).mono (by rfl)
      (Finset.filter_subset _ _)),G.card_neighborFinset_eq_degree,hr.degree_eq]
  change 12 ≤ S.card + 1 + (3 + L.card)
  omega


set_option maxHeartbeats 1000000 in
-- The two actual balls and four face filters share the full support subtype.
private lemma distance_seven_thin {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hc : C.card = 54) (x y : (C : Set (Q 9)))
    (hxy : hammingDist x.val y.val = 7) :
    ∃ j : Fin 9, ∃ b : Bool, (C.filter (fun x => x j = b)).card ≤ 19 := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let A : Finset _ := HammingSeven.ball G x
  let B : Finset _ := HammingSeven.ball G y
  let T := Finset.univ.filter (fun i : Fin 9 => x.val i = y.val i)
  have hTcard : T.card = 2 := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin 9 => x.val i = y.val i)
    change T.card + hammingDist x.val y.val = 9 at h
    omega
  obtain ⟨i,j,hij,hT⟩ := Finset.card_eq_two.mp hTcard
  have hTgood : ∀ k ∈ T, x.val k = y.val k := fun k hk => (Finset.mem_filter.mp hk).2
  have hi : x.val i = y.val i := hTgood i (by simp [hT])
  have hj : x.val j = y.val j := hTgood j (by simp [hT])
  let F00 := Finset.univ.filter (fun z : (C : Set (Q 9)) =>
    z.val i = x.val i ∧ z.val j = x.val j)
  let F11 := Finset.univ.filter (fun z : (C : Set (Q 9)) =>
    z.val i ≠ x.val i ∧ z.val j ≠ x.val j)
  obtain ⟨hdis,_⟩ := two_ball_cross hr hb hc x y hxy
  have h00 : 24 ≤ F00.card := by
    have hx := good_ball_count hr hb hc x y hxy T hTgood
    have hy := good_ball_count hr hb hc y x (by simpa [hammingDist_comm] using hxy)
      T (fun k hk => (hTgood k hk).symm)
    have hxs : A.filter (fun z => ∀ k ∈ T, z.val k = x.val k) ⊆ F00 := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hz).2 i (by simp [hT]),
        (Finset.mem_filter.mp hz).2 j (by simp [hT])⟩
    have hys : B.filter (fun z => ∀ k ∈ T, z.val k = y.val k) ⊆ F00 := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ((Finset.mem_filter.mp hz).2 i (by simp [hT])).trans hi.symm,
        ((Finset.mem_filter.mp hz).2 j (by simp [hT])).trans hj.symm⟩
    have hh := Finset.card_le_card (Finset.union_subset hxs hys)
    rw [Finset.card_union_of_disjoint (hdis.mono (Finset.filter_subset _ _)
      (Finset.filter_subset _ _))] at hh
    have hx' : 12 ≤ (A.filter (fun z => ∀ k ∈ T, z.val k = x.val k)).card := by
      convert hx using 1 <;> congr 1 <;> ext z <;> simp only [A,G,Finset.mem_filter]
    have hy' : 12 ≤ (B.filter (fun z => ∀ k ∈ T, z.val k = y.val k)).card := by
      convert hy using 1 <;> congr 1 <;> ext z <;> simp only [B,G,Finset.mem_filter]
    omega
  have h11 : F11.card ≤ 10 := by
    have hsub : F11 ⊆ Finset.univ \ (A ∪ B) := by
      intro z hz
      have hm := (Finset.mem_filter.mp hz).2
      have hsub : T ⊆ diff x.val z.val ∩ diff y.val z.val := by
        intro k hk
        have hk' : k = i ∨ k = j := by simpa [hT] using hk
        rcases hk' with rfl | rfl
        · simp [diff,← hi,Ne.symm hm.1]
        · simp [diff,← hj,Ne.symm hm.2]
      have hge := Finset.card_le_card hsub
      rw [hTcard] at hge
      have ht := diff_triangle_card x.val y.val z.val
      change hammingDist x.val y.val + 2 * (diff x.val z.val ∩ diff y.val z.val).card =
        hammingDist x.val z.val + hammingDist y.val z.val at ht
      have hd := HammingSeven.hamming_distance_le_seven hr hb hc
      have hx7 : hammingDist x.val z.val ≤ 7 := hd x.val x.property z.val z.property
      have hy7 : hammingDist y.val z.val ≤ 7 := hd y.val y.property z.val z.property
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
      intro hz'
      rcases Finset.mem_union.mp hz' with hz' | hz'
      · obtain ⟨p,hp⟩ := ball_walk hz'
        have ha := hamming_le_walk p
        omega
      · obtain ⟨p,hp⟩ := ball_walk hz'
        have ha := hamming_le_walk p
        omega
    have hh := Finset.card_le_card hsub
    have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (A ∪ B))
    have hg := BalancedCubeGirth.eight_le_egirth C hb
    have hx22 : A.card = 22 := (root_data (parity_bipartite C) hg hr.degree_eq x).1
    have hy22 : B.card = 22 := (root_data (parity_bipartite C) hg hr.degree_eq y).1
    rw [Finset.card_union_of_disjoint hdis,hx22,hy22,Finset.card_univ,
      show Fintype.card (C : Set (Q 9)) = 54 by simpa using hc] at hcard
    omega
  let H (k : Fin 9) := Finset.univ.filter (fun z : (C : Set (Q 9)) => z.val k = !x.val k)
  have heq : (H i).card + (H j).card + F00.card = 54 + F11.card := by
    have hp (z : (C : Set (Q 9))) :
        (if z.val i = !x.val i then 1 else 0) + (if z.val j = !x.val j then 1 else 0) +
        (if z.val i = x.val i ∧ z.val j = x.val j then 1 else 0) =
        1 + (if z.val i ≠ x.val i ∧ z.val j ≠ x.val j then 1 else 0) := by
      cases z.val i <;> cases x.val i <;> cases z.val j <;> cases x.val j <;> decide
    have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun z _ => hp z)
    simpa only [Finset.sum_add_distrib,← Finset.card_filter,Finset.sum_const,
      Finset.card_univ,show Fintype.card (C : Set (Q 9)) = 54 by simpa using hc,
      smul_eq_mul,Nat.mul_one,H,F00,F11] using hh
  have hH (k : Fin 9) : (H k).card = (C.filter (fun z => z k = !x.val k)).card := by
    dsimp only [H]
    simp only [Finset.card_filter]
    exact Finset.sum_finset_coe (fun z : Q 9 => if z k = !x.val k then 1 else 0) C
  have ho (k : Fin 9) : (H k).card % 2 = 1 := by
    rw [hH]
    exact half_odd hr hb hc k _
  have hthin : (H i).card ≤ 19 ∨ (H j).card ≤ 19 := by
    have hoi := ho i
    have hoj := ho j
    omega
  rcases hthin with h | h
  · refine ⟨i,!x.val i,?_⟩
    rwa [hH] at h
  · refine ⟨j,!x.val j,?_⟩
    rwa [hH] at h

/-- Actual cubicity, original Huang balance and cardinality 54 force a total
cube symmetry and coordinate permutation reconstructing the Gray support. -/
theorem gray_reconstruction {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hc : C.card = 54) :
    ∃ (g : Q 9 ≃ Q 9) (pi : Fin 9 ≃ Fin 9),
      (∀ x i, g (flip x i) = flip (g x) (pi i)) ∧
      C = (GrayGridComponent.support 3).image g := by
  have hC : C.Nonempty := Finset.card_pos.mp (by omega)
  have hthin : ∃ j : Fin 9, ∃ b : Bool, (C.filter (fun x => x j = b)).card ≤ 19 := by
    by_cases h7 : ∃ x ∈ C, ∃ y ∈ C, hammingDist x y = 7
    · obtain ⟨x,hx,y,hy,hxy⟩ := h7
      exact distance_seven_thin hr hb hc ⟨x,hx⟩ ⟨y,hy⟩ hxy
    · have hd := HammingSeven.hamming_distance_le_seven hr hb hc
      have h6 : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 6 := by
        intro x hx y hy
        have hle : hammingDist x y ≤ 7 := hd x hx y hy
        have hne : hammingDist x y ≠ 7 := fun h => h7 ⟨x,hx,y,hy,h⟩
        omega
      obtain ⟨j,b,hj⟩ := diameter_six_thin hr hb hc h6
      exact ⟨j,b,by omega⟩
  obtain ⟨j,b,hs⟩ := hthin
  let p := Equiv.swap j (0 : Fin 9)
  let R := reindex p
  let C' := C.image R
  have hC' : C'.Nonempty := hC.image _
  have hr' := reindex_regular hr p
  have hb' := reindex_balanced hb p
  have hs' : (coordinateSlice C' b).card ≤ 19 := by
    rw [reindex_slice,Finset.card_image_of_injective _ (reindex _).injective]
    exact hs
  obtain ⟨g',pi',hg',himage⟩ :=
    NineteenPointSlice.nineteen_point_slice_gray_reconstruction hC' hr' hb' b hs'
  refine ⟨g'.trans R.symm,pi'.trans p.symm,?_,?_⟩
  · intro x i
    change R.symm (g' (flip x i)) = flip (R.symm (g' x)) (p.symm (pi' i))
    apply R.injective
    rw [R.apply_symm_apply,hg',reindex_flip,R.apply_symm_apply,p.apply_symm_apply]
  · have h := congrArg (fun S : Finset (Q 9) => S.image R.symm) himage
    simpa [C',Finset.image_image,Function.comp_def] using h

#print axioms gray_reconstruction

end D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
