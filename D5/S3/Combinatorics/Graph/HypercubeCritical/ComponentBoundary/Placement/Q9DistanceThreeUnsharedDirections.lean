/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedDirections
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedDirections
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Unshared distance-three contacts partition the neighbor directions and preserve a coordinate translate. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentDirectionTypes

/-! The occupied directions at a closest endpoint with no common flips. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceThreeUnsharedDirections

open Finset
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_flip IsBalanced)
open BalancedCubeGirth (no_selected_square flip_comm)
open BalancedCubeComponentBoundary (directions mem_directions regular_directions exterior_even)
open Q9TriplePartitions (IsTriplePartition neighborPartition)
open private directions_subset_agreement flip_eq_flip_iff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.CubicContactDistance
open private differingAxes foldl_flip_apply from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private differingAxes_symm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactComplement
open private mem_diff diff_flip_left from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar

private theorem card_sdiff_eq {α : Type*} [DecidableEq α] {S T : Finset α}
    (h : T ⊆ S) : (S \ T).card + T.card = S.card := by
  rw [card_sdiff_of_subset h]
  exact Nat.sub_add_cancel (card_le_card h)

/-- The axes appearing in a distance-three contact with the fixed endpoint. -/
def unsharedContactAxes (C : Finset (Q 9)) (y : Q 9) : Finset (Fin 9) :=
    (C.filter fun x => hammingDist x y = 3).biUnion fun x => differingAxes x y

open Classical in
/-- At a distance-three endpoint with no common flips, at least five axes
occur in the closest displacements. The direction triples at its neighbors
partition all nine axes. -/
theorem axes_and_partition_of_unshared_contacts
    {C D : Finset (Q 9)}
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 3 ≤ hammingDist u v)
    {y : Q 9} (hy : y ∈ D)
    (hne : ∃ x ∈ C, hammingDist x y = 3)
    (hdis : ∀ x ∈ C, hammingDist x y = 3 →
      Disjoint (directions C x) (directions D y)) :
    5 ≤ (unsharedContactAxes C y).card ∧ IsTriplePartition (neighborPartition D y) := by
  let E := directions D y
  let B := (univ : Finset (Fin 9)) \ E
  have hEc : E.card = 3 := regular_directions D hrD hy
  have hBc : B.card = 6 := by
    have h := card_sdiff_eq (subset_univ E)
    simp only [card_univ, Fintype.card_fin, hEc] at h
    change B.card + 3 = 9 at h
    omega
  let U := unsharedContactAxes C y
  have hUmem {i : Fin 9} : i ∈ U ↔ ∃ x ∈ C, hammingDist x y = 3 ∧ i ∈ differingAxes x y := by
    simp only [U, unsharedContactAxes, mem_biUnion, mem_filter]
    constructor
    · rintro ⟨x, ⟨hx, hd⟩, hi⟩
      exact ⟨x, hx, hd, hi⟩
    · rintro ⟨x, hx, hd, hi⟩
      exact ⟨x, ⟨hx, hd⟩, hi⟩
  have hshape {x : Q 9} (hx : x ∈ C) (hd : hammingDist x y = 3) :
      differingAxes x y ⊆ B ∧ directions C x = B \ differingAxes x y := by
    have hm (u : Q 9) (hu : u ∈ C) (v : Q 9) (hv : v ∈ D) :
        hammingDist x y ≤ hammingDist u v := hd.le.trans (hsep u hu v hv)
    have he := directions_subset_agreement hx (C := D) (D := C) (x := y)
      (fun u hu v hv => by simpa only [hammingDist_comm] using hm v hv u hu)
    have hin : differingAxes x y ⊆ B := by
      intro i hi
      exact mem_sdiff.mpr ⟨mem_univ _, fun h => (mem_diff x y i).mp hi
        (mem_filter.mp (he h)).2.symm⟩
    have hcx := directions_subset_agreement hy hm
    have hs : directions C x ⊆ B \ differingAxes x y := by
      intro i hi
      exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,
        fun h => disjoint_left.mp (hdis x hx hd) hi h⟩,
        fun h => (mem_diff x y i).mp h (mem_filter.mp (hcx hi)).2⟩
    have hc := card_sdiff_eq hin
    change (B \ differingAxes x y).card + hammingDist x y = B.card at hc
    refine ⟨hin, eq_of_subset_of_card_le hs ?_⟩
    rw [regular_directions C hrC hx]
    omega
  have hUB : U ⊆ B := by
    intro i hi
    obtain ⟨x, hx, hd, hxi⟩ := hUmem.mp hi
    exact (hshape hx hd).1 hxi
  have hrepair {x : Q 9} (hx : x ∈ C) (hd : hammingDist x y = 3)
      {i : Fin 9} (hi : i ∈ differingAxes x y) :
      ∃ k ∈ U, k ∉ differingAxes x y ∧ flip (flip x i) k ∈ C := by
    let w := flip x i
    have hwDiff : differingAxes w y = (differingAxes x y).erase i := by
      rw [diff_flip_left, ite_eq_left hi]
    have hwDist : hammingDist w y = 2 := by
      change (differingAxes w y).card = 2
      rw [hwDiff, card_erase_of_mem hi]
      change hammingDist x y - 1 = 2
      rw [hd]
    have hwo : w ∉ C := by
      intro hw
      have := hsep w hw y hy
      omega
    have hiw : i ∈ directions C w := (mem_directions C w i).mpr (by simpa only [w, BalancedCriticalSpectrum.flip_flip] using hx)
    obtain ⟨n, hn⟩ := exterior_even C hrC hbC w hwo
    have hc := card_erase_add_one hiw
    obtain ⟨k, hk⟩ := card_pos.mp (show 0 < ((directions C w).erase i).card by omega)
    obtain ⟨hki, hk⟩ := mem_erase.mp hk
    have hkc := (mem_directions C w k).mp hk
    let x' := flip w k
    have hg : hammingDist w x' = 1 := BalancedCriticalSpectrum.flip_adj w k
    have hl := hsep x' hkc y hy
    have ht := hammingDist_triangle x' w y
    rw [hammingDist_comm x' w, hg, hwDist] at ht
    have hd' : hammingDist x' y = 3 := by omega
    have hkm : k ∉ differingAxes w y := by
      intro h
      have hcard := card_erase_add_one h
      have he := diff_flip_left w y k
      rw [ite_eq_left h] at he
      change differingAxes x' y = _ at he
      rw [← he] at hcard
      change hammingDist x' y + 1 = hammingDist w y at hcard
      omega
    have hkold : k ∉ differingAxes x y := by
      intro h
      exact hkm (hwDiff.symm ▸ mem_erase.mpr ⟨hki, h⟩)
    have hknew : k ∈ differingAxes x' y := by
      change k ∈ differingAxes (flip w k) y
      rw [diff_flip_left, ite_eq_right hkm]
      exact mem_insert_self _ _
    exact ⟨k, hUmem.mpr ⟨x', hkc, hd', hknew⟩, hkold, hkc⟩
  have hUcard : 5 ≤ U.card := by
    obtain ⟨x, hx, hd⟩ := hne
    let T := differingAxes x y
    have hTc : T.card = 3 := hd
    have hTU : T ⊆ U := fun _ hi => hUmem.mpr ⟨x, hx, hd, hi⟩
    obtain ⟨i, hi⟩ := card_pos.mp (show 0 < T.card by omega)
    obtain ⟨k, hkU, hkT, _⟩ := hrepair hx hd hi
    have hsub : insert k T ⊆ U := insert_subset_iff.mpr ⟨hkU, hTU⟩
    have hcard : (insert k T).card = 4 := by rw [card_insert_of_notMem hkT, hTc]
    by_contra h
    have he := eq_of_subset_of_card_le hsub (show U.card ≤ (insert k T).card by omega)
    have hwC : flip x k ∈ C := by
      apply (mem_directions C x k).mp
      rw [(hshape hx hd).2]
      exact mem_sdiff.mpr ⟨hUB hkU, hkT⟩
    have hinc : insert k T ⊆ directions C (flip x k) := by
      apply insert_subset_iff.mpr
      refine ⟨(mem_directions C (flip x k) k).mpr (by simpa only [BalancedCriticalSpectrum.flip_flip] using hx), ?_⟩
      intro j hj
      obtain ⟨l, hlU, hlT, hcl⟩ := hrepair hx hd hj
      have hlk := (mem_insert.mp (he.symm ▸ hlU)).resolve_right hlT
      subst l
      exact (mem_directions C (flip x k) j).mpr (by simpa only [flip_comm x j k] using hcl)
    have hi := card_le_card hinc
    rw [hcard, regular_directions C hrC hwC] at hi
    omega
  let P (e : Fin 9) := (directions D (flip y e)).erase e
  let I (p : Fin 9) := E.filter fun e => p ∈ P e
  have hback {e : Fin 9} (he : e ∈ E) : e ∈ directions D (flip y e) :=
    (mem_directions D (flip y e) e).mpr (by simpa only [BalancedCriticalSpectrum.flip_flip] using hy)
  have hPcard {e : Fin 9} (he : e ∈ E) : (P e).card = 2 := by
    simp only [P, card_erase_of_mem (hback he),
      regular_directions D hrD ((mem_directions D y e).mp he)]
  have hPsub {e : Fin 9} (he : e ∈ E) : P e ⊆ B := by
    intro p hp
    obtain ⟨hne, hp⟩ := mem_erase.mp hp
    refine mem_sdiff.mpr ⟨mem_univ _, fun hpE => ?_⟩
    exact no_selected_square hbD hne.symm hy ((mem_directions D y e).mp he)
      ((mem_directions D y p).mp hpE) ((mem_directions D (flip y e) p).mp hp)
  have hsum : ∑ p ∈ B, (I p).card = 6 := by
    calc
      _ = ∑ p ∈ B, ∑ e ∈ E, if p ∈ P e then (1 : ℕ) else 0 := by
        simp only [I, ← sum_filter, sum_const, smul_eq_mul, mul_one]
      _ = ∑ e ∈ E, ∑ p ∈ B, if p ∈ P e then (1 : ℕ) else 0 := Finset.sum_comm
      _ = ∑ e ∈ E, (2 : ℕ) := by
        apply sum_congr rfl
        intro e he
        have heq : B.filter (fun p => p ∈ P e) = P e := by
          ext p
          exact mem_filter.trans ⟨And.right, fun hp => ⟨hPsub he hp, hp⟩⟩
        rw [← sum_filter, heq]
        simp [hPcard he]
      _ = 6 := by simp [hEc]
  have hodd {p : Fin 9} (hp : p ∈ U) : ∃ n : ℕ, (I p).card = 2 * n + 1 := by
    obtain ⟨x, hx, hd, hpT⟩ := hUmem.mp hp
    have hpE := (mem_sdiff.mp (hUB hp)).2
    let w := flip y p
    have hw : w ∉ D := fun h => hpE ((mem_directions D y p).mpr h)
    have ht : differingAxes w x = (differingAxes y x).erase p := by
      rw [diff_flip_left, ite_eq_left (by rwa [differingAxes_symm])]
    have hwy : hammingDist w x = 2 := by
      change (differingAxes w x).card = 2
      rw [ht, differingAxes_symm y x, card_erase_of_mem hpT]
      change hammingDist x y - 1 = 2
      rw [hd]
    have hin (k : Fin 9) (hk : k ∈ directions D w) (hkp : k ≠ p) : k ∈ E := by
      by_contra hkE
      have hkv := (mem_directions D w k).mp hk
      by_cases hkt : k ∈ differingAxes x y
      · have hkw : k ∈ differingAxes w x := by
          rw [ht, differingAxes_symm y x]
          exact mem_erase.mpr ⟨hkp, hkt⟩
        have hflip : differingAxes (flip w k) x = (differingAxes w x).erase k := by
          rw [diff_flip_left, ite_eq_left hkw]
        have hdist : hammingDist (flip w k) x = 1 := by
          change (differingAxes (flip w k) x).card = 1
          rw [hflip, card_erase_of_mem hkw]
          change hammingDist w x - 1 = 1
          rw [hwy]
        have := hsep x hx _ hkv
        rw [hammingDist_comm, hdist] at this
        omega
      · have hxc : flip x k ∈ C := by
          apply (mem_directions C x k).mp
          rw [(hshape hx hd).2]
          exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, hkE⟩, hkt⟩
        have hdist : hammingDist (flip w k) (flip x k) = hammingDist w x := by
          change (univ.filter fun j => flip w k j ≠ flip x k j).card =
            (univ.filter fun j => w j ≠ x j).card
          simp only [ne_eq, flip_eq_flip_iff]
        have := hsep _ hxc _ hkv
        rw [hammingDist_comm, hdist, hwy] at this
        omega
    have heq : directions D w = insert p (I p) := by
      ext k
      by_cases hkp : k = p
      · subst k
        have := (mem_directions D w p).mpr (by simpa only [w, BalancedCriticalSpectrum.flip_flip] using hy)
        simp [this]
      · rw [mem_insert, or_iff_right hkp]
        constructor
        · intro hk
          refine mem_filter.mpr ⟨hin k hk hkp, mem_erase.mpr ⟨fun h => hkp h.symm, ?_⟩⟩
          exact (mem_directions D (flip y k) p).mpr
            (by simpa only [w, flip_comm y k p] using (mem_directions D w k).mp hk)
        · intro hk
          obtain ⟨_, hmem⟩ := mem_filter.mp hk
          apply (mem_directions D w k).mpr
          simpa only [w, flip_comm y p k] using
            (mem_directions D (flip y k) p).mp (mem_of_mem_erase hmem)
    have hnI : p ∉ I p := fun h => hpE (mem_filter.mp h).1
    obtain ⟨n, hn⟩ := exterior_even D hrD hbD w hw
    rw [heq, card_insert_of_notMem hnI] at hn
    refine ⟨n - 1, ?_⟩
    omega
  have hposU {p : Fin 9} (hp : p ∈ U) : 1 ≤ (I p).card := by
    obtain ⟨n, h⟩ := hodd hp
    omega
  have hleone {p : Fin 9} (hp : p ∈ B) : (I p).card ≤ 1 := by
    have hinc : U.erase p ⊆ B.erase p := by
      intro i hi
      exact mem_erase.mpr ⟨ne_of_mem_erase hi, hUB (mem_of_mem_erase hi)⟩
    have hsumU : (U.erase p).card ≤ ∑ i ∈ B.erase p, (I i).card := by
      calc
        _ = ∑ _i ∈ U.erase p, (1 : ℕ) := by simp
        _ ≤ ∑ i ∈ U.erase p, (I i).card :=
          sum_le_sum fun i hi => hposU (mem_of_mem_erase hi)
        _ ≤ _ := sum_le_sum_of_subset hinc
    have hsplit := sum_erase_add B (fun i => (I i).card) hp
    rw [hsum] at hsplit
    by_cases hpu : p ∈ U
    · rw [card_erase_of_mem hpu] at hsumU
      obtain ⟨n, hn⟩ := hodd hpu
      omega
    · rw [erase_eq_of_notMem hpu] at hsumU
      omega
  have hone {p : Fin 9} (hp : p ∈ B) : (I p).card = 1 := by
    have hsmall : ∑ i ∈ B.erase p, (I i).card ≤ (B.erase p).card := by
      calc
        _ ≤ ∑ _i ∈ B.erase p, (1 : ℕ) := sum_le_sum fun i hi => hleone (mem_of_mem_erase hi)
        _ = _ := by simp
    rw [card_erase_of_mem hp, hBc] at hsmall
    have hsplit := sum_erase_add B (fun i => (I i).card) hp
    rw [hsum] at hsplit
    have hle := hleone hp
    omega
  let block (e : Fin 9) := directions D (flip y e)
  have hsame {e f k : Fin 9} (he : e ∈ E) (hf : f ∈ E)
      (hke : k ∈ block e) (hkf : k ∈ block f) : e = f := by
    by_contra hef
    have hneE : k ≠ e := by
      intro h
      subst k
      exact (mem_sdiff.mp (hPsub hf (mem_erase.mpr ⟨hef, hkf⟩))).2 he
    have hneF : k ≠ f := by
      intro h
      subst k
      exact (mem_sdiff.mp (hPsub he (mem_erase.mpr ⟨fun h => hef h.symm, hke⟩))).2 hf
    have hkP : k ∈ P e := mem_erase.mpr ⟨hneE, hke⟩
    have hI := hone (hPsub he hkP)
    have heI : e ∈ I k := mem_filter.mpr ⟨he, hkP⟩
    have hfI : f ∈ I k := mem_filter.mpr ⟨hf, mem_erase.mpr ⟨hneF, hkf⟩⟩
    obtain ⟨t, ht⟩ := card_eq_one.mp hI
    have heq : e = t := by simpa only [ht, mem_singleton] using heI
    have hfq : f = t := by simpa only [ht, mem_singleton] using hfI
    exact hef (heq.trans hfq.symm)
  refine ⟨hUcard, ?_⟩
  change IsTriplePartition (E.image block)
  have hdeg {e : Fin 9} (he : e ∈ E) : (block e).card = 3 :=
    regular_directions D hrD ((mem_directions D y e).mp he)
  have hinj : Set.InjOn block (E : Set (Fin 9)) := by
    intro e he f hf heq
    exact hsame he hf (hback he) (heq ▸ hback he)
  refine ⟨(Finset.card_image_iff.mpr hinj).trans hEc, ?_, ?_⟩
  · intro A hA
    obtain ⟨e, he, rfl⟩ := mem_image.mp hA
    exact hdeg he
  · intro A hA B' hB' hab
    obtain ⟨e, he, rfl⟩ := mem_image.mp hA
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hB'
    exact disjoint_left.mpr fun {_} hke hkf => hab (congrArg block (hsame he hf hke hkf))


/-- Translate a vertex by the coordinate mask of its occupied directions. -/
noncomputable def directionOrigin (D : Finset (Q 9)) (y : Q 9) : Q 9 :=
    (directions D y).toList.foldl flip y

open Classical in
private theorem directions_eq_agreement_complement
    {C D : Finset (Q 9)}
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 3 ≤ hammingDist u v)
    {x y : Q 9} (hx : x ∈ C) (hy : y ∈ D) (hd : hammingDist x y = 3)
    (hdis : Disjoint (directions C x) (directions D y)) :
    directions D y = univ \ (directions C x ∪ differingAxes x y) := by
  have hm (u : Q 9) (hu : u ∈ C) (v : Q 9) (hv : v ∈ D) :
      hammingDist x y ≤ hammingDist u v := hd.le.trans (hsep u hu v hv)
  have hC := directions_subset_agreement hy hm
  have hD := directions_subset_agreement hx (C := D) (D := C) (x := y)
    (fun u hu v hv => by simpa only [hammingDist_comm] using hm v hv u hu)
  have heC : Disjoint (directions C x) (differingAxes x y) := disjoint_left.mpr
    fun _ hdir hdiff => (mem_diff x y _).mp hdiff (mem_filter.mp (hC hdir)).2
  have hs : directions D y ⊆ univ \ (directions C x ∪ differingAxes x y) := by
    intro i hi
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro h
    rcases mem_union.mp h with h | h
    · exact disjoint_left.mp hdis h hi
    · exact (mem_diff x y i).mp h (mem_filter.mp (hD hi)).2.symm
  apply eq_of_subset_of_card_le hs
  rw [card_univ_sdiff, Fintype.card_fin, card_union_of_disjoint heC,
    regular_directions C hrC hx, regular_directions D hrD hy]
  change 9 - (3 + hammingDist x y) ≤ 3
  rw [hd]

open Classical in
/-- Replacing a disagreeing axis by a first-step direction preserves the closest
distance and the vertex obtained by translating by all three occupied directions. -/
theorem unshared_two_step_preserves_direction_origin
    {C D : Finset (Q 9)}
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 3 ≤ hammingDist u v)
    (hdis : ∀ x ∈ C, ∀ y ∈ D, hammingDist x y = 3 →
      Disjoint (directions C x) (directions D y))
    {x y : Q 9} (hx : x ∈ C) (hy : y ∈ D) (hd : hammingDist x y = 3)
    {p : Fin 9} (hp : x p ≠ y p) :
    ∃ e ∈ directions D y,
      let z := flip (flip y e) p
      z ∈ D ∧ hammingDist x z = 3 ∧
        directions D z = insert p ((directions D y).erase e) ∧
        directionOrigin D z = directionOrigin D y := by
  let T := differingAxes x y
  let E := directions D y
  let P := neighborPartition D y
  have hpT : p ∈ T := (mem_diff x y p).mpr hp
  have hE := directions_eq_agreement_complement hrC hrD hsep hx hy hd (hdis x hx y hy hd)
  have hPE : P = E.image (fun e => directions D (flip y e)) := rfl
  have hpart : IsTriplePartition P := (axes_and_partition_of_unshared_contacts hrC hrD hbC hbD
    hsep hy ⟨x, hx, hd⟩ (fun u hu h => hdis u hu y hy h)).2
  have hcover : P.biUnion id = (univ : Finset (Fin 9)) := by
    apply eq_of_subset_of_card_le (subset_univ _)
    change (univ : Finset (Fin 9)).card ≤ (P.biUnion (fun A => A)).card
    rw [card_univ, Fintype.card_fin, card_biUnion (fun A hA B hB hAB =>
      hpart.disjoint_blocks hA hB hAB)]
    rw [sum_const_nat hpart.block_card, hpart.card_eq]
  have hpU : p ∈ P.biUnion id := by rw [hcover]; exact mem_univ _
  obtain ⟨R, hR, hpR⟩ := mem_biUnion.mp hpU
  rw [hPE] at hR
  obtain ⟨e, he, rfl⟩ := mem_image.mp hR
  have heT : e ∉ T := by
    intro heT
    have h := he
    change e ∈ directions D y at h
    rw [hE] at h
    exact (mem_sdiff.mp h).2 (mem_union_right _ heT)
  have hpE : p ∉ E := by
    intro h
    change p ∈ directions D y at h
    rw [hE] at h
    exact (mem_sdiff.mp h).2 (mem_union_right _ hpT)
  have hep : e ≠ p := fun h => heT (h ▸ hpT)
  let z := flip (flip y e) p
  have hz : z ∈ D := (mem_directions D (flip y e) p).mp hpR
  have hTz : differingAxes x z = insert e (T.erase p) := by
    rw [differingAxes_symm x z]
    change differingAxes (flip (flip y e) p) x = _
    rw [diff_flip_left, diff_flip_left, differingAxes_symm y x]
    rw [ite_eq_right heT]
    rw [ite_eq_left (mem_insert_of_mem hpT), erase_insert_of_ne hep]
  have hdz : hammingDist x z = 3 := by
    change (differingAxes x z).card = 3
    rw [hTz, card_insert_of_notMem (fun h => heT (mem_of_mem_erase h)), card_erase_of_mem hpT]
    change hammingDist x y - 1 + 1 = 3
    rw [hd]
  have hEz := directions_eq_agreement_complement hrC hrD hsep hx hz hdz (hdis x hx z hz hdz)
  have hpC : p ∉ directions C x := by
    intro hpC
    have hm (u : Q 9) (hu : u ∈ C) (v : Q 9) (hv : v ∈ D) :
        hammingDist x y ≤ hammingDist u v := hd.le.trans (hsep u hu v hv)
    exact hp (mem_filter.mp (directions_subset_agreement hy hm hpC)).2
  have hdir : directions D z = insert p (E.erase e) := by
    rw [hEz, hTz]
    ext i
    simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or, mem_insert, mem_erase]
    by_cases hip : i = p
    · subst i
      simp [hpC, Ne.symm hep]
    · by_cases hie : i = e
      · subst i
        simp [hip]
      · have hiE : i ∈ E ↔ ¬ i ∈ directions C x ∧ ¬ i ∈ T := by
          change i ∈ directions D y ↔ _
          rw [hE]
          simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or, T]
        simp [hip, hie, hiE]
  refine ⟨e, he, hz, hdz, hdir, ?_⟩
  funext i
  change directionOrigin D z i = directionOrigin D y i
  simp only [directionOrigin, foldl_flip_apply _ (nodup_toList _), mem_toList, hdir]
  change (if i ∈ insert p (E.erase e) then !(z i) else z i) =
    (if i ∈ E then !(y i) else y i)
  by_cases hip : i = p
  · subst i
    simp [z, BalancedCriticalSpectrum.flip, hpE, Ne.symm hep]
  · by_cases hie : i = e
    · subst i
      simp [z, BalancedCriticalSpectrum.flip, hip, he]
    · simp [z, BalancedCriticalSpectrum.flip, hip, hie]

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceThreeUnsharedDirections
