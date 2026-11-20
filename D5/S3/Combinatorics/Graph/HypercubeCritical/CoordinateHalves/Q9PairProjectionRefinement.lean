/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjectionRefinement
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjectionRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A missing pair bounds the half-size sum and forces a four-star fiber at equality. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

/-! The partition and crossing count follow `Q9PairProjection`. Square exclusion
sends the third edge of each double-crossing vertex to a zero-crossing vertex. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairProjectionRefinement

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced directionEdges direction_edge_count)
open BalancedCubeComponentBoundary (directions regular_directions)
open BalancedCubeGirth (no_selected_square)

local notation "flip" => BalancedCriticalSpectrum.flip

open Classical in
private theorem missing_pair_partition_card {S : Finset (Q 9)} {i j : Fin 9} {b c : Bool}
    (hmissing : ¬ ∃ x ∈ S, x i = b ∧ x j = c) :
    (S.filter (fun x => x i ≠ b ∧ x j ≠ c)).card +
      ((S.filter (fun x => x i = b)).card + (S.filter (fun x => x j = c)).card) = S.card := by
  let A := S.filter (fun x => x i ≠ b ∧ x j ≠ c)
  let B := S.filter (fun x => x i = b)
  let C := S.filter (fun x => x j = c)
  have hBC : Disjoint B C := Finset.disjoint_left.mpr (by
    intro x hxB hxC
    obtain ⟨hx, hxi⟩ := Finset.mem_filter.mp hxB
    exact hmissing ⟨x, hx, hxi, (Finset.mem_filter.mp hxC).2⟩)
  have hABC : Disjoint A (B ∪ C) := Finset.disjoint_left.mpr (by
    intro x hxA hxBC
    obtain ⟨_, hxi, hxj⟩ := Finset.mem_filter.mp hxA
    rcases Finset.mem_union.mp hxBC with hxB | hxC
    · exact hxi (Finset.mem_filter.mp hxB).2
    · exact hxj (Finset.mem_filter.mp hxC).2)
  have hpartition : A ∪ (B ∪ C) = S := by
    ext x
    by_cases hxi : x i = b <;> by_cases hxj : x j = c <;> simp [A, B, C, hxi, hxj]
  change A.card + (B.card + C.card) = S.card
  rw [← Finset.card_union_of_disjoint hBC, ← Finset.card_union_of_disjoint hABC, hpartition]

open Classical in
private theorem missing_pair_opposite_fiber {S : Finset (Q 9)} (hsize : S.card = 72)
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) {i j : Fin 9} (hij : i ≠ j) {b c : Bool}
    (hmissing : ¬ ∃ x ∈ S, x i = b ∧ x j = c) :
    let A := S.filter (fun x => x i ≠ b ∧ x j ≠ c)
    let E (k : Fin 9) (r : Bool) := S.filter (fun x => x k ≠ r ∧ flip x k ∈ S)
    let D := E i b ∩ E j c
    let N := A \ (E i b ∪ E j c)
    16 ≤ A.card ∧ (A.card = 16 →
      D.card = 12 ∧ N.card = 4 ∧ Disjoint D N ∧ D ∪ N = A ∧
      (∀ x ∈ D, ∃ k : Fin 9, directions A x = {k} ∧ flip x k ∈ N) ∧
      (∀ y ∈ N, (directions A y).card = 3 ∧ ∀ k ∈ directions A y, flip y k ∈ D)) := by
  dsimp only
  let A := S.filter (fun x => x i ≠ b ∧ x j ≠ c)
  let E (k : Fin 9) (r : Bool) := S.filter (fun x => x k ≠ r ∧ flip x k ∈ S)
  have hE_card (k : Fin 9) (r : Bool) : (E k r).card = 12 := by
    let F := S.filter (fun x => x k = false ∧ flip x k ∈ S)
    let T := S.filter (fun x => x k = true ∧ flip x k ∈ S)
    have hF : F.card = 12 := by
      change directionEdges S k = 12
      have hcount := direction_edge_count (d := 3) S hr hb k
      rw [hsize] at hcount
      omega
    have hFT : F.card = T.card := by
      apply Finset.card_bij (fun x _ => flip x k)
      · intro x hx
        simp only [F, Finset.mem_filter] at hx
        simp [T, hx.1, hx.2.1, hx.2.2]
      · intro x _ y _ hxy
        simpa using congrArg (fun z : Q 9 => flip z k) hxy
      · intro y hy
        simp only [T, Finset.mem_filter] at hy
        refine ⟨flip y k, ?_, by simp⟩
        simp [F, hy.1, hy.2.1, hy.2.2]
    cases r with
    | false =>
      have h : E k false = T := by
        ext x
        cases hx : x k <;> simp [E, T, hx]
      rw [h]
      exact hFT.symm.trans hF
    | true =>
      have h : E k true = F := by
        ext x
        cases hx : x k <;> simp [E, F, hx]
      rw [h]
      exact hF
  have flip_bit {t r : Bool} (h : t ≠ r) : (!t) = r := by
    cases t <;> cases r <;> simp_all
  have hEi : E i b ⊆ A := by
    intro x hxE
    obtain ⟨hx, hxi, hflip⟩ := Finset.mem_filter.mp hxE
    refine Finset.mem_filter.mpr ⟨hx, hxi, ?_⟩
    intro hxj
    exact hmissing ⟨flip x i, hflip, by simpa using flip_bit hxi,
      by simpa [BalancedCriticalSpectrum.flip, hij.symm] using hxj⟩
  have hEj : E j c ⊆ A := by
    intro x hxE
    obtain ⟨hx, hxj, hflip⟩ := Finset.mem_filter.mp hxE
    refine Finset.mem_filter.mpr ⟨hx, ?_, hxj⟩
    intro hxi
    exact hmissing ⟨flip x j, hflip, by simpa [BalancedCriticalSpectrum.flip, hij] using hxi,
      by simpa using flip_bit hxj⟩
  -- Count the union of the crossing endpoints and its complement within A.
  let D := E i b ∩ E j c
  let N := A \ (E i b ∪ E j c)
  have hDle : D.card ≤ 12 := by
    rw [← hE_card i b]
    exact Finset.card_le_card Finset.inter_subset_left
  have hpartition : A.card + D.card = 24 + N.card := by
    have hUnion := Finset.card_union_add_card_inter (E i b) (E j c)
    rw [hE_card, hE_card] at hUnion
    have hN := Finset.card_sdiff_add_card_eq_card (Finset.union_subset hEi hEj)
    change (E i b ∪ E j c).card + D.card = 12 + 12 at hUnion
    change N.card + (E i b ∪ E j c).card = A.card at hN
    omega
  -- A third edge at a double-crossing vertex cannot complete a selected square.
  have hthird (x : Q 9) : ∃ k : Fin 9, x ∈ D →
      directions S x = insert k {i, j} ∧ flip x k ∈ N := by
    by_cases hxD : x ∈ D
    · obtain ⟨hxEi, hxEj⟩ := Finset.mem_inter.mp hxD
      obtain ⟨hx, hxi, hxj⟩ := Finset.mem_filter.mp (hEi hxEi)
      have hxiS := (Finset.mem_filter.mp hxEi).2.2
      have hxjS := (Finset.mem_filter.mp hxEj).2.2
      have hdeg := regular_directions S hr hx
      have hlt : ({i, j} : Finset (Fin 9)).card < (directions S x).card := by
        rw [Finset.card_pair hij, hdeg]
        decide
      obtain ⟨k, hk, hknot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      have hki : k ≠ i := fun he => hknot (by simp [he])
      have hkj : k ≠ j := fun he => hknot (by simp [he])
      have hxk : flip x k ∈ S := by simpa [directions] using hk
      have hdirs : directions S x = insert k {i, j} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro l hl
          have h : l = k ∨ l = i ∨ l = j := by simpa using hl
          rcases h with rfl | rfl | rfl
          · exact hk
          · simpa [directions] using hxiS
          · simpa [directions] using hxjS
        · rw [Finset.card_insert_of_notMem hknot, Finset.card_pair hij, hdeg]
      refine ⟨k, fun _ => ⟨hdirs, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩⟩
      · exact Finset.mem_filter.mpr
          ⟨hxk, by simpa [BalancedCriticalSpectrum.flip, hki.symm] using hxi,
            by simpa [BalancedCriticalSpectrum.flip, hkj.symm] using hxj⟩
      · intro hy
        rcases Finset.mem_union.mp hy with hyi | hyj
        · exact no_selected_square hb hki hx hxk hxiS (Finset.mem_filter.mp hyi).2.2
        · exact no_selected_square hb hkj hx hxk hxjS (Finset.mem_filter.mp hyj).2.2
    · exact ⟨i, fun hx => (hxD hx).elim⟩
  choose k hk using hthird
  -- Store the zero-crossing neighbor together with the direction back to the leaf.
  let target := N.sigma (directions S)
  let f (x : Q 9) : Σ _ : Q 9, Fin 9 := ⟨flip x (k x), k x⟩
  have hf : Function.Injective f := by
    intro x z h
    have hDir : k x = k z := congrArg (fun p : Σ _ : Q 9, Fin 9 => p.2) h
    have hVertex : flip x (k x) = flip z (k z) := congrArg Sigma.fst h
    rw [← hDir] at hVertex
    simpa using congrArg (fun v : Q 9 => flip v (k x)) hVertex
  have hsub : D.image f ⊆ target := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    have hyN := (hk x hx).2
    have hback : k x ∈ directions S (flip x (k x)) := by
      have hxS := (Finset.mem_filter.mp (hEi (Finset.mem_inter.mp hx).1)).1
      simpa [directions] using hxS
    exact Finset.mem_sigma.mpr ⟨hyN, hback⟩
  have htarget : target.card = N.card * 3 := by
    change (N.sigma (directions S)).card = N.card * 3
    rw [Finset.card_sigma]
    apply Finset.sum_const_nat
    intro y hy
    exact regular_directions S hr (Finset.mem_filter.mp (Finset.mem_sdiff.mp hy).1).1
  have himage : (D.image f).card = D.card := Finset.card_image_of_injective _ hf
  have hcapacity := Finset.card_le_card hsub
  rw [himage, htarget] at hcapacity
  change 16 ≤ A.card ∧ _
  refine ⟨by omega, ?_⟩
  change A.card = 16 → _
  intro hA
  have hD : D.card = 12 := by omega
  have hN : N.card = 4 := by omega
  have hfull : D.image f = target := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [himage, htarget, hD, hN]
  have hDi : D = E i b := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
    rw [hD, hE_card])
  have hDj : D = E j c := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
    rw [hD, hE_card])
  have hUnion : E i b ∪ E j c = D := by rw [← hDi, ← hDj, Finset.union_self]
  have hDsub : D ⊆ A := by
    rw [hDi]
    exact hEi
  have hNdiff : N = A \ D := by
    change A \ (E i b ∪ E j c) = A \ D
    rw [hUnion]
  change D.card = 12 ∧ N.card = 4 ∧ Disjoint D N ∧ D ∪ N = A ∧ _
  refine ⟨hD, hN, ?_, ?_, ?_, ?_⟩
  · rw [hNdiff]
    exact Finset.disjoint_left.mpr fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx
  · rw [hNdiff]
    exact Finset.union_sdiff_of_subset hDsub
  · intro x hx
    obtain ⟨hdirs, hneighbor⟩ := hk x hx
    obtain ⟨_, hxi, hxj⟩ := Finset.mem_filter.mp (hDsub hx)
    refine ⟨k x, ?_, hneighbor⟩
    ext l
    constructor
    · intro hl
      have hlA : flip x l ∈ A := (Finset.mem_filter.mp hl).2
      have hlS : l ∈ directions S x := by
        simpa [directions] using (Finset.mem_filter.mp hlA).1
      rw [hdirs] at hlS
      have h : l = k x ∨ l = i ∨ l = j := by simpa using hlS
      rcases h with rfl | rfl | rfl
      · exact Finset.mem_singleton_self _
      · exact ((Finset.mem_filter.mp hlA).2.1 (by simpa using flip_bit hxi)).elim
      · exact ((Finset.mem_filter.mp hlA).2.2 (by simpa using flip_bit hxj)).elim
    · intro hl
      rw [Finset.mem_singleton.mp hl]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hneighbor).1⟩
  · intro y hy
    have hall (l : Fin 9) (hl : l ∈ directions S y) : flip y l ∈ D := by
      have hp : (⟨y, l⟩ : Σ _ : Q 9, Fin 9) ∈ target := Finset.mem_sigma.mpr ⟨hy, hl⟩
      rw [← hfull] at hp
      obtain ⟨x, hx, h⟩ := Finset.mem_image.mp hp
      have hDir : k x = l := congrArg (fun p : Σ _ : Q 9, Fin 9 => p.2) h
      have hVertex : flip x (k x) = y := congrArg Sigma.fst h
      rw [hDir] at hVertex
      rwa [← hVertex, BalancedCriticalSpectrum.flip_flip]
    have hdirs : directions A y = directions S y := by
      ext l
      simp only [directions, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hl => (Finset.mem_filter.mp hl).1,
        fun hl => hDsub (hall l (by simpa [directions] using hl))⟩
    rw [hdirs]
    exact ⟨regular_directions S hr (Finset.mem_filter.mp (Finset.mem_sdiff.mp hy).1).1, hall⟩

open Classical in
/-- If a bit pair is absent, its two disjoint coordinate halves have total size at most 56. -/
theorem missing_pair_half_sum_le {S : Finset (Q 9)} (hsize : S.card = 72)
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) {i j : Fin 9} (hij : i ≠ j) {b c : Bool}
    (hmissing : ¬ ∃ x ∈ S, x i = b ∧ x j = c) :
    (S.filter (fun x => x i = b)).card + (S.filter (fun x => x j = c)).card ≤ 56 := by
  have hpartition := missing_pair_partition_card hmissing
  have hlower := (missing_pair_opposite_fiber hsize hr hb hij hmissing).1
  omega

open Classical in
/-- If both missing-pair halves have size at least 28, each has size 28 and the
opposite fiber is a disjoint union of four 3-stars, with leaves `D` and centers `N`. -/
theorem missing_pair_halves_eq_twenty_eight {S : Finset (Q 9)} (hsize : S.card = 72)
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) {i j : Fin 9} (hij : i ≠ j) {b c : Bool}
    (hmissing : ¬ ∃ x ∈ S, x i = b ∧ x j = c)
    (hi : 28 ≤ (S.filter (fun x => x i = b)).card)
    (hj : 28 ≤ (S.filter (fun x => x j = c)).card) :
    (S.filter (fun x => x i = b)).card = 28 ∧ (S.filter (fun x => x j = c)).card = 28 ∧
    let A := S.filter (fun x => x i ≠ b ∧ x j ≠ c)
    let E (k : Fin 9) (r : Bool) := S.filter (fun x => x k ≠ r ∧ flip x k ∈ S)
    let D := E i b ∩ E j c
    let N := A \ (E i b ∪ E j c)
    D.card = 12 ∧ N.card = 4 ∧ Disjoint D N ∧ D ∪ N = A ∧
      (∀ x ∈ D, ∃ k : Fin 9, directions A x = {k} ∧ flip x k ∈ N) ∧
      (∀ y ∈ N, (directions A y).card = 3 ∧ ∀ k ∈ directions A y, flip y k ∈ D) := by
  have hsum := missing_pair_half_sum_le hsize hr hb hij hmissing
  have hpartition := missing_pair_partition_card hmissing
  have hstars := (missing_pair_opposite_fiber hsize hr hb hij hmissing).2
  exact ⟨by omega, by omega, hstars (by omega)⟩

#print axioms missing_pair_half_sum_le
#print axioms missing_pair_halves_eq_twenty_eight

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairProjectionRefinement
