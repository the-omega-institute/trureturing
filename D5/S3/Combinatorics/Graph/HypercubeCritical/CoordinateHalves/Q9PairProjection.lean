/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Surjectivity of two-coordinate projections for balanced cubic nine-cube supports. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

/-! Counting directional edge endpoints rules out missing two-coordinate patterns. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairProjection

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced directionEdges direction_edge_count)
open BalancedCubeComponentBoundary (directions regular_directions)
open BalancedCubeGirth (no_selected_square)

local notation "flip" => BalancedCriticalSpectrum.flip

open Classical in
/-- Every pair of distinct coordinates attains all four bit pairs on an order-72
balanced cubic support whose coordinate halves have at least 30 vertices.
The proof uses the uniform edge count and square exclusion for Huang's cube
signing from the construction in Mathlib's `Archive.Sensitivity`. -/
theorem pair_projection_surjective {S : Finset (Q 9)} (hsize : S.card = 72)
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S)
    (hhalf : ∀ (k : Fin 9) (r : Bool), 30 ≤ (S.filter (fun x => x k = r)).card)
    {i j : Fin 9} (hij : i ≠ j) (b c : Bool) :
    ∃ x ∈ S, x i = b ∧ x j = c := by
  apply Classical.byContradiction
  intro hmissing
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
    by_cases hxi : x i = b <;> by_cases hxj : x j = c <;>
      simp [A, B, C, hxi, hxj]
  have hsum : A.card + (B.card + C.card) = 72 := by
    rw [← Finset.card_union_of_disjoint hBC, ← Finset.card_union_of_disjoint hABC,
      hpartition, hsize]
  have hA_le : A.card ≤ 12 := by
    have hBC_ge : 60 ≤ B.card + C.card := Nat.add_le_add (hhalf i b) (hhalf j c)
    have hle : A.card + 60 ≤ 12 + 60 := by
      calc
        A.card + 60 ≤ A.card + (B.card + C.card) := Nat.add_le_add_left hBC_ge _
        _ = 12 + 60 := hsum
    exact le_of_add_le_add_right hle

  let E (k : Fin 9) (r : Bool) := S.filter (fun x => x k ≠ r ∧ flip x k ∈ S)
  have hE_card (k : Fin 9) (r : Bool) : (E k r).card = 12 := by
    let F := S.filter (fun x => x k = false ∧ flip x k ∈ S)
    let T := S.filter (fun x => x k = true ∧ flip x k ∈ S)
    have hF : F.card = 12 := by
      change directionEdges S k = 12
      have hcount : 6 * directionEdges S k = 6 * 12 := by
        calc
          6 * directionEdges S k = S.card := direction_edge_count (d := 3) S hr hb k
          _ = 6 * 12 := hsize
      exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ 5) hcount
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
    apply hmissing
    exact ⟨flip x i, hflip, by simpa using flip_bit hxi,
      by simpa [BalancedCriticalSpectrum.flip, hij.symm] using hxj⟩
  have hEj : E j c ⊆ A := by
    intro x hxE
    obtain ⟨hx, hxj, hflip⟩ := Finset.mem_filter.mp hxE
    refine Finset.mem_filter.mpr ⟨hx, ?_, hxj⟩
    intro hxi
    apply hmissing
    exact ⟨flip x j, hflip, by simpa [BalancedCriticalSpectrum.flip, hij] using hxi,
      by simpa using flip_bit hxj⟩
  have hAEi : A = E i b := (Finset.eq_of_subset_of_card_le hEi
    (hA_le.trans (hE_card i b).ge)).symm
  have hAEj : A = E j c := (Finset.eq_of_subset_of_card_le hEj
    (hA_le.trans (hE_card j c).ge)).symm
  have hA_card : A.card = 12 := by rw [hAEj, hE_card]
  have hA_nonempty : A.Nonempty := Finset.card_pos.mp (by
    simpa only [hA_card] using Nat.zero_lt_succ 11)
  obtain ⟨x, hxA⟩ := hA_nonempty
  obtain ⟨hx, hxi, hxj⟩ := Finset.mem_filter.mp hxA
  have i_neighbor {y : Q 9} (hy : y ∈ A) : flip y i ∈ S := by
    rw [hAEi] at hy
    exact (Finset.mem_filter.mp hy).2.2
  have hdirections : ({i, j} : Finset (Fin 9)).card < (directions S x).card := by
    simpa only [Finset.card_pair hij, regular_directions S hr hx] using Nat.lt_succ_self 2
  obtain ⟨k, hk, hknot⟩ := Finset.exists_mem_notMem_of_card_lt_card hdirections
  have hki : k ≠ i := fun he => hknot (by simp [he])
  have hkj : k ≠ j := fun he => hknot (by simp [he])
  have hxk : flip x k ∈ S := by
    simpa [directions] using hk
  have hxkA : flip x k ∈ A := Finset.mem_filter.mpr
    ⟨hxk, by simpa [BalancedCriticalSpectrum.flip, hki.symm] using hxi, by simpa [BalancedCriticalSpectrum.flip, hkj.symm] using hxj⟩
  exact no_selected_square hb hki hx hxk (i_neighbor hxA) (i_neighbor hxkA)

#print axioms pair_projection_surjective

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairProjection
