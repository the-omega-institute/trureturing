import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayRepresentativeBounds
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayPlacementReconstruction
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixClosingCertificates

/-! Two separate balanced cubic components of order 54 cannot both lie in
a 258-vertex degree-three restriction of the nine-cube. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwoGrayComponents

open Finset
open D5.S3.Combinatorics.Graph.Hypercube
open Q9GrayPlacementNormalForm (Vertex placement)
open Q9GrayCrossedPlacement (cube)
open BalancedCriticalSpectrum (IsBalanced)
attribute [local instance] Classical.propDecidable

private theorem card_le_of_two_placements
    (first second : Fin 9 → Fin 3) (c d : Vertex)
    (hfirst : ∀ b, (univ.filter (fun i => first i = b)).card = 3)
    (hsecond : ∀ b, (univ.filter (fun i => second i = b)).card = 3)
    (hsep : ∀ x ∈ placement first c, ∀ y ∈ placement second d, 1 < hammingDist x y)
    (U : Finset Vertex) (hU : placement first c ∪ placement second d ⊆ U)
    (hcl : ∀ x ∈ placement first c ∪ placement second d, ∀ y ∈ U,
      (hypercube 9).Adj x y → y ∈ placement first c ∪ placement second d)
    (hdeg : ∀ v ∈ U, (U.filter ((hypercube 9).Adj v)).card ≤ 3) : U.card ≤ 257 := by
  obtain ⟨e, k, t, ht, hd, hA, hB⟩ :=
    Q9GrayRelativeCenters.separated_pair_normal_form first second c d hfirst hsecond hsep
  let f := e.trans (cubeBitVec 9).symm
  let W := U.map f.toEmbedding
  have hF (x : Vertex) : cubeBitVec 9 (f x) = e x := by simp [f]
  have hAdj (x y : Vertex) : cube.Adj (f x) (f y) ↔ (hypercube 9).Adj x y := by
    change hammingDist (cubeBitVec 9 (f x)) (cubeBitVec 9 (f y)) = 1 ↔ hammingDist x y = 1
    rw [hF x, hF y, hd]
  have hf : (placement first c ∪ placement second d).map f.toEmbedding =
      Q9GrayEasyPlacements.supports k t := by
    change (placement first c ∪ placement second d).map
      (e.toEmbedding.trans (cubeBitVec 9).symm.toEmbedding) = _
    rw [← map_map, map_union, hA, hB]
    apply Finset.ext_iff.mpr
    intro v
    obtain ⟨y, rfl⟩ := (cubeBitVec 9).symm.surjective v
    rw [Q9GrayEasyPlacements.mem_supports]
    simp only [mem_map, Equiv.toEmbedding_apply, Equiv.apply_eq_iff_eq, exists_eq_right,
      mem_union, Equiv.apply_symm_apply]
  have hWs : Q9GrayEasyPlacements.supports k t ⊆ W := by
    rw [← hf]
    exact map_subset_map.mpr hU
  have hWc : ∀ x ∈ Q9GrayEasyPlacements.supports k t, ∀ y ∈ W,
      cube.Adj x y → y ∈ Q9GrayEasyPlacements.supports k t := by
    intro x hx y hy hxy
    rw [← hf] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_map.mp hy
    exact mem_map.mpr ⟨b, hcl a ha b hb ((hAdj a b).mp hxy), rfl⟩
  have hWd : ∀ x ∈ W, (W.filter (cube.Adj x)).card ≤ 3 := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hx
    unfold W
    rw [filter_map, card_map]
    simpa only [Function.comp_apply, Equiv.toEmbedding_apply, hAdj] using hdeg v hv
  have h := Q9GrayRepresentativeBounds.candidate_card_le k t ht W hWs hWc hWd
  simpa only [W, card_map] using h

/-- Two separated Huang-balanced induced cubic components of order 54 limit
the whole degree-three candidate to at most 257 vertices. -/
theorem card_le_of_two_balanced_cubic_fifty_four
    (U C D : Finset Vertex) (hC : C.card = 54) (hD : D.card = 54)
    (hrC : ((hypercube 9).induce (C : Set Vertex)).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set Vertex)).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 1 < hammingDist x y)
    (hU : C ∪ D ⊆ U)
    (hcl : ∀ x ∈ C ∪ D, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C ∪ D)
    (hdeg : ∀ v ∈ U, (U.filter ((hypercube 9).Adj v)).card ≤ 3) : U.card ≤ 257 := by
  obtain ⟨first, c, ha, rfl⟩ :=
    Q9GrayPlacementReconstruction.exists_placement_of_balanced_cubic C hC hrC hbC
  obtain ⟨second, d, hb, rfl⟩ :=
    Q9GrayPlacementReconstruction.exists_placement_of_balanced_cubic D hD hrD hbD
  exact card_le_of_two_placements first second c d ha hb hsep U hU hcl hdeg

#print axioms card_le_of_two_balanced_cubic_fifty_four

/-- A 258-vertex degree-three candidate contains an actual Huang-balanced
cubic component of order at least 72. -/
theorem exists_large_balanced_component (U : Finset Vertex) (hU : U.card = 258)
    (hdeg : ∀ v : (U : Set Vertex), ((hypercube 9).induce (U : Set Vertex)).degree v ≤ 3) :
    ∃ K : ((hypercube 9).induce (U : Set Vertex)).ConnectedComponent,
      let C := TwoBalancedComponents.componentFinset U K
      ((hypercube 9).induce (C : Set Vertex)).IsRegularOfDegree 3 ∧
        IsBalanced C ∧ 72 ≤ C.card := by
  classical
  obtain ⟨K, L, _, C, D, hK, hL, hCn, hDn, hCU, hDU, hdis, hclC, hclD, hrC, hrD,
    hbC, hbD, _⟩ := TwoBalancedComponents.exists_two_balanced_components U hU hdeg
  rcases q9_balanced_induced_cubic_small_orders C hCn hrC hbC with h54C | h72C
  · rcases q9_balanced_induced_cubic_small_orders D hDn hrD hbD with h54D | h72D
    · have hsep : ∀ x ∈ C, ∀ y ∈ D, 1 < hammingDist x y := by
        intro x hx y hy
        by_contra! hn
        have hne : x ≠ y := by
          rintro rfl
          exact Finset.disjoint_left.mp hdis hx hy
        have hpos : hammingDist x y ≠ 0 := fun h => hne (hammingDist_eq_zero.mp h)
        have hadj : (hypercube 9).Adj x y := by
          change hammingDist x y = 1
          omega
        exact Finset.disjoint_left.mp hdis (hclC x hx y (hDU hy) hadj) hy
      have hdegU : ∀ v ∈ U, (U.filter ((hypercube 9).Adj v)).card ≤ 3 := by
        intro v hv
        have h := congrArg Finset.card
          (SimpleGraph.map_neighborFinset_induce (G := hypercube 9) ⟨v, hv⟩)
        rw [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree] at h
        have he : U.filter ((hypercube 9).Adj v) = (hypercube 9).neighborFinset v ∩ U := by
          ext x
          simp [SimpleGraph.mem_neighborFinset, and_comm]
        have hcard : ((hypercube 9).induce (U : Set Vertex)).degree ⟨v, hv⟩ =
            ((hypercube 9).neighborFinset v ∩ U).card := by
          rw [Finset.toFinset_coe] at h
          refine Eq.trans ?_ h
          exact congrArg (fun inst => @SimpleGraph.degree _ ((hypercube 9).induce (U : Set Vertex))
            ⟨v, hv⟩ inst) (Subsingleton.elim _ _)
        rw [he, ← hcard]
        exact hdeg ⟨v, hv⟩
      have h := card_le_of_two_balanced_cubic_fifty_four U C D h54C h54D hrC hrD hbC hbD
        hsep (union_subset hCU hDU) (by
          intro x hx y hy ha
          rcases mem_union.mp hx with hx | hx
          · exact mem_union_left _ (hclC x hx y hy ha)
          · exact mem_union_right _ (hclD x hx y hy ha)) hdegU
      omega
    · exact ⟨L, by rw [← hL]; exact ⟨hrD, hbD, h72D⟩⟩
  · exact ⟨K, by rw [← hK]; exact ⟨hrC, hbC, h72C⟩⟩

#print axioms exists_large_balanced_component

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwoGrayComponents
