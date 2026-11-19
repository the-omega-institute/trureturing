import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedPlacements
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonCoverage

/-! Coverage of the paired search for placements with either normalized seed. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedCoverage

open private middleOptions labels from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements
open private separated fill_middles_member from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonCoverage
open private hollowEdges valid seed searchOrder stepOptions highPlacements highCandidates
  candidates hasExcessDegree checked from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedPlacements

private abbrev Vertex := BitVec 9
private abbrev Placement := Fin 10 → Vertex
private abbrev Step := Fin 10 × Fin 10 × Bool

private theorem valid_restrict (placed : List (Fin 10)) (p q : Placement)
    (agree : ∀ k ∈ placed, q k = p k) (full : valid labels p = true) :
    valid placed q = true := by
  unfold valid at full ⊢
  apply List.all_eq_true.mpr
  intro i hi
  apply List.all_eq_true.mpr
  intro j hj
  by_cases hij : i < j
  · have h := List.all_eq_true.mp (List.all_eq_true.mp full i (List.mem_finRange i))
      j (List.mem_finRange j)
    simp only [hij, ite_true] at h ⊢
    rw [agree i hi, agree j hj]
    refine Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp h).1, ?_⟩
    have h := (Bool.and_eq_true_iff.mp h).2
    cases hc : hollowEdges.contains (i, j)
    · simp
    · simp only [hc, Bool.not_true, Bool.false_or] at h ⊢
      refine Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp h).1, ?_⟩
      have ht : (middleOptions labels p i j).isEmpty = false := by
        simpa using (Bool.and_eq_true_iff.mp h).2
      obtain ⟨x, hx⟩ := List.isEmpty_eq_false_iff_exists_mem.mp ht
      have hx' : x ∈ middleOptions placed q i j := by
        unfold middleOptions at hx ⊢
        obtain ⟨hu, hv⟩ := List.mem_filter.mp hx
        refine List.mem_filter.mpr ⟨by simpa only [agree i hi] using hu, ?_⟩
        apply List.all_eq_true.mpr
        intro k hk
        rw [agree k hk]
        exact List.all_eq_true.mp hv k (List.mem_finRange k)
      simpa using List.isEmpty_eq_false_iff_exists_mem.mpr ⟨x, hx'⟩
  · simp [hij]

private def anchorsAvailable (placed : List (Fin 10)) : List Step → Bool
  | [] => true
  | s :: rest => placed.contains s.2.1 && anchorsAvailable (s.1 :: placed) rest

private theorem complete_steps (p : Placement) (full : valid labels p = true)
    (cut : ∀ i, (p i).getLsbD 0 = false) (rest : List Step)
    (moves : ∀ s ∈ rest, p s.1 ∈ stepOptions (p s.2.1) s.2.2)
    (placed : List (Fin 10)) (q : Placement) (agree : ∀ k ∈ placed, q k = p k)
    (available : anchorsAvailable placed rest = true) :
    ∃ r ∈ highPlacements placed q rest,
      ∀ k ∈ rest.map Prod.fst ++ placed, r k = p k := by
  induction rest generalizing placed q with
  | nil => exact ⟨q, by simp [highPlacements], agree⟩
  | cons s rest ih =>
    let i := s.1
    let q' := Function.update q i (p i)
    have agree' : ∀ k ∈ i :: placed, q' k = p k := by
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · simp [q']
      · by_cases h : k = i
        · simp [q', h]
        · simp [q', h, agree k hk]
    change (placed.contains s.2.1 && anchorsAvailable (i :: placed) rest) = true at available
    obtain ⟨anchor, available'⟩ := Bool.and_eq_true_iff.mp available
    obtain ⟨r, hr, hpr⟩ := ih (fun t ht => moves t (List.mem_cons_of_mem _ ht))
      (i :: placed) q' agree' available'
    have ha : s.2.1 ∈ placed := by simpa using anchor
    refine ⟨r, ?_, ?_⟩
    · unfold highPlacements
      apply List.mem_flatMap.mpr
      refine ⟨p i, by rw [agree _ ha]; exact moves s (List.mem_cons_self ..), ?_⟩
      have hv := valid_restrict (i :: placed) p q' agree' full
      change r ∈ (if !(p i).getLsbD 0 && valid (i :: placed) q'
        then highPlacements (i :: placed) q' rest else [])
      rw [cut i, hv]
      exact hr
    · intro k hk
      apply hpr k
      simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at hk ⊢
      change k = i ∨ _ at hk
      tauto

/-- Every normalized paired placement and its compatible subdivisions occur in
the finite search, so its reconstruction has a vertex of degree above three. -/
theorem normalized_placement_excess_degree (sameAxis : Bool) (p : Placement)
    (roots : ∀ k ∈ ([0, 1, 2, 7] : List (Fin 10)), seed sameAxis k = p k)
    (full : valid labels p = true) (cut : ∀ i, (p i).getLsbD 0 = false)
    (moves : ∀ s ∈ searchOrder, p s.1 ∈ stepOptions (p s.2.1) s.2.2)
    (middle : Fin 10 × Fin 10 → Vertex)
    (options : ∀ e ∈ hollowEdges, middle e ∈ middleOptions labels p e.1 e.2)
    (distinct : (hollowEdges.map middle).Pairwise separated) :
    hasExcessDegree ((hollowEdges.map middle).reverse ++ labels.map p) = true := by
  obtain ⟨r, hr, hagree⟩ := complete_steps p full cut searchOrder moves
    [0, 1, 2, 7] (seed sameAxis) roots (by decide)
  have cover : ∀ k : Fin 10, k ∈ searchOrder.map Prod.fst ++ [0, 1, 2, 7] := by decide
  have he : r = p := funext fun k => hagree k (cover k)
  rw [he] at hr
  have member : (hollowEdges.map middle).reverse ++ labels.map p ∈ candidates sameAxis := by
    unfold candidates
    exact List.mem_flatMap.mpr ⟨p, hr, List.mem_map.mpr ⟨_,
      by simpa using fill_middles_member p middle hollowEdges [] options distinct (by simp), rfl⟩⟩
  exact List.all_eq_true.mp (checked sameAxis) _ member

#print axioms normalized_placement_excess_degree

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedCoverage
