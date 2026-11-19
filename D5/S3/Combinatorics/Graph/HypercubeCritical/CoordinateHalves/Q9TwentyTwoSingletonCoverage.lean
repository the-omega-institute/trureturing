import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements

/-! Coverage of the two singleton-parity searches for normalized placements. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonCoverage

open private adjacent adjacent_iff moves from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SeventyTwoEmbeddingSearch
open private attachment solid hollow middleOptions valid root cycleVertices firstPointAxes
  highPlacements highCandidates labels hollowEdges fillMiddles candidates reconstructionSize checked
  from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements

private abbrev Vertex := BitVec 9
private abbrev Placement := Fin 10 → Vertex

private theorem valid_restrict (opposite : Bool) (placed : List (Fin 10))
    (p q : Placement) (agree : ∀ k ∈ placed, q k = p k)
    (full : valid opposite labels p = true) :
    valid opposite placed q = true := by
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
    cases hc : hollow opposite i j
    · simp
    · simp only [hc, Bool.not_true, Bool.false_or] at h ⊢
      refine Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp h).1, ?_⟩
      have ht : (middleOptions labels p i j).isEmpty = false := by
        simpa using (Bool.and_eq_true_iff.mp h).2
      obtain ⟨x, hx⟩ := List.isEmpty_eq_false_iff_exists_mem.mp ht
      have hx' : x ∈ middleOptions placed q i j := by
        unfold middleOptions at hx ⊢
        obtain ⟨hu, hv⟩ := List.mem_filter.mp hx
        apply List.mem_filter.mpr
        refine ⟨by simpa only [agree i hi] using hu, List.all_eq_true.mpr ?_⟩
        intro k hk
        rw [agree k hk]
        exact List.all_eq_true.mp hv k (List.mem_finRange k)
      have := List.isEmpty_eq_false_iff_exists_mem.mpr ⟨x, hx'⟩
      simpa using this
  · simp [hij]

private def cycleIndex (c : Fin 6) : Fin 10 := ⟨c.val + 4, by omega⟩

private theorem high_membership (opposite : Bool) (p : Placement)
    (full : valid opposite labels p = true)
    (hcut : ∀ c : Fin 6, (p (cycleIndex c)).getLsbD 0 = false)
    (hfirst : firstPointAxes (p (cycleIndex 0)) = true)
    (hmove : ∀ c : Fin 6, p (cycleIndex c) ∈ moves (p (attachment opposite c)))
    (rest : List (Fin 6)) (placed : List (Fin 10)) (q : Placement)
    (agree : ∀ k ∈ placed, q k = p k)
    (hanchor : ∀ c ∈ rest, attachment opposite c ∈ placed) :
    ∃ r ∈ highPlacements opposite placed q rest,
      ∀ k ∈ rest.map cycleIndex ++ placed, r k = p k := by
  induction rest generalizing placed q with
  | nil => exact ⟨q, by simp [highPlacements], agree⟩
  | cons c rest ih =>
    let i := cycleIndex c
    let q' := Function.update q i (p i)
    have agree' : ∀ k ∈ i :: placed, q' k = p k := by
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · simp [q']
      · by_cases h : k = i
        · simp [q', h]
        · simp [q', h, agree k hk]
    have hanchor' : ∀ a ∈ rest, attachment opposite a ∈ i :: placed :=
      fun a ha => List.mem_cons_of_mem _ (hanchor a (List.mem_cons_of_mem _ ha))
    obtain ⟨r, hr, hpr⟩ := ih (i :: placed) q' agree' hanchor'
    refine ⟨r, ?_, ?_⟩
    · unfold highPlacements
      apply List.mem_flatMap.mpr
      have ha := agree _ (hanchor c (List.mem_cons_self ..))
      have hmc : p i ∈ moves (q (attachment opposite c)) := by rw [ha]; exact hmove c
      refine ⟨p i, hmc, ?_⟩
      have hv := valid_restrict opposite (i :: placed) p q' agree' full
      have hcanon : (c != 0 || firstPointAxes (p i)) = true := by
        by_cases h : c = 0
        · subst c
          exact Bool.or_eq_true_iff.mpr (Or.inr hfirst)
        · simp [h]
      change r ∈ (if !(p i).getLsbD 0 && (c != 0 || firstPointAxes (p i)) &&
          valid opposite (i :: placed) q' then highPlacements opposite (i :: placed) q' rest
        else [])
      rw [hcut c, hcanon, hv]
      exact hr
    · intro k hk
      apply hpr k
      simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at hk ⊢
      change k = i ∨ _ at hk
      tauto

/-- The search contains every normalized high-vertex placement satisfying the
local constraints of the singleton parity case. -/
theorem high_candidate_of_normalized (opposite : Bool) (p : Placement)
    (hroot : ∀ k ∈ ([0, 1, 2, 3] : List (Fin 10)), root k = p k)
    (full : valid opposite labels p = true)
    (hcut : ∀ c : Fin 6, (p (cycleIndex c)).getLsbD 0 = false)
    (hfirst : firstPointAxes (p (cycleIndex 0)) = true)
    (hmove : ∀ c : Fin 6, p (cycleIndex c) ∈ moves (p (attachment opposite c))) :
    p ∈ highCandidates opposite := by
  have hanchor : ∀ (b : Bool) (c : Fin 6),
      attachment b c ∈ ([0, 1, 2, 3] : List (Fin 10)) := by decide
  obtain ⟨r, hr, hrp⟩ := high_membership opposite p full hcut hfirst hmove
    cycleVertices [0, 1, 2, 3] root hroot (fun c _ => hanchor opposite c)
  have hcover : ∀ k : Fin 10, k ∈ cycleVertices.map cycleIndex ++ [0, 1, 2, 3] := by decide
  have he : r = p := funext fun k => hrp k (hcover k)
  rw [he] at hr
  exact hr

private def separated (x y : Vertex) : Prop := x ≠ y ∧ adjacent x y = false

private theorem fill_middles_member (p : Placement) (f : Fin 10 × Fin 10 → Vertex)
    (es : List (Fin 10 × Fin 10)) (chosen : List Vertex)
    (hoptions : ∀ e ∈ es, f e ∈ middleOptions labels p e.1 e.2)
    (hpairs : (es.map f).Pairwise separated)
    (hchosen : ∀ x ∈ es.map f, ∀ y ∈ chosen, separated x y) :
    (es.map f).reverse ++ chosen ∈ fillMiddles p chosen es := by
  induction es generalizing chosen with
  | nil => simp [fillMiddles]
  | cons e es ih =>
    have hc : (chosen.any fun y => f e == y || adjacent (f e) y) = false := by
      apply List.any_eq_false.mpr
      intro y hy
      have ht := hchosen (f e) (by simp) y hy
      simp [ht.1, ht.2]
    have hpair := List.pairwise_cons.mp hpairs
    have ht : ∀ x ∈ es.map f, ∀ y ∈ f e :: chosen, separated x y := by
      intro x hx y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · have h := hpair.1 x hx
        refine ⟨h.1.symm, ?_⟩
        cases hxy : adjacent x (f e)
        · rfl
        · have ha := (adjacent_iff x (f e)).mp hxy
          exact (Bool.noConfusion (h.2.symm.trans ((adjacent_iff (f e) x).mpr ha.symm)))
      · exact hchosen x (List.mem_cons_of_mem _ hx) y hy
    have hm := ih (f e :: chosen) (fun a ha => hoptions a (List.mem_cons_of_mem _ ha))
      hpair.2 ht
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    apply List.mem_flatMap.mpr
    refine ⟨f e, hoptions e (List.mem_cons_self ..), ?_⟩
    simpa only [hc, Bool.false_eq_true, ite_false] using hm

/-- The full search contains the normalized high vertices and every allowed
choice of their distinct, pairwise nonadjacent degree-two subdivisions. -/
theorem candidate_of_normalized (opposite : Bool) (p : Placement)
    (hp : p ∈ highCandidates opposite) (f : Fin 10 × Fin 10 → Vertex)
    (hoptions : ∀ e ∈ hollowEdges opposite, f e ∈ middleOptions labels p e.1 e.2)
    (hpairs : ((hollowEdges opposite).map f).Pairwise separated) :
    ((hollowEdges opposite).map f).reverse ++ labels.map p ∈ candidates opposite := by
  unfold candidates
  apply List.mem_flatMap.mpr
  refine ⟨p, hp, List.mem_map.mpr ?_⟩
  refine ⟨((hollowEdges opposite).map f).reverse, ?_, rfl⟩
  simpa using fill_middles_member p f (hollowEdges opposite) [] hoptions hpairs (by simp)

/-- Every completed placement found by the search reconstructs a number of
opposite-half vertices different from fifty. -/
theorem candidate_size_ne_fifty {opposite : Bool} {half : List Vertex}
    (h : half ∈ candidates opposite) : reconstructionSize half ≠ 50 := by
  exact bne_iff_ne.mp (List.all_eq_true.mp (checked opposite) half h)

#print axioms high_candidate_of_normalized
#print axioms candidate_of_normalized
#print axioms candidate_size_ne_fifty

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonCoverage
