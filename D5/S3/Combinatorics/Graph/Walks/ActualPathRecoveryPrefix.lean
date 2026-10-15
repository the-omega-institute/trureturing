/- GID: D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual retained inventories recover literal initial paths and restored crossing prefixes inside supplied simple boundary walks. -/
import D5.S3.Combinatorics.Graph.Walks.ActualPiecePrefix

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualPathRecoveryPrefix

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualPiecePrefix

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- A rooted actual walk whose edges are in a disjoint path partition
stays in the starting piece. Global retained inventory thus implies local
edge inclusion without taking component ownership as a premise. -/
theorem actual_partition_rooted_walk_edges
    (pieces : List (Piece G))
    (hn : (pieces.flatMap fun z => z.walk.support).Nodup)
    (p : Piece G) (hp : p ∈ pieces) {a b : V} (q : G.Walk a b)
    (ha : a ∈ p.walk.support)
    (hkeep : ∀ e ∈ q.edges, e ∈ pieces.flatMap (fun z => z.walk.edges)) :
    ∀ e ∈ q.edges, e ∈ p.walk.edges := by
  revert ha hkeep
  induction q with
  | nil =>
    intro _ _
    simp only [SimpleGraph.Walk.edges_nil, List.not_mem_nil, false_implies, implies_true]
  | @cons a x b h q ih =>
    intro ha hkeep
    have hhead : s(a, x) ∈ p.walk.edges :=
      actual_partition_incident_edge_owner pieces hn p hp ha
        (hkeep _ (by simp only [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_self))
    have hx : x ∈ p.walk.support := p.walk.snd_mem_support_of_mem_edges hhead
    have htail := ih hx (fun e he => hkeep e
      (by simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]; exact Or.inr he))
    intro e he
    simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact hhead
    · exact htail e he

/-- Sharing the start and retaining all actual edges of a simple path
forces it to be a literal front of another simple path. Undirected edge
inclusion cannot reverse an interior piece at the common starting point. -/
theorem actual_rooted_path_is_prefix {a b c : V}
    (q : G.Walk a b) (hq : q.IsPath) (p : G.Walk a c) (hp : p.IsPath)
    (hkeep : ∀ e ∈ q.edges, e ∈ p.edges) :
    ∃ tail : G.Walk b c, p = q.append tail ∧ tail.IsPath := by
  revert hq p
  induction q generalizing c with
  | nil =>
    intro _ p hp _
    exact ⟨p, by simp only [SimpleGraph.Walk.nil_append], hp⟩
  | @cons a x b h q ih =>
    intro hq p hp hkeep
    have hhead : s(a, x) ∈ p.edges := hkeep _
      (by simp only [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_self)
    have hx : x = p.snd := hp.eq_snd_of_mem_edges hhead
    cases p with
    | nil => simp only [SimpleGraph.Walk.edges_nil, List.not_mem_nil] at hhead
    | @cons a y c h' p =>
      have hxy : x = y := by simpa only [SimpleGraph.Walk.snd_cons] using hx
      clear hx
      subst y
      have hsub : ∀ e ∈ q.edges, e ∈ p.edges := by
        intro e he
        have hnot : e ≠ s(a, x) := by
          intro heq
          have haq : a ∈ q.support := q.fst_mem_support_of_mem_edges (heq ▸ he)
          exact ((SimpleGraph.Walk.cons_isPath_iff h q).mp hq).2 haq
        have hmem := hkeep e (by
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]; exact Or.inr he)
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hmem
        exact hmem.resolve_left hnot
      obtain ⟨tail, he, ht⟩ := ih hq.of_cons p hp.of_cons hsub
      refine ⟨tail, ?_, ht⟩
      rw [he]
      rfl

/-- Apply the previous joint path directly to the single-order actual
pieces obtained by restoring the other marks. Its retained global edges
earn the local ownership and hence its actual front position. -/
theorem actual_restored_partition_joint_prefix
    (pieces : List (Piece G))
    (hn : (pieces.flatMap fun z => z.walk.support).Nodup)
    (p : Piece G) (hp : p ∈ pieces) (hpath : p.walk.IsPath)
    {b : V} (q : G.Walk p.start b) (hq : q.IsPath)
    (hkeep : ∀ e ∈ q.edges, e ∈ pieces.flatMap (fun z => z.walk.edges)) :
    ∃ tail : G.Walk b p.finish, p.walk = q.append tail ∧ tail.IsPath := by
  have hlocal := actual_partition_rooted_walk_edges pieces hn p hp q
    p.walk.start_mem_support hkeep
  exact actual_rooted_path_is_prefix q hq p.walk hpath hlocal

/-- The primary boundary starts at the old distinguished joint piece.
Both exact inventories refer to the same cycle, so retaining that whole
joint piece and its literal initial position are earned together. -/
theorem actual_restored_initial_joint_prefix
    {base ℓ z y : V} (c : G.Walk base base)
    (d : G.Walk ℓ z) (jointrest : List (Piece G))
    (old : G.Walk ℓ y) (oldrest : List (Piece G))
    (hnjoint : ((⟨ℓ, z, d⟩ :: jointrest).flatMap
      fun p : Piece G => p.walk.support).Nodup)
    (hnold : ((⟨ℓ, y, old⟩ :: oldrest).flatMap
      fun p : Piece G => p.walk.support).Nodup)
    (K H : Finset (Sym2 V))
    (hjoint : ∀ e, e ∈ ((⟨ℓ, z, d⟩ :: jointrest).flatMap
      fun p : Piece G => p.walk.edges) ↔ e ∈ c.edges ∧ e ∉ K ∪ H)
    (hold : ∀ e, e ∈ ((⟨ℓ, y, old⟩ :: oldrest).flatMap
      fun p : Piece G => p.walk.edges) ↔ e ∈ c.edges ∧ e ∉ K) :
    d.support.Nodup ∧ (∀ e ∈ d.edges, e ∈ old.edges) ∧
      ∃ tail : G.Walk z y, old = d.append tail ∧ tail.IsPath := by
  have hnd : d.support.Nodup := by
    change (d.support ++ jointrest.flatMap fun p => p.walk.support).Nodup at hnjoint
    exact (List.nodup_append'.mp hnjoint).1
  have hkeep : ∀ e ∈ d.edges, e ∈ ((⟨ℓ, y, old⟩ :: oldrest).flatMap
      fun p : Piece G => p.walk.edges) := by
    intro e he
    have hj := (hjoint e).mp (List.mem_flatMap.mpr
      ⟨⟨ℓ, z, d⟩, List.mem_cons_self, he⟩)
    exact (hold e).mpr ⟨hj.1, fun hk => hj.2 (Finset.mem_union.mpr (Or.inl hk))⟩
  have hlocal := actual_partition_rooted_walk_edges (⟨ℓ, y, old⟩ :: oldrest)
    hnold ⟨ℓ, y, old⟩ List.mem_cons_self d old.start_mem_support hkeep
  have holdPath : old.IsPath := SimpleGraph.Walk.IsPath.mk' (by
    change (old.support ++ oldrest.flatMap fun p => p.walk.support).Nodup at hnold
    exact (List.nodup_append'.mp hnold).1)
  exact ⟨hnd, hlocal, actual_rooted_path_is_prefix d
    (SimpleGraph.Walk.IsPath.mk' hnd) old holdPath hlocal⟩

/-- The opposite-order rooted route is earned from two disjoint actual
joint pieces and one restored marked edge. Its simplicity follows from
the joint support partition. The same-cycle inventories put every route
edge in the actual single-order partition; ownership at its start then
forces it to be a front of that whole boundary path. No route-retention
or route-factorization certificate is an input. -/
theorem actual_restored_bridge_route_prefix
    {base ℓ z r x y : V} (c : G.Walk base base)
    (d : G.Walk ℓ z) (cross : G.Walk r x) (jointrest : List (Piece G))
    (old : G.Walk x y) (oldrest : List (Piece G))
    (hnjoint : ((⟨ℓ, z, d⟩ :: ⟨r, x, cross⟩ :: jointrest).flatMap
      fun p : Piece G => p.walk.support).Nodup)
    (hnold : ((⟨x, y, old⟩ :: oldrest).flatMap
      fun p : Piece G => p.walk.support).Nodup)
    (K H : Finset (Sym2 V)) (hdisjoint : Disjoint K H)
    (hjoint : ∀ e, e ∈ ((⟨ℓ, z, d⟩ :: ⟨r, x, cross⟩ :: jointrest).flatMap
      fun p : Piece G => p.walk.edges) ↔ e ∈ c.edges ∧ e ∉ K ∪ H)
    (hold : ∀ e, e ∈ ((⟨x, y, old⟩ :: oldrest).flatMap
      fun p : Piece G => p.walk.edges) ↔ e ∈ c.edges ∧ e ∉ K)
    (hcuts : ∀ e ∈ K ∪ H, e ∈ c.edges) (hseam : s(r, ℓ) ∈ H) :
    ∃ hrestore : G.Adj r ℓ,
      let front := cross.reverse.concat hrestore
      (front.append d).support.Nodup ∧
      (∀ e ∈ (front.append d).edges, e ∈ old.edges) ∧
      ∃ tail : G.Walk z y,
        old = front.append (d.append tail) ∧ tail.IsPath := by
  classical
  have hrestore : G.Adj r ℓ :=
    c.adj_of_mem_edges (hcuts _ (Finset.mem_union.mpr (Or.inr hseam)))
  let front := cross.reverse.concat hrestore
  let route := front.append d
  have hroute : route = cross.reverse.append (d.cons hrestore) :=
    SimpleGraph.Walk.concat_append cross.reverse hrestore d
  have hpair : (d.support ++ cross.support).Nodup := by
    simp only [List.flatMap_cons] at hnjoint
    have hn : ((d.support ++ cross.support) ++
        jointrest.flatMap fun p => p.walk.support).Nodup := by
      simpa only [List.append_assoc] using hnjoint
    exact (List.nodup_append'.mp hn).1
  have hsupport : route.support.Perm (d.support ++ cross.support) := by
    rw [hroute]
    apply List.perm_iff_count.mpr
    intro v
    simp only [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_reverse,
      SimpleGraph.Walk.support_cons, List.tail_cons, List.count_append, List.count_reverse]
    omega
  have hnroute : route.support.Nodup := hsupport.nodup_iff.mpr hpair
  have hseamNot : s(r, ℓ) ∉ K := fun he =>
    Finset.disjoint_left.mp hdisjoint he hseam
  have hkeep : ∀ e ∈ route.edges, e ∈ ((⟨x, y, old⟩ :: oldrest).flatMap
      fun p : Piece G => p.walk.edges) := by
    intro e he
    rw [hroute] at he
    simp only [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse,
      SimpleGraph.Walk.edges_cons, List.mem_append, List.mem_reverse, List.mem_cons] at he
    apply (hold e).mpr
    rcases he with he | (rfl | he)
    · have hj := (hjoint e).mp (by
        simp only [List.flatMap_cons]
        exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl he))))
      exact ⟨hj.1, fun hk => hj.2 (Finset.mem_union.mpr (Or.inl hk))⟩
    · exact ⟨hcuts _ (Finset.mem_union.mpr (Or.inr hseam)), hseamNot⟩
    · have hj := (hjoint e).mp (by
        simp only [List.flatMap_cons]
        exact List.mem_append.mpr (Or.inl he))
      exact ⟨hj.1, fun hk => hj.2 (Finset.mem_union.mpr (Or.inl hk))⟩
  have hlocal := actual_partition_rooted_walk_edges (⟨x, y, old⟩ :: oldrest)
    hnold ⟨x, y, old⟩ List.mem_cons_self route old.start_mem_support hkeep
  have holdPath : old.IsPath := SimpleGraph.Walk.IsPath.mk' (by
    change (old.support ++ oldrest.flatMap fun p => p.walk.support).Nodup at hnold
    exact (List.nodup_append'.mp hnold).1)
  obtain ⟨tail, hfactor, htail⟩ := actual_rooted_path_is_prefix route
    (SimpleGraph.Walk.IsPath.mk' hnroute) old holdPath hlocal
  refine ⟨hrestore, hnroute, hlocal, tail, ?_, htail⟩
  simpa only [route, SimpleGraph.Walk.append_assoc] using hfactor

/-- In particular, the oriented cut just before an old joint path's
finish occurs on the same forward single-order boundary path. Its actual
position is earned from the forced joint suffix and literal recovery. -/
theorem actual_restored_joint_cut_position
    (pieces : List (Piece G))
    (hn : (pieces.flatMap fun z => z.walk.support).Nodup)
    (p : Piece G) (hp : p ∈ pieces) (hpath : p.walk.IsPath)
    {b x y : V} (q : G.Walk p.start b) (hq : q.IsPath)
    (hkeep : ∀ e ∈ q.edges, e ∈ pieces.flatMap (fun z => z.walk.edges))
    (hbx : s(b, x) ∈ q.edges) (hxy : s(x, y) ∈ q.edges) (hyb : y ≠ b) :
    ∃ i : ℕ, i < p.walk.length ∧
      p.walk.getVert i = y ∧ p.walk.getVert (i + 1) = x := by
  obtain ⟨tail, hpref, _⟩ := actual_restored_partition_joint_prefix
    pieces hn p hp hpath q hq hkeep
  obtain ⟨i, hi, hy, hx⟩ := actual_retained_suffix_cut_position q hq hbx hxy hyb
  refine ⟨i, ?_, ?_, ?_⟩
  · rw [hpref, SimpleGraph.Walk.length_append]
    omega
  · rw [hpref, SimpleGraph.Walk.getVert_append', if_pos (by omega)]
    exact hy
  · rw [hpref, SimpleGraph.Walk.getVert_append', if_pos (by omega)]
    exact hx

#print axioms actual_partition_rooted_walk_edges
#print axioms actual_rooted_path_is_prefix
#print axioms actual_restored_partition_joint_prefix
#print axioms actual_restored_initial_joint_prefix
#print axioms actual_restored_bridge_route_prefix
#print axioms actual_restored_joint_cut_position

end D5.S3.Combinatorics.Graph.Walks.ActualPathRecoveryPrefix
