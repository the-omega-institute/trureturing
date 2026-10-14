/- UNCOMPILED snippet in the NativeJ2SurvivingEdges namespace after
   actual_six_cut_slicing_with_endpoints. Import Mathlib.Data.List.Nodup.
   Every support and edge equality below comes from map/transfer of actual
   slices. No symbolic component partition is assumed. -/

private theorem actual_surviving_path_partition {m : ℕ} (hm : 5 ≤ m) :
    ∃ pieces : List (D5.S3.Combinatorics.Graph.Walks.EdgeSlicing.Piece
        (survivingGraph m)),
      (∀ z ∈ pieces, z.walk.IsPath) ∧
      (pieces.flatMap fun z => z.walk.support).Nodup ∧
      (∀ x, x ∈ (pieces.flatMap fun z => z.walk.support) ↔ F2Domain m x) ∧
      (∀ e, e ∈ (pieces.flatMap fun z => z.walk.edges) ↔ SurvivingEdge m e) ∧
      pieces.length = 6 ∧
      ∀ z ∈ pieces,
        (∃ q : Fin 3 × Bool × Bool, z.start = port m q) ∧
        (∃ q : Fin 3 × Bool × Bool, z.finish = port m q) := by
  classical
  obtain ⟨pieces, hpath, hcount, hinventory, hlength, hendpoints⟩ :=
    actual_six_cut_slicing_with_endpoints hm
  let f : domainGraph (F2Domain m) →g
      SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m)) :=
    ⟨Subtype.val, fun h => h⟩
  have htransfer (z : {z // z ∈ pieces}) :
      ∀ e, e ∈ (z.val.walk.map f).edges → e ∈ (survivingGraph m).edgeSet := by
    intro e he
    have hmem : e ∈ (pieces.flatMap fun z => z.walk.edges).map
        (Sym2.map Subtype.val) := by
      rw [SimpleGraph.Walk.edges_map] at he
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he
      exact List.mem_map.mpr ⟨e, List.mem_flatMap.mpr ⟨z.val, z.property, he⟩, rfl⟩
    have hs := (hinventory e).mp hmem
    obtain ⟨⟨x, y⟩, rfl⟩ := Sym2.mk_surjective e
    change (survivingGraph m).Adj x y
    exact (surviving_adj_iff m x y).mpr
      ⟨hs, ((z.val.walk.map f).adj_of_mem_edges he).ne⟩
  let lift : {z // z ∈ pieces} →
      D5.S3.Combinatorics.Graph.Walks.EdgeSlicing.Piece (survivingGraph m) := fun z =>
    ⟨z.val.start.val, z.val.finish.val,
      (z.val.walk.map f).transfer (survivingGraph m) (htransfer z)⟩
  let lifted := pieces.attach.map lift
  have hs : (lifted.flatMap fun z => z.walk.support) =
      (pieces.flatMap fun z => z.walk.support).map Subtype.val := by
    calc
      _ = pieces.attach.flatMap (fun z => z.val.walk.support.map Subtype.val) := by
        simp only [lifted, List.flatMap_map, lift, SimpleGraph.Walk.support_transfer,
          SimpleGraph.Walk.support_map]
      _ = (pieces.attach.flatMap fun z => z.val.walk.support).map Subtype.val := by
        rw [List.map_flatMap]
      _ = _ := by rw [← List.flatMap_map, List.attach_map_subtype_val]
  have he : (lifted.flatMap fun z => z.walk.edges) =
      (pieces.flatMap fun z => z.walk.edges).map (Sym2.map Subtype.val) := by
    calc
      _ = pieces.attach.flatMap (fun z => z.val.walk.edges.map (Sym2.map Subtype.val)) := by
        simp only [lifted, List.flatMap_map, lift, SimpleGraph.Walk.edges_transfer,
          SimpleGraph.Walk.edges_map]
      _ = (pieces.attach.flatMap fun z => z.val.walk.edges).map (Sym2.map Subtype.val) := by
        rw [List.map_flatMap]
      _ = _ := by rw [← List.flatMap_map, List.attach_map_subtype_val]
  have hn : (pieces.flatMap fun z => z.walk.support).Nodup :=
    List.nodup_iff_count_le_one.mpr (fun x => by rw [hcount x])
  refine ⟨lifted, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hz
    apply SimpleGraph.Walk.IsPath.mk'
    simpa only [lift, SimpleGraph.Walk.support_transfer, SimpleGraph.Walk.support_map] using
      (hpath z.val z.property).support_nodup.map Subtype.val_injective
  · rw [hs]
    exact hn.map Subtype.val_injective
  · intro x
    rw [hs]
    constructor
    · intro hx
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
      exact v.property
    · intro hx
      let v : {x : Configuration m // F2Domain m x} := ⟨x, hx⟩
      have hv : v ∈ (pieces.flatMap fun z => z.walk.support) := by
        exact List.count_pos_iff.mp (by rw [hcount v]; omega)
      exact List.mem_map.mpr ⟨v, hv, rfl⟩
  · intro e
    rw [he]
    exact hinventory e
  · simpa only [lifted, List.length_map, List.length_attach] using hlength
  · intro z hz
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hz
    exact hendpoints z.val z.property

#print axioms actual_surviving_path_partition
