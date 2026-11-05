/- GID: D5/S3/Combinatorics/Graph/Walks/CycleDetour
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/CycleDetour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hamiltonian]
   utility: none
   digest: An external path and adjacent cycle successors produce an actual longer cycle. -/
import D5.S3.Combinatorics.Graph.Walks.OrderedTwoCutSlicing
import D5.S3.Combinatorics.Graph.Walks.PathRingSplicing

/-
The detour argument follows Juan Pablo Traverso Gianini's
MengerHamilton/LongerCycle.lean in jtraverso/menger-hamiltonian at
35c5f684f9bfbd244bd0999ce725623ab571adb6, licensed under Apache 2.0 in
docs/reports/licenses/menger-hamiltonian-LICENSE.txt.
The construction uses native walks, the original ordered path cutter and
the original path-ring splicer on the induced union-of-supports graph.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Combinatorics.Graph.Walks.CycleDetour

open SimpleGraph EdgeSlicing PathRingSplicing OrderedTwoCutSlicing

universe u
variable {V : Type u} {G : SimpleGraph V}

theorem exists_cycle_through_detour {base successor : V}
    (closing : G.Adj base successor) (path : G.Walk successor base)
    (hcycle : (path.cons closing).IsCycle) (index : ℕ) (hindex : index < path.length)
    (detour : G.Walk base (path.getVert index)) (hdetour : detour.IsPath)
    (hdetourLength : 2 ≤ detour.length)
    (hclean : ∀ vertex ∈ detour.support, vertex ∈ (path.cons closing).support →
      vertex = base ∨ vertex = path.getVert index)
    (hconnect : G.Adj successor (path.getVert (index + 1))) :
    ∃ extended : G.Walk (path.getVert index) (path.getVert index),
      extended.IsCycle ∧ extended.length = (path.cons closing).length + detour.length - 1 ∧
      ∀ vertex, vertex ∈ extended.support ↔
        vertex ∈ (path.cons closing).support ∨ vertex ∈ detour.support := by
  classical
  have hpath : path.IsPath := (Walk.cons_isCycle_iff path closing).mp hcycle |>.1
  have hpathLength : 2 ≤ path.length := by
    have := hcycle.three_le_length
    simp only [Walk.length_cons] at this
    omega
  obtain ⟨leftEnd, interior, rightEnd, _, hinterior, _, hdetourSupport, _, _,
      hleftLength, hinteriorLength, hrightLength⟩ :=
    exists_path_slicing_at_two_ordered_edges detour hdetour
      (ℓ₀ := base) (r₁ := path.getVert index)
      (i := 0) (j := detour.length - 1) (by omega) (by omega)
      detour.getVert_zero rfl rfl (by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ detour.length)]
        exact detour.getVert_length)
  have hleft : leftEnd = Walk.nil := (Walk.length_eq_zero_iff.mp hleftLength).eq_nil
  have hright : rightEnd = Walk.nil :=
    (Walk.length_eq_zero_iff.mp (by omega : rightEnd.length = 0)).eq_nil
  rw [hleft, hright, Walk.support_nil, Walk.support_nil] at hdetourSupport
  have hdetourNodup : (base :: (interior.support ++ [path.getVert index])).Nodup := by
    have hnodup := hdetour.support_nodup
    rw [← hdetourSupport] at hnodup
    simpa only [List.singleton_append, List.cons_append, List.nil_append] using hnodup
  have hbaseInterior : base ∉ interior.support := fun hmem =>
    (List.nodup_cons.mp hdetourNodup).1 (List.mem_append_left _ hmem)
  have hendInterior : path.getVert index ∉ interior.support := by
    intro hmem
    exact List.disjoint_left.mp (List.nodup_append'.mp (List.nodup_cons.mp hdetourNodup).2).2.2
      hmem (by simp)
  have hdisjoint : path.support.Disjoint interior.support := by
    apply List.disjoint_left.mpr
    intro vertex hpathMem hinteriorMem
    have hdetourMem : vertex ∈ detour.support := by
      rw [← hdetourSupport]
      simp [hinteriorMem]
    rcases hclean vertex hdetourMem (by simp [hpathMem]) with heq | heq
    · exact hbaseInterior (heq ▸ hinteriorMem)
    · exact hendInterior (heq ▸ hinteriorMem)
  let first := path.take index
  let second := path.drop (index + 1)
  have hpartition : first.support ++ second.support = path.support := by
    simp only [first, second, Walk.support_take, Walk.drop_support_eq_support_drop_min,
      Nat.min_eq_left (by omega : index + 1 ≤ path.length), List.take_append_drop]
  let inventory := first.reverse.support ++ second.support ++ interior.support
  have hperm : inventory.Perm (path.support ++ interior.support) := by
    dsimp [inventory]
    rw [Walk.support_reverse, ← hpartition]
    exact ((List.reverse_perm _).append_right _).append_right _
  have hnodup : inventory.Nodup := hperm.nodup_iff.mpr
    (List.nodup_append'.mpr ⟨hpath.support_nodup, hinterior.support_nodup, hdisjoint⟩)
  let carrier : Set V := {vertex | vertex ∈ inventory}
  letI : DecidableEq carrier := Classical.typeDecidableEq _
  letI : BEq carrier := instBEqOfDecidableEq
  have hfirst : ∀ vertex ∈ first.reverse.support, vertex ∈ carrier := by
    intro vertex hmem
    exact List.mem_append_left _ (List.mem_append_left _ hmem)
  have hsecond : ∀ vertex ∈ second.support, vertex ∈ carrier := by
    intro vertex hmem
    simp [carrier, inventory, hmem]
  have hinteriorCarrier : ∀ vertex ∈ interior.support, vertex ∈ carrier := by
    intro vertex hmem
    simp [carrier, inventory, hmem]
  let firstPiece : Piece (G.induce carrier) :=
    ⟨_, _, first.reverse.induce carrier hfirst⟩
  let secondPiece : Piece (G.induce carrier) :=
    ⟨_, _, second.induce carrier hsecond⟩
  let interiorPiece : Piece (G.induce carrier) :=
    ⟨_, _, interior.induce carrier hinteriorCarrier⟩
  let liftedInventory := [firstPiece, secondPiece, interiorPiece].flatMap
    (fun piece => piece.walk.support)
  have hmap : liftedInventory.map Subtype.val = inventory := by
    simp [liftedInventory, firstPiece, secondPiece, interiorPiece, Walk.support_induce,
      List.map_attachWith, inventory]
  have hliftedNodup : liftedInventory.Nodup :=
    List.Nodup.of_map Subtype.val (hmap.symm ▸ hnodup)
  have hfull : ∀ vertex : carrier, liftedInventory.count vertex = 1 := by
    intro vertex
    apply List.count_eq_one_of_mem hliftedNodup
    have hmem : vertex.val ∈ liftedInventory.map Subtype.val := hmap.symm ▸ vertex.property
    obtain ⟨other, hother, heq⟩ := List.mem_map.mp hmem
    have heq' : other = vertex := Subtype.ext heq
    exact heq' ▸ hother
  have hlengthInventory : inventory.length = path.length + detour.length := by
    have hlength := hperm.length_eq
    simp only [List.length_append, Walk.length_support] at hlength
    omega
  have hliftedLength : liftedInventory.length = inventory.length := by
    simpa only [List.length_map] using congrArg List.length hmap
  have hlink : Linked firstPiece [secondPiece, interiorPiece] := by
    refine ⟨?_, ?_, trivial⟩
    · exact hconnect
    · have hstart := detour.adj_getVert_succ (show 0 < detour.length by omega)
      change G.Adj base (detour.getVert (0 + 1))
      simpa only [Walk.getVert_zero, Nat.zero_add] using hstart
  have hclose : (G.induce carrier).Adj (finish firstPiece [secondPiece, interiorPiece])
      firstPiece.start := by
    have hend := detour.adj_getVert_succ (show detour.length - 1 < detour.length by omega)
    change G.Adj (detour.getVert (detour.length - 1)) (path.getVert index)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ detour.length), Walk.getVert_length] using hend
  obtain ⟨liftedCycle, hliftedCycle, hsupport, _⟩ :=
    exists_spliced_hamiltonian_cycle firstPiece [secondPiece, interiorPiece] hlink hclose hfull
      (by change 3 ≤ liftedInventory.length; rw [hliftedLength, hlengthInventory]; omega)
  dsimp only [firstPiece] at liftedCycle hliftedCycle hsupport
  let extended : G.Walk (path.getVert index) (path.getVert index) :=
    (liftedCycle.map (Embedding.induce carrier).toHom).copy rfl rfl
  refine ⟨extended, ?_, ?_, ?_⟩
  · simpa only [extended, Walk.isCycle_copy] using
      hliftedCycle.isCycle.map Subtype.val_injective
  · have hlength := congrArg List.length hsupport
    simp only [List.length_reverse, List.length_tail, Walk.length_support] at hlength
    change liftedCycle.length = _ at hlength
    rw [show extended.length = liftedCycle.length by simp only
      [extended, Walk.length_copy, Walk.length_map]]
    change liftedCycle.length = liftedInventory.length at hlength
    rw [hlength, hliftedLength, hlengthInventory, Walk.length_cons]
    omega
  · intro vertex
    have hmem : vertex ∈ extended.support ↔ vertex ∈ inventory := by
      simp only [extended, Walk.support_copy, Walk.support_map, List.mem_map]
      constructor
      · rintro ⟨liftedVertex, _, rfl⟩
        exact liftedVertex.property
      · intro hvertex
        exact ⟨⟨vertex, hvertex⟩, hliftedCycle.mem_support _, rfl⟩
    rw [hmem, hperm.mem_iff, List.mem_append]
    rw [← hdetourSupport]
    simp only [Walk.support_cons, List.mem_cons, List.mem_append, List.mem_singleton]
    have hbase : base ∈ path.support := path.end_mem_support
    have hend : path.getVert index ∈ path.support := path.getVert_mem_support index
    aesop

end D5.S3.Combinatorics.Graph.Walks.CycleDetour
