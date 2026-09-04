/- GID: D5/S3/Zeros/Symmetry/EdgeTranspositionGroup
   generality: G
   mirror-B: D5/B/S3/Zeros/Symmetry/EdgeTranspositionGroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Edge transpositions generate the full symmetric group on each connected component. -/

/- Library-search audit trail (2026-09-04):
   * D5 searches for graph edge transpositions, permutation closure, and connected-component
     generation found no equivalent declaration.
   * Pinned Mathlib provides `closure_of_isSwap_of_isPretransitive`, applied below after graph
     connectedness is converted into transitivity of the generated subgroup.
   * Searches of the installed non-Mathlib packages for graph transposition generation found no
     matching declaration.
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.GroupTheory.Perm.ClosureSwap

namespace D5.S3.Zeros.Symmetry.EdgeTranspositionGroup

open MulAction Set Subgroup

noncomputable section

private theorem connected_edge_transpositions_generate
    {V : Type*} [Finite V] (graph : SimpleGraph V)
    (connected : graph.Connected) :
    Subgroup.closure
        {sigma : Equiv.Perm V |
          exists first second,
            graph.Adj first second ∧
              sigma = @Equiv.swap V (Classical.decEq V) first second} =
      ⊤ := by
  classical
  let generators : Set (Equiv.Perm V) :=
    {sigma | exists first second,
      graph.Adj first second ∧
        sigma = @Equiv.swap V (Classical.decEq V) first second}
  have generatorsAreSwaps :
      ∀ sigma ∈ generators, sigma.IsSwap := by
    rintro sigma ⟨first, second, adjacent, rfl⟩
    exact ⟨first, second, adjacent.ne, rfl⟩
  let _ : MulAction.IsPretransitive (Subgroup.closure generators) V := by
    constructor
    intro first last
    have reachable : Relation.ReflTransGen graph.Adj first last :=
      (graph.reachable_iff_reflTransGen first last).mp
        (connected.preconnected first last)
    induction reachable with
    | refl =>
        exact ⟨1, by simp⟩
    | @tail middle last reachable adjacent ih =>
        rcases ih with ⟨sigma, hsigma⟩
        let edgeSwap : Subgroup.closure generators :=
          ⟨@Equiv.swap V (Classical.decEq V) middle last,
            Subgroup.subset_closure
              ⟨middle, last, adjacent, rfl⟩⟩
        refine ⟨edgeSwap * sigma, ?_⟩
        change (Equiv.swap middle last) ((sigma : Equiv.Perm V) first) = last
        change (sigma : Equiv.Perm V) first = middle at hsigma
        rw [hsigma, Equiv.swap_apply_left]
  exact closure_of_isSwap_of_isPretransitive generatorsAreSwaps

/-- Edge transpositions generate the full permutation group on each connected component. If the
whole graph is connected, they generate every vertex permutation and transport any vertex to any
other vertex. -/
theorem edge_transposition_group
    {V : Type*} [Finite V] (graph : SimpleGraph V) :
    (∀ component : graph.ConnectedComponent,
      Subgroup.closure
          {sigma : Equiv.Perm component |
            exists first second,
              component.toSimpleGraph.Adj first second ∧
                sigma = @Equiv.swap component (Classical.decEq component)
                  first second} =
        ⊤) ∧
      (graph.Connected ->
        let generated :=
          Subgroup.closure
            {sigma : Equiv.Perm V |
              exists first second,
                graph.Adj first second ∧
                  sigma = @Equiv.swap V (Classical.decEq V) first second}
        generated = ⊤ ∧
          ∀ first last,
            ∃ sigma : generated, (sigma : Equiv.Perm V) first = last) := by
  classical
  constructor
  · intro component
    exact connected_edge_transpositions_generate component.toSimpleGraph
      component.connected_toSimpleGraph
  · intro connected
    let generated :=
      Subgroup.closure
        {sigma : Equiv.Perm V |
          exists first second,
            graph.Adj first second ∧
              sigma = @Equiv.swap V (Classical.decEq V) first second}
    have generatedTop : generated = ⊤ :=
      connected_edge_transpositions_generate graph connected
    refine ⟨generatedTop, ?_⟩
    intro first last
    let sigma : Equiv.Perm V :=
      @Equiv.swap V (Classical.decEq V) first last
    have sigmaMem : sigma ∈ generated := by
      rw [generatedTop]
      exact Subgroup.mem_top sigma
    refine ⟨⟨sigma, sigmaMem⟩, ?_⟩
    exact Equiv.swap_apply_left first last

#print axioms edge_transposition_group

end

end D5.S3.Zeros.Symmetry.EdgeTranspositionGroup
