/- GID: D5/S3/Combinatorics/Graph/FiniteColoringCompactness
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/FiniteColoringCompactness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Compactness]
   utility: none
   digest: Finite-palette graph coloring is compact, with a sharp infinite-palette failure. -/

/- Library search audit: D5 has only the generic compact_local_realization engine.
   Pinned Mathlib has Rado selection and SimpleGraph coloring primitives, but no
   finite-induced-subgraph coloring compactness theorem. GitHub code searches for
   de Bruijn-Erdos and finite-subgraph Colorable statements found no exact Lean owner.

   proof_shape: finite_palette_coloring_compactness: content;
     infinite_palette_coloring_compactness_failure: content
   escape_witness: the active finite_palette_coloring_compactness proof reduces each
     finite family of adjacency constraints to the finite union of its endpoints,
     extends an induced-subgraph coloring to a total assignment, and proves every
     selected constraint proper before invoking compact_local_realization. The
     boundary theorem constructs all finite colorings and derives the global failure
     from Cantor's strict cardinal inequality.
   admission_basis: escape-witness -/

import D5.S3.Observer.Completion.CompactLocalRealization
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Topology.Constructions.SumProd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.FiniteColoringCompactness

open D5.S3.Observer.Completion.CompactLocalRealization

/-- A graph has a coloring by a fixed finite palette exactly when every finite
induced subgraph has one. The reverse direction sends a finite family of edge
constraints to the union of its endpoints before applying compactness. -/
theorem finite_palette_coloring_compactness
    {V : Type*} (G : SimpleGraph V) (k : Nat) :
    G.Colorable k ↔
      ∀ s : Finset V, (G.induce (s : Set V)).Colorable k := by
  classical
  constructor
  · rintro ⟨color⟩ s
    exact ⟨color.comap (SimpleGraph.Embedding.induce (G := G) (s : Set V)).toHom⟩
  · intro hlocal
    cases isEmpty_or_nonempty V with
    | inl hV =>
        let _ := hV
        exact SimpleGraph.Colorable.of_isEmpty k
    | inr hV =>
        let _ := hV
        let v0 : V := Classical.choice hV
        obtain ⟨singletonColoring⟩ := hlocal {v0}
        let _ : Nonempty (Fin k) :=
          ⟨singletonColoring ⟨v0, by simp⟩⟩
        let Context := {p : V × V // G.Adj p.1 p.2}
        let beta : Context → (V → Fin k) → Bool := fun constraint color =>
          decide (color constraint.1.1 ≠ color constraint.1.2)
        let target : Context → Bool := fun _ => true
        obtain ⟨color, hcolor⟩ := compact_local_realization beta target (by
          intro constraint
          change IsClosed ((fun color : V → Fin k =>
            decide (color constraint.1.1 ≠ color constraint.1.2)) ⁻¹' ({true} : Set Bool))
          apply (isClosed_discrete _).preimage
          have hpair : Continuous (fun color : V → Fin k =>
              (color constraint.1.1, color constraint.1.2)) :=
            (continuous_apply constraint.1.1).prodMk
              (continuous_apply constraint.1.2)
          have hproper : Continuous (fun pair : Fin k × Fin k =>
              decide (pair.1 ≠ pair.2)) := continuous_of_discreteTopology
          exact hproper.comp hpair) (by
          intro constraints
          let endpoints : Finset V := constraints.biUnion fun constraint =>
            {constraint.1.1, constraint.1.2}
          obtain ⟨localColoring⟩ := hlocal endpoints
          let extended : V → Fin k := fun vertex =>
            if hvertex : vertex ∈ endpoints then localColoring ⟨vertex, hvertex⟩
            else Classical.arbitrary (Fin k)
          refine ⟨extended, ?_⟩
          intro constraint hconstraint
          have hleft : constraint.1.1 ∈ endpoints := by
            apply Finset.mem_biUnion.mpr
            exact ⟨constraint, hconstraint, by simp⟩
          have hright : constraint.1.2 ∈ endpoints := by
            apply Finset.mem_biUnion.mpr
            exact ⟨constraint, hconstraint, by simp⟩
          have hadj : (G.induce (endpoints : Set V)).Adj
              ⟨constraint.1.1, hleft⟩ ⟨constraint.1.2, hright⟩ :=
            constraint.2
          have hne := localColoring.valid hadj
          simp [beta, target, extended, hleft, hright, hne])
        refine ⟨SimpleGraph.Coloring.mk color ?_⟩
        intro u v huv
        have h := hcolor ⟨(u, v), huv⟩
        simpa [beta, target] using h

/-- The finite-palette hypothesis is sharp. The complete graph on the uncountable
carrier `Set Nat` has a coloring by `Nat` on every finite induced subgraph, but
no global coloring by `Nat`. -/
theorem infinite_palette_coloring_compactness_failure :
    (∀ s : Finset (Set Nat),
      Nonempty (((SimpleGraph.completeGraph (Set Nat)).induce
        (s : Set (Set Nat))).Coloring Nat)) ∧
    ¬ Nonempty ((SimpleGraph.completeGraph (Set Nat)).Coloring Nat) := by
  constructor
  · intro s
    let color : s → Nat := fun x => (s.equivFin x).val
    refine ⟨SimpleGraph.Coloring.mk color ?_⟩
    intro u v huv
    exact fun h => huv (congrArg Subtype.val (s.equivFin.injective (Fin.ext h)))
  · rintro ⟨color⟩
    have hinjective : Function.Injective color := by
      intro u v hcolor
      by_contra huv
      exact color.valid huv hcolor
    have hle : Cardinal.mk (Set Nat) ≤ Cardinal.mk Nat :=
      Cardinal.mk_le_of_injective hinjective
    have hlt : Cardinal.mk Nat < Cardinal.mk (Set Nat) := by
      simpa only [Cardinal.mk_set] using Cardinal.cantor (Cardinal.mk Nat)
    exact (not_le_of_gt hlt) hle

#print axioms finite_palette_coloring_compactness
#print axioms infinite_palette_coloring_compactness_failure

end D5.S3.Combinatorics.Graph.FiniteColoringCompactness
