/- GID: D5/S3/Combinatorics/Graph/CycleSpaceEulerRank
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/CycleSpaceEulerRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The binary graph cycle space is the first Betti space with Euler rank m-n+c. -/

import D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.CycleSpaceEulerRank

open SimpleGraph
open D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace
open D5.S3.Fourier.CharacterSelection.BinaryCharacterCodeDuality

/-- The mod-two boundary map of the graph chain model.  An edge labeling is
sent to the linear functional obtained by summing its endpoint characters.
Over ZMod 2 this is the usual unoriented graph boundary, expressed through
the standard coordinate pairing. -/
noncomputable def graphBoundary {V : Type*} (G : SimpleGraph V) :
    (G.edgeSet → ZMod 2) →ₗ[ZMod 2] Module.Dual (ZMod 2) (V → ZMod 2) :=
  Fintype.linearCombination (ZMod 2) (endpointCharacters G)

/-- First homology in the finite binary graph chain model. -/
noncomputable def graphFirstHomology {V : Type*} [Fintype G.edgeSet]
    (G : SimpleGraph V) : Submodule (ZMod 2) (G.edgeSet → ZMod 2) :=
  LinearMap.ker (graphBoundary G)

/-- The cycle-space carrier is exactly the kernel of the graph boundary. -/
theorem graphFirstHomology_eq_simpleCycleSpace
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    [MeasurableSpace (ZMod 2)] [MeasurableSingletonClass (ZMod 2)] :
    graphFirstHomology G = simpleCycleSpace G := by
  have h := finite_graph_cycle_space G
  have hspace := h.1
  simpa [graphFirstHomology, graphBoundary, characterRelationSpace] using hspace.symm

/-- The first Betti rank of the finite binary graph chain model. -/
def graphBettiOne {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Nat :=
  Module.finrank (ZMod 2) (graphFirstHomology G)

/-- The Euler cycle rank |E| - |V| + c, written with natural subtraction
after the forest inequality. -/
def eulerCycleRank {V : Type*} (G : SimpleGraph V)
    [Fintype V] [Fintype G.edgeSet] [Fintype G.ConnectedComponent] : Nat :=
  Fintype.card G.edgeSet + Fintype.card G.ConnectedComponent - Fintype.card V

/-- The finite binary graph chain model has Euler first-Betti rank m - n + c.
The proof projects the existing simple-cycle/fundamental-cycle basis theorem. -/
theorem graphBettiOne_eq_eulerCycleRank
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    [MeasurableSpace (ZMod 2)] [MeasurableSingletonClass (ZMod 2)] :
    graphBettiOne G = eulerCycleRank G := by
  rw [graphBettiOne, graphFirstHomology_eq_simpleCycleSpace G]
  have h := finite_graph_cycle_space G
  rcases h with ⟨_, _, _, _, hforest, hrest⟩
  obtain ⟨T, hTG, hacyc, hreach⟩ := hforest
  have hdata := hrest T hTG hacyc hreach
  obtain ⟨cycles, _, _, _, basis, _, _, _, _, hcard, _, _, hfinrank, _⟩ := hdata
  calc
    Module.finrank (ZMod 2) (simpleCycleSpace G) =
        Nat.card {e : G.edgeSet // e.val ∉ T.edgeSet} := by
      simpa using hfinrank
    _ = eulerCycleRank G := by
      simpa [eulerCycleRank] using hcard

#print axioms graphFirstHomology_eq_simpleCycleSpace
#print axioms graphBettiOne_eq_eulerCycleRank

end D5.S3.Combinatorics.Graph.CycleSpaceEulerRank
