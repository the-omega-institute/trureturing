/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DegreeFourWitness
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DegreeFourWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: An explicit 260-vertex induced subgraph of Q9 of maximum degree at most four. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9OrbitCertificateProbe

/-! Take both ninth-coordinate lifts of the parity-selected eight-cube set from
Hong–Wu–Xia, arXiv:2610.09483v1, Proposition 6.2. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9DegreeFourWitness

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip)
open BalancedCubeComponentBoundary (directions)
open private mem_directions directions_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private selected_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation

private def f5 (x : BitVec 5) : Bool :=
  decide (x.cpop.toNat ≤ 2) || (x == 19) || (x == 13) || (x == 14) || (x == 28)

private def selected (x : BitVec 9) : Bool :=
  let parity := (x.extractLsb' 0 8).cpop.getLsbD 0
  let f8 := f5 (x.extractLsb' 0 5) && (x.extractLsb' 5 3 != 0)
  parity == f8

private def selectedCodes : Finset (Fin 512) :=
  Finset.univ.filter fun x => selected (BitVec.ofFin x) = true

private def codeToVertex : Fin 512 ↪ Q 9 :=
  ⟨fun x => cubeBitVec 9 (BitVec.ofFin x),
    fun _ _ h => congrArg BitVec.toFin ((cubeBitVec 9).injective h)⟩

private def witness : Finset (Q 9) := selectedCodes.map codeToVertex

private theorem mem_witness (x : BitVec 9) :
    cubeBitVec 9 x ∈ witness ↔ selected x = true := by
  change codeToVertex x.toFin ∈ witness ↔ _
  simp [witness, selectedCodes, Finset.mem_map']

private def toggle (x : BitVec 9) (i : Fin 9) : BitVec 9 :=
  x ^^^ BitVec.ofNat 9 (2 ^ i.val)

private def selectedDirections (x : BitVec 9) : Finset (Fin 9) :=
  Finset.univ.filter fun i => selected (toggle x i) = true

set_option maxRecDepth 4096 in
private theorem selectedCodes_card : selectedCodes.card = 260 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- Kernel reduction enumerates the vertices and checks the nine coordinate flips.
private theorem selectedDirections_card_le : ∀ x : Fin 512,
    selected (BitVec.ofFin x) = true → (selectedDirections (BitVec.ofFin x)).card ≤ 4 := by
  decide +kernel

private theorem directions_eq (x : BitVec 9) :
    directions witness (cubeBitVec 9 x) = selectedDirections x := by
  ext i
  rw [mem_directions, ← show cubeBitVec 9 (toggle x i) = flip (cubeBitVec 9 x) i
    from cubeBitVec_xor_single x i, mem_witness]
  simp [selectedDirections]

open Classical in
/-- The nine-cube contains an induced subgraph on 260 vertices of maximum degree at most four. -/
theorem exists_card_260_maxDegree_le_four :
    ∃ U : Finset (Q 9), U.card = 260 ∧ ((hypercube 9).induce (U : Set (Q 9))).maxDegree ≤ 4 := by
  refine ⟨witness, (Finset.card_map _).trans selectedCodes_card, ?_⟩
  apply SimpleGraph.maxDegree_le_of_forall_degree_le
  rintro ⟨v, hv⟩
  obtain ⟨x, rfl⟩ := (cubeBitVec 9).surjective v
  have hfilter :
      (hypercube 9).neighborFinset (cubeBitVec 9 x) ∩ witness =
        witness.filter (fun y => (hypercube 9).Adj (cubeBitVec 9 x) y) := by
    ext y
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  rw [← selected_neighbor_card hv, hfilter, ← directions_card, directions_eq]
  exact selectedDirections_card_le x.toFin ((mem_witness x).mp hv)

#print axioms selectedCodes_card
#print axioms selectedDirections_card_le
#print axioms exists_card_260_maxDegree_le_four

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9DegreeFourWitness
