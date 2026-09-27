/- GID: D5/S3/Fourier/CharacterSelection/EdgeConnectivityDecoding
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/EdgeConnectivityDecoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Edge connectivity gives unique binary gradient recovery below half the cut size. -/

import D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace
import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CharacterSelection.EdgeConnectivityDecoding

open SimpleGraph
open D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace

/-- A binary edge gradient is the unique gradient within `t` arbitrary edge errors
when the graph remains connected after fewer than `k` edges are deleted. -/
theorem edge_gradient_unique_recovery
    {V : Type*}
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (k t : Nat) (hk : G.IsEdgeConnected k) (ht : 2 * t < k)
    (x : V → ZMod 2) (received : G.edgeSet → ZMod 2)
    (hnoise : hammingDist received (edgeDifferential G x) ≤ t) :
    ∃! c : G.edgeSet → ZMod 2,
      c ∈ Set.range (edgeDifferential G) ∧ hammingDist received c ≤ t := by
  classical
  have separate (x y : V → ZMod 2)
      (hsmall : hammingDist (edgeDifferential G x) (edgeDifferential G y) < k) :
      edgeDifferential G x = edgeDifferential G y := by
    let bad : Finset G.edgeSet := Finset.univ.filter
      (fun e => edgeDifferential G x e ≠ edgeDifferential G y e)
    let removed : Finset (Sym2 V) := bad.image Subtype.val
    have hcard : removed.card = hammingDist (edgeDifferential G x) (edgeDifferential G y) := by
      simpa [removed, bad, hammingDist] using
        (Finset.card_image_of_injective bad (fun _ _ h => Subtype.val_injective h))
    have hremoved : (removed : Set (Sym2 V)).encard < k := by
      simpa [Set.encard_coe_eq_coe_finsetCard, hcard] using hsmall
    have hadj {a b : V} (hab : (G.deleteEdges (removed : Set (Sym2 V))).Adj a b) :
        x a + y a = x b + y b := by
      obtain ⟨hG, hnot⟩ := deleteEdges_adj.mp hab
      have hsame : edgeDifferential G x ⟨s(a,b), hG⟩ =
          edgeDifferential G y ⟨s(a,b), hG⟩ := by
        by_contra hdiff
        apply hnot
        change s(a,b) ∈ removed
        simp only [removed, Finset.mem_image]
        exact ⟨⟨s(a,b), hG⟩, by simp [bad, hdiff], rfl⟩
      change x a + x b = y a + y b at hsame
      linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) hsame
    have hwalk {a b : V} (p : (G.deleteEdges (removed : Set (Sym2 V))).Walk a b) :
        x a + y a = x b + y b := by
      induction p with
      | nil => rfl
      | @cons a b c hab p ih => exact (hadj hab).trans ih
    funext e
    obtain ⟨e, he⟩ := e
    induction e using Sym2.inductionOn with
    | hf a b =>
      have hreach : (G.deleteEdges (removed : Set (Sym2 V))).Reachable a b :=
        hk a b hremoved
      have hpot := hwalk hreach.some
      change x a + x b = y a + y b
      linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) hpot
  refine ⟨edgeDifferential G x, ⟨⟨x, rfl⟩, hnoise⟩, ?_⟩
  intro c hc
  obtain ⟨y, rfl⟩ := hc.1
  have hdistance : hammingDist (edgeDifferential G x) (edgeDifferential G y) < k := calc
    hammingDist (edgeDifferential G x) (edgeDifferential G y) ≤
        hammingDist received (edgeDifferential G x) +
          hammingDist received (edgeDifferential G y) :=
      hammingDist_triangle_left _ _ received
    _ ≤ t + t := Nat.add_le_add hnoise hc.2
    _ < k := by omega
  exact (separate x y hdistance).symm

#print axioms edge_gradient_unique_recovery

end D5.S3.Fourier.CharacterSelection.EdgeConnectivityDecoding
