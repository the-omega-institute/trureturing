/- GID: D5/S3/Fourier/CharacterSelection/EdgeConnectivityGradientWeight
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/EdgeConnectivityGradientWeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Edge connectivity is the minimum Hamming weight of a nonconstant binary edge gradient. -/

import D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace
import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
import Mathlib.InformationTheory.Hamming

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight

open SimpleGraph
open D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace

/-- A graph remains connected after deletion of fewer than `k` edges exactly when every
nonconstant binary vertex labeling has an edge gradient of Hamming weight at least `k`. -/
theorem edge_connected_iff_gradient_weight
    {V : Type*} (G : SimpleGraph V) [Fintype G.edgeSet] (k : Nat) :
    G.IsEdgeConnected k ↔
      ∀ x : V → ZMod 2,
        (∃ u v : V, x u ≠ x v) → k ≤ hammingNorm (edgeDifferential G x) := by
  classical
  constructor
  · intro hk x ⟨u, v, huv⟩
    by_contra hweight
    have hsmall : hammingNorm (edgeDifferential G x) < k := Nat.lt_of_not_ge hweight
    let bad : Finset G.edgeSet := Finset.univ.filter (fun e => edgeDifferential G x e ≠ 0)
    let removed : Finset (Sym2 V) := bad.image Subtype.val
    have hcard : removed.card = hammingNorm (edgeDifferential G x) := by
      simpa [removed, bad, hammingNorm] using
        (Finset.card_image_of_injective bad (fun _ _ h => Subtype.val_injective h))
    have hremoved : (removed : Set (Sym2 V)).encard < k := by
      simpa [Set.encard_coe_eq_coe_finsetCard, hcard] using hsmall
    have hadj {a b : V} (hab : (G.deleteEdges (removed : Set (Sym2 V))).Adj a b) :
        x a = x b := by
      obtain ⟨hG, hnot⟩ := deleteEdges_adj.mp hab
      have hzero : edgeDifferential G x ⟨s(a,b), hG⟩ = 0 := by
        by_contra hne
        apply hnot
        change s(a,b) ∈ removed
        simp only [removed, Finset.mem_image]
        exact ⟨⟨s(a,b), hG⟩, by simp [bad, hne], rfl⟩
      change x a + x b = 0 at hzero
      exact (add_eq_zero_iff_eq_neg.mp hzero).trans (ZMod.neg_eq_self_mod_two _)
    have hwalk {a b : V} (p : (G.deleteEdges (removed : Set (Sym2 V))).Walk a b) :
        x a = x b := by
      induction p with
      | nil => rfl
      | @cons a b c hab p ih => exact (hadj hab).trans ih
    exact huv (hwalk (hk u v hremoved).some)
  · intro hweight u v s hs
    by_contra hreach
    let H := G.deleteEdges s
    let x : V → ZMod 2 := fun w => if H.Reachable u w then 0 else 1
    have hnonconstant : ∃ a b : V, x a ≠ x b := by
      refine ⟨u, v, ?_⟩
      simp [x, H, hreach]
    let bad : Finset G.edgeSet := Finset.univ.filter (fun e => edgeDifferential G x e ≠ 0)
    let removed : Finset (Sym2 V) := bad.image Subtype.val
    have hcard : removed.card = hammingNorm (edgeDifferential G x) := by
      simpa [removed, bad, hammingNorm] using
        (Finset.card_image_of_injective bad (fun _ _ h => Subtype.val_injective h))
    have hsub : (removed : Set (Sym2 V)) ⊆ s := by
      intro e he
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp (show e ∈ removed from he)
      obtain ⟨e, heG⟩ := f
      induction e using Sym2.inductionOn with
      | hf a b =>
        by_contra hnot
        have hab : H.Adj a b := deleteEdges_adj.mpr ⟨heG, hnot⟩
        have hiff : H.Reachable u a ↔ H.Reachable u b :=
          ⟨fun ha => ha.trans hab.reachable, fun hb => hb.trans hab.symm.reachable⟩
        have hsame : x a = x b := by simp [x, hiff]
        have hzero : edgeDifferential G x ⟨s(a,b), heG⟩ = 0 := by
          change x a + x b = 0
          rw [hsame, ← two_mul]
          simp [show (2 : ZMod 2) = 0 by decide]
        exact (Finset.mem_filter.mp hf).2 hzero
    have hbound : (hammingNorm (edgeDifferential G x) : ℕ∞) ≤ s.encard := by
      rw [← hcard, ← Set.encard_coe_eq_coe_finsetCard]
      exact Set.encard_mono hsub
    have hweight' : (k : ℕ∞) ≤ (hammingNorm (edgeDifferential G x) : ℕ∞) := by
      exact_mod_cast hweight x hnonconstant
    have hlarge : (k : ℕ∞) ≤ s.encard := hweight'.trans hbound
    exact (not_lt_of_ge hlarge) hs

#print axioms edge_connected_iff_gradient_weight

end D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight
