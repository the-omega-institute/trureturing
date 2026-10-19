/- GID: D5/S3/Geometry/Hyperideal/FaceSignaturePropagation
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/FaceSignaturePropagation
   mirror-E: none(waiver:combinatorial-face-transport)
   anchors: []
   utility: none
   digest: Face pairings preserve opposite-pair low counts along dual paths. -/

import D5.S3.Geometry.Hyperideal.FaceSignatureBalance
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Hyperideal.FaceSignaturePropagation

open D5.S3.Geometry.Hyperideal.FaceSignatureBalance

/-- The three actual edges of each face, in the local order (12,13,14,34,24,23). -/
def faceEdge : Fin 4 → Fin 3 → Fin 6 :=
  ![![3, 4, 5], ![1, 2, 3], ![0, 2, 4], ![0, 1, 5]]

/-- The number of low opposite-edge pairs in a balanced tetrahedron. -/
def lowPairCount {T E : Type*} (edge : T → Fin 6 → E) (low : E → Bool) (t : T) : ℕ :=
  (low (edge t 0)).toNat + (low (edge t 1)).toNat + (low (edge t 2)).toNat

/-- Opposite local edges receive the same global Boolean color. -/
def oppositeBalancedAt {T E : Type*} (edge : T → Fin 6 → E) (low : E → Bool)
    (t : T) : Prop :=
  low (edge t 0) = low (edge t 3) ∧
  low (edge t 1) = low (edge t 4) ∧
  low (edge t 2) = low (edge t 5)

/-- The dual edges whose two incident tetrahedra are both opposite-balanced. -/
def balancedGraph {T E : Type*} (G : SimpleGraph T)
    (edge : T → Fin 6 → E) (low : E → Bool) : SimpleGraph T where
  Adj s t := G.Adj s t ∧ oppositeBalancedAt edge low s ∧ oppositeBalancedAt edge low t
  symm := ⟨by
    intro s t h
    exact ⟨G.symm.symm s t h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨by
    intro s h
    exact G.loopless.irrefl s h.1⟩

/-- Every dual adjacency is a face pairing whose three actual global edge labels agree
    after a permutation. The tetrahedron and edge-label types may be infinite. -/
def faceGluingCompatible {T E : Type*} (G : SimpleGraph T) (edge : T → Fin 6 → E) : Prop :=
  ∀ {s t : T}, G.Adj s t →
    ∃ (i j : Fin 4) (p : Fin 3 ≃ Fin 3),
      ∀ n : Fin 3, edge s (faceEdge i n) = edge t (faceEdge j (p n))

/-- The low-pair count is constant along every dual path whose incident tetrahedra
    are opposite-balanced, even if other tetrahedra are unbalanced. -/
theorem lowPairCount_eq_of_reachable
    {T E : Type*} (G : SimpleGraph T) (edge : T → Fin 6 → E) (low : E → Bool)
    (glued : faceGluingCompatible G edge)
    {s t : T} (connected : (balancedGraph G edge low).Reachable s t) :
    lowPairCount edge low s = lowPairCount edge low t := by
  have face_sum (t : T) (i : Fin 4) :
      faceLowCount (fun e => low (edge t e)) i =
        ∑ n : Fin 3, (low (edge t (faceEdge i n))).toNat := by
    fin_cases i <;> simp [faceLowCount, faceEdge, Fin.sum_univ_three]
  have face_k (t : T) (ht : oppositeBalancedAt edge low t) (i : Fin 4) :
      faceLowCount (fun e => low (edge t e)) i = lowPairCount edge low t := by
    rcases ht with ⟨h03, h14, h25⟩
    fin_cases i <;>
      simp [faceLowCount, lowPairCount, h03, h14, h25,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have edge_k {a b : T} (adj : (balancedGraph G edge low).Adj a b) :
      lowPairCount edge low a = lowPairCount edge low b := by
    obtain ⟨hab, ha, hb⟩ := adj
    obtain ⟨i, j, p, hp⟩ := glued hab
    calc
      lowPairCount edge low a = faceLowCount (fun e => low (edge a e)) i :=
        (face_k a ha i).symm
      _ = ∑ n : Fin 3, (low (edge a (faceEdge i n))).toNat := face_sum a i
      _ = ∑ n : Fin 3, (low (edge b (faceEdge j (p n)))).toNat := by
        apply Finset.sum_congr rfl
        intro n _
        rw [hp n]
      _ = ∑ n : Fin 3, (low (edge b (faceEdge j n))).toNat := by
        exact Equiv.sum_comp p (fun n : Fin 3 => (low (edge b (faceEdge j n))).toNat)
      _ = faceLowCount (fun e => low (edge b e)) j := (face_sum b j).symm
      _ = lowPairCount edge low b := face_k b hb j
  rw [(balancedGraph G edge low).reachable_iff_reflTransGen] at connected
  induction connected with
  | refl => rfl
  | tail _ adj ih => exact ih.trans (edge_k adj)

#print axioms lowPairCount_eq_of_reachable

end D5.S3.Geometry.Hyperideal.FaceSignaturePropagation
