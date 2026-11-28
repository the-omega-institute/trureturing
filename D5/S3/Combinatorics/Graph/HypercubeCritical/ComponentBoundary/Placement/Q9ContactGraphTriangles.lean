import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9CubicContactCommonPartner

/-! The exterior parity obstruction as a structural law of the contact graph. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
namespace Q9ContactGraphTriangles

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9CubicContactCommonPartner (no_single_common_partner)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9SquareMaskGraph (activeAxes maskGraph)
open Q9WeightedSaturation (defect signedBiadjacency)
open private mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private pair_ne from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SquareMaskGraph
open private mem_axes from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.MinimumContactDisplacementCount

private theorem third_neighbor {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {i j d : V}
    (hij : G.Adj i j) (hid : G.Adj i d) (hjd : j ≠ d) (hi : G.degree i = 3) :
    ∃ a, G.Adj i a ∧ a ≠ j ∧ a ≠ d ∧ ∀ k, G.Adj i k → k = j ∨ k = a ∨ k = d := by
  let N := G.neighborFinset i
  let S := (N.erase j).erase d
  have hj : j ∈ N := (G.mem_neighborFinset _ _).mpr hij
  have hd : d ∈ N := (G.mem_neighborFinset _ _).mpr hid
  have hde : d ∈ N.erase j := mem_erase.mpr ⟨hjd.symm, hd⟩
  have hS : S.card = 1 := by
    rw [show S = (N.erase j).erase d from rfl, card_erase_of_mem hde, card_erase_of_mem hj]
    change (G.neighborFinset i).card - 1 - 1 = 1
    rw [G.card_neighborFinset_eq_degree, hi]
  obtain ⟨a, hS'⟩ := card_eq_one.mp hS
  have ha : a ∈ S := hS'.symm ▸ mem_singleton_self a
  obtain ⟨had, hae⟩ := mem_erase.mp ha
  obtain ⟨haj, haN⟩ := mem_erase.mp hae
  refine ⟨a, (G.mem_neighborFinset _ _).mp haN, haj, had, ?_⟩
  intro k hk
  by_cases hj' : k = j
  · exact Or.inl hj'
  by_cases hd' : k = d
  · exact Or.inr (Or.inr hd')
  have hkm : k ∈ S := mem_erase.mpr ⟨hd', mem_erase.mpr
    ⟨hj', (G.mem_neighborFinset _ _).mpr hk⟩⟩
  exact Or.inr (Or.inl (mem_singleton.mp (hS' ▸ hkm)))

open Classical in
/-- If two adjacent cubic contact coordinates share a neighbor, they share
a second one. This restricts triangles even when the third vertex has higher degree. -/
theorem cubic_edge_common_neighbor_has_companion
    {C D : Finset (Q 9)} {b : Bool}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0) :
    let F := minimumDisplacements C D b 2
    let G := maskGraph F
    ∀ {i j d}, G.Adj i j → G.degree i = 3 → G.degree j = 3 →
      G.Adj i d → G.Adj j d → ∃ e, e ≠ d ∧ G.Adj i e ∧ G.Adj j e := by
  let F := minimumDisplacements C D b 2
  let G := maskGraph F
  change ∀ {i j d : activeAxes F}, G.Adj i j → G.degree i = 3 → G.degree j = 3 →
    G.Adj i d → G.Adj j d → ∃ e, e ≠ d ∧ G.Adj i e ∧ G.Adj j e
  intro i j d hij hi hj hid hjd
  obtain ⟨a, hia, _, had, hI⟩ := third_neighbor G hij hid hjd.ne hi
  obtain ⟨c, hjc, hci, hcd, hJ⟩ := third_neighbor G hij.symm hjd hid.ne hj
  by_cases hac : c = a
  · exact ⟨a, had, hia, hac ▸ hjc⟩
  exfalso
  have hsize (T : Finset (Fin 9)) (hT : T ∈ F) : T.card = 2 := by
    obtain ⟨x, _, y, _, _, hd, rfl⟩ := mem_minimumDisplacements.mp hT
    exact hd
  have fromMask (u : activeAxes F) (k : Fin 9)
      (hk : ({u.val, k} : Finset (Fin 9)) ∈ F) :
      ∃ v : activeAxes F, v.val = k ∧ G.Adj u v := by
    let v : activeAxes F := ⟨k, mem_axes.mpr ⟨_, hk, by simp⟩⟩
    exact ⟨v, rfl, ⟨fun he => pair_ne hsize hk (congrArg Subtype.val he), hk⟩⟩
  have maskI (k : Fin 9) (hk : ({i.val, k} : Finset (Fin 9)) ∈ F) :
      k = j.val ∨ k = a.val ∨ k = d.val := by
    obtain ⟨v, rfl, hv⟩ := fromMask i k hk
    rcases hI v hv with rfl | rfl | rfl <;> simp
  have maskJ (k : Fin 9) (hk : ({j.val, k} : Finset (Fin 9)) ∈ F) :
      k = i.val ∨ k = c.val ∨ k = d.val := by
    obtain ⟨v, rfl, hv⟩ := fromMask j k hk
    rcases hJ v hv with rfl | rfl | rfl <;> simp
  exact no_single_common_partner (fun h => hij.ne (Subtype.ext h))
    (fun h => hci (Subtype.ext h).symm) (fun h => hac (Subtype.ext h))
    (fun h => hjc.ne (Subtype.ext h).symm) (fun h => had (Subtype.ext h))
    (fun h => hcd (Subtype.ext h)) hsep hrC hrD hcC hcD hbC hbD hdetC hdetD hij.2 maskI maskJ

#print axioms cubic_edge_common_neighbor_has_companion

end Q9ContactGraphTriangles
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
