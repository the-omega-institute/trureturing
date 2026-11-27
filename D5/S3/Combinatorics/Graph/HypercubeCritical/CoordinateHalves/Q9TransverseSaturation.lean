/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TransverseSaturation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TransverseSaturation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Transverse incidence saturates minority edge classes and exceeds cubic degree. -/

import Archive.Sensitivity
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import Batteries.Tactic.OpenPrivate

/-! The terminal counting argument for the separated 120+138 branch of Hong, Wu and
Xia's Problem 2 (arXiv:2610.09483v1, Section 7). The cross-incidence hypothesis
is the input supplied by the double-cover classification. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TransverseSaturation

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip)
open BalancedCubeComponentBoundary (directions mem_directions regular_directions)
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum

open Classical in
/-- Actual `j`-edges tagged by the Boolean weight parity of their unique false endpoint. -/
noncomputable def parityEdgeTails (C : Finset (Q 9)) (j : Fin 9) (p : Bool) : Finset (Q 9) :=
  C.filter fun x => x j = false ∧ flip x j ∈ C ∧ cubeParity x = p

open Classical in
/-- Four transverse incidences from each size-four axis force every minority edge
to meet all eight other axes, exceeding the two spare directions at each endpoint. -/
theorem no_cubic_minority_transverse_saturation (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (minority : Fin 9 → Bool)
    (hquota : ∀ j, (parityEdgeTails C j (minority j)).card = 1 ∨
      (parityEdgeTails C j (minority j)).card = 4)
    (hseed : ∃ i, (parityEdgeTails C i (minority i)).card = 4)
    (hcross : ∀ i j : Fin 9, i ≠ j → (parityEdgeTails C i (minority i)).card = 4 →
      4 ≤ ((parityEdgeTails C j (minority j)).filter fun x =>
        i ∈ directions C x ∨ i ∈ directions C (flip x j)).card) : False := by
  let tails (j : Fin 9) := parityEdgeTails C j (minority j)
  let touching (i j : Fin 9) := (tails j).filter fun x =>
    i ∈ directions C x ∨ i ∈ directions C (flip x j)
  change ∀ j, (tails j).card = 1 ∨ (tails j).card = 4 at hquota
  change ∃ i, (tails i).card = 4 at hseed
  change ∀ i j, i ≠ j → (tails i).card = 4 → 4 ≤ (touching i j).card at hcross
  have hsub (i j : Fin 9) : touching i j ⊆ tails j := Finset.filter_subset _ _
  obtain ⟨j, hj⟩ := hseed
  have hfour (k : Fin 9) : (tails k).card = 4 := by
    by_cases hjk : j = k
    · simpa only [← hjk] using hj
    · have hle := (hcross j k hjk hj).trans (Finset.card_le_card (hsub j k))
      rcases hquota k with hone | hfour
      · omega
      · exact hfour
  have hsaturated {i k : Fin 9} (hik : i ≠ k) : touching i k = tails k := by
    apply Finset.eq_of_subset_of_card_le (hsub i k)
    rw [hfour k]
    exact hcross i k hik (hfour i)
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (tails j).card by rw [hj]; decide)
  have hx' : x ∈ C ∧ x j = false ∧ flip x j ∈ C ∧ cubeParity x = minority j := by
    simpa only [tails, parityEdgeTails, Finset.mem_filter] using hx
  let y := flip x j
  have hy : y ∈ C := hx'.2.2.1
  have hjx : j ∈ directions C x := (mem_directions C x j).mpr hy
  have hjy : j ∈ directions C y := (mem_directions C y j).mpr (by
    simpa only [y, BalancedCriticalSpectrum.flip_flip] using hx'.1)
  have hall : (Finset.univ : Finset (Fin 9)).erase j ⊆
      (directions C x).erase j ∪ (directions C y).erase j := by
    intro i hi
    have hij := (Finset.mem_erase.mp hi).1
    have htouch : x ∈ touching i j := (hsaturated hij).symm ▸ hx
    rcases (Finset.mem_filter.mp htouch).2 with hix | hiy
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨hij, hix⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_erase.mpr ⟨hij, hiy⟩))
  have hbound := (Finset.card_le_card hall).trans (Finset.card_union_le _ _)
  rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
    Finset.card_erase_of_mem hjx, Finset.card_erase_of_mem hjy,
    regular_directions C hr hx'.1, regular_directions C hr hy] at hbound
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TransverseSaturation
