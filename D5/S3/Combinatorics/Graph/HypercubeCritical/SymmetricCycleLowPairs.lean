/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricCycleLowPairs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricCycleLowPairs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.result; instance=D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.claim
   digest: On an actual embedded high eight-cycle, girth excludes low pairs between distinct cycle points and forces two cycle partners of an outside high leaf to be antipodal. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Batteries.Tactic.OpenPrivate

/-! Low-point pairs on an actual embedded high eight-cycle.
Finite index witnesses are proved by kernel computation and immediately
transported to real graph edges and the existing girth exclusion lemmas. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricCycleLowPairs

open SimpleGraph

attribute [local instance] Classical.propDecidable

open private lowPair low_pair_excluded_by_common_high
  low_pair_excluded_by_short_paths low_pair_excluded_by_fixed_pair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels

/-- Two distinct same-parity indices have either a common cycle neighbor or
an actual four-edge cycle path with the required distinct internal indices. -/
private theorem same_parity_cycle_path_witness :
    ∀ i j : Fin 8, i ≠ j → i.val % 2 = j.val % 2 →
      (∃ k : Fin 8, (cycleGraph 8).Adj i k ∧ (cycleGraph 8).Adj j k) ∨
      ∃ p m q : Fin 8, (cycleGraph 8).Adj i p ∧ (cycleGraph 8).Adj p m ∧
        (cycleGraph 8).Adj m q ∧ (cycleGraph 8).Adj j q ∧ i ≠ m ∧ p ≠ q := by
  decide +kernel

/-- Same-parity distinct indices that are not opposite have a common neighbor. -/
private theorem nonopposite_cycle_common_neighbor :
    ∀ i j : Fin 8, i ≠ j → i.val % 2 = j.val % 2 → j ≠ i + 4 →
      ∃ k : Fin 8, (cycleGraph 8).Adj i k ∧ (cycleGraph 8).Adj j k := by
  decide +kernel

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

private theorem low_pair_symm {a b : V} (hp : lowPair G a b) : lowPair G b a := by
  obtain ⟨w, hw, haw, hbw⟩ := hp
  exact ⟨w, hw, hbw, haw⟩

private theorem low_pair_same_side
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    {a b : V} (hbL : b ∈ L) (hp : lowPair G a b) : a ∈ L := by
  obtain ⟨w, _hw, haw, hbw⟩ := hp
  have hwR : w ∈ R := hpart.mem_of_mem_adj hbL hbw
  exact hpart.symm.mem_of_mem_adj hwR haw.symm

private theorem opposite_side_low_pair_excluded
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    {a b : V} (haL : a ∈ L) (hbR : b ∈ R) : ¬ lowPair G a b := by
  intro hp
  have haR := low_pair_same_side hpart.symm hbR hp
  exact Set.disjoint_left.mp hpart.disjoint haL haR

private theorem same_parity_cycle_low_pair_excluded
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (c : Fin 8 → V) (hc : Function.Injective c)
    (hc3 : ∀ k, G.degree (c k) = 3)
    (hcycle : ∀ i j, (cycleGraph 8).Adj i j → G.Adj (c i) (c j))
    {i j : Fin 8} (hij : i ≠ j) (hpar : i.val % 2 = j.val % 2)
    (hiR : c i ∈ R) : ¬ lowPair G (c i) (c j) := by
  have hcij : c i ≠ c j := fun he => hij (hc he)
  rcases same_parity_cycle_path_witness i j hij hpar with
    ⟨k, hik, hjk⟩ | ⟨p, m, q, hip, hpm, hmq, hjq, him, hpq⟩
  · exact low_pair_excluded_by_common_high hpart hg hiR (hc3 k)
      (hcycle i k hik) (hcycle j k hjk) hcij
  · exact low_pair_excluded_by_short_paths hpart hg hiR (hc3 p) (hc3 q)
      (hcycle i p hip) (hcycle p m hpm) (hcycle m q hmq) (hcycle j q hjq)
      hcij (fun he => him (hc he)) (fun he => hpq (hc he))

/-- No distinct actual eight-cycle high points can share a degree-two neighbor.
Same-side pairs are excluded by actual four- or six-cycles; opposite-side
pairs are excluded by the actual bipartition. -/
private theorem cycle_low_pairs_excluded
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (c : Fin 8 → V) (hc : Function.Injective c)
    (hc3 : ∀ k, G.degree (c k) = 3)
    (hcycle : ∀ i j, (cycleGraph 8).Adj i j → G.Adj (c i) (c j))
    (hcL : ∀ i, i.val % 2 = 0 → c i ∈ L)
    (hcR : ∀ i, i.val % 2 = 1 → c i ∈ R)
    {i j : Fin 8} (hij : i ≠ j) : ¬ lowPair G (c i) (c j) := by
  by_cases hpar : i.val % 2 = j.val % 2
  · by_cases hi0 : i.val % 2 = 0
    · exact same_parity_cycle_low_pair_excluded hpart.symm hg c hc hc3 hcycle
        hij hpar (hcL i hi0)
    · have hi1 : i.val % 2 = 1 := by omega
      exact same_parity_cycle_low_pair_excluded hpart hg c hc hc3 hcycle
        hij hpar (hcR i hi1)
  · by_cases hi0 : i.val % 2 = 0
    · have hj1 : j.val % 2 = 1 := by omega
      exact opposite_side_low_pair_excluded hpart (hcL i hi0) (hcR j hj1)
    · have hi1 : i.val % 2 = 1 := by omega
      have hj0 : j.val % 2 = 0 := by omega
      exact opposite_side_low_pair_excluded hpart.symm (hcR i hi1) (hcL j hj0)

private theorem cycle_low_pair_partners_same_parity
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (c : Fin 8 → V)
    (hcL : ∀ i, i.val % 2 = 0 → c i ∈ L)
    (hcR : ∀ i, i.val % 2 = 1 → c i ∈ R)
    {t : V} {i j : Fin 8}
    (hti : lowPair G t (c i)) (htj : lowPair G t (c j)) :
    i.val % 2 = j.val % 2 := by
  by_contra hpar
  by_cases hi0 : i.val % 2 = 0
  · have hj1 : j.val % 2 = 1 := by omega
    have htL := low_pair_same_side hpart (hcL i hi0) hti
    have htR := low_pair_same_side hpart.symm (hcR j hj1) htj
    exact Set.disjoint_left.mp hpart.disjoint htL htR
  · have hi1 : i.val % 2 = 1 := by omega
    have hj0 : j.val % 2 = 0 := by omega
    have htR := low_pair_same_side hpart.symm (hcR i hi1) hti
    have htL := low_pair_same_side hpart (hcL j hj0) htj
    exact Set.disjoint_left.mp hpart.disjoint htL htR

/-- Two distinct cycle partners of an actual point outside the eight-cycle
must be opposite. No degree or leaf premise on that outside point is needed. -/
private theorem outside_cycle_low_pair_partners_opposite
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (c : Fin 8 → V) (hc : Function.Injective c)
    (hc3 : ∀ k, G.degree (c k) = 3)
    (hcycle : ∀ i j, (cycleGraph 8).Adj i j → G.Adj (c i) (c j))
    (hcL : ∀ i, i.val % 2 = 0 → c i ∈ L)
    (hcR : ∀ i, i.val % 2 = 1 → c i ∈ R)
    {t : V} (ht : ∀ k, t ≠ c k) {i j : Fin 8} (hij : i ≠ j)
    (hti : lowPair G t (c i)) (htj : lowPair G t (c j)) : j = i + 4 := by
  have hpar := cycle_low_pair_partners_same_parity hpart c hcL hcR hti htj
  by_contra hnot
  obtain ⟨k, hik, hjk⟩ := nonopposite_cycle_common_neighbor i j hij hpar hnot
  have hcij : c i ≠ c j := fun he => hij (hc he)
  have hcit : c i ≠ t := (ht i).symm
  have hcjt : c j ≠ t := (ht j).symm
  have hfixed := low_pair_symm hti
  have hother := low_pair_symm htj
  by_cases hj0 : j.val % 2 = 0
  · exact (low_pair_excluded_by_fixed_pair hpart.symm hg (hcL j hj0) (hc3 k)
      hcij hcit hcjt (hcycle j k hjk) (hcycle i k hik) hfixed) hother
  · have hj1 : j.val % 2 = 1 := by omega
    exact (low_pair_excluded_by_fixed_pair hpart hg (hcR j hj1) (hc3 k)
      hcij hcit hcjt (hcycle j k hjk) (hcycle i k hik) hfixed) hother

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricCycleLowPairs
