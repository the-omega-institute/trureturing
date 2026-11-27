/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedMidpointFiveAxes
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedMidpointFiveAxes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Separation confines the two shores' neighbors to disjoint subsets of the five active coordinates. Exterior cancellation forces both nonempty subsets to have even cardinalities, so both contain exactly two directions. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter

/-! Five active axes force two neighbors on each side of a shared midpoint. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedMidpointFiveAxes

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip flip_adj)
open BalancedCubeComponentBoundary (directions mem_directions exterior_even)
open Q9IsotropicHuang (parity)
open Q9MinimumDistanceOperator (minimumDisplacements)
open private parity_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private row_contact from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter

open Classical in
/-- If the masks on the starting parity use at most five axes, every common
midpoint has exactly two occupied neighbors from each support. -/
theorem two_neighbors_each
    {C D : Finset (Q 9)} {b : Bool} {z : Q 9} {i j : Fin 9} {A : Finset (Fin 9)}
    (hA : A.card ≤ 5) (hmask : ∀ T ∈ minimumDisplacements C D b 2, T ⊆ A)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hi : flip z i ∈ C) (hj : flip z j ∈ D) (hb : parity (flip z i) = b) :
    (directions C z).card = 2 ∧ (directions D z).card = 2 := by
  have disjoint_dirs {k l : Fin 9} (hk : flip z k ∈ C) (hl : flip z l ∈ D) : k ≠ l := by
    intro he
    subst l
    have hbad := hsep _ hk _ hl
    simp at hbad
  have hb' (k : Fin 9) : parity (flip z k) = b :=
    (parity_flip z k).trans ((parity_flip z i).symm.trans hb)
  have hleft : directions C z ⊆ A := by
    intro k hk
    have hk' := (mem_directions C z k).mp hk
    exact hmask _ (row_contact hk' hj (disjoint_dirs hk' hj) (hb' k)) (by simp)
  have hright : directions D z ⊆ A := by
    intro k hk
    have hk' := (mem_directions D z k).mp hk
    exact hmask _ (row_contact hi hk' (disjoint_dirs hi hk') hb) (by simp)
  have hzC : z ∉ C := by
    intro hz
    have hs := hsep z hz _ hj
    have hd : hammingDist z (flip z j) = 1 := flip_adj z j
    omega
  have hzD : z ∉ D := by
    intro hz
    have hs := hsep _ hi z hz
    have hd : hammingDist (flip z i) z = 1 := (flip_adj z i).symm
    omega
  have hdis : Disjoint (directions C z) (directions D z) := by
    apply disjoint_left.mpr
    intro k hk hl
    exact disjoint_dirs ((mem_directions C z k).mp hk) ((mem_directions D z k).mp hl) rfl
  have hcap := (card_le_card (union_subset hleft hright)).trans hA
  rw [card_union_of_disjoint hdis] at hcap
  have hposC := card_pos.mpr ⟨i, (mem_directions C z i).mpr hi⟩
  have hposD := card_pos.mpr ⟨j, (mem_directions D z j).mpr hj⟩
  obtain ⟨n, hn⟩ := exterior_even C hrC hbC z hzC
  obtain ⟨m, hm⟩ := exterior_even D hrD hbD z hzD
  omega

#print axioms two_neighbors_each

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedMidpointFiveAxes
