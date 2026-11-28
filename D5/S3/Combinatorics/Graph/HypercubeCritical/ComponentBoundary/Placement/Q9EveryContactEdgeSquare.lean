import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactFibreSmallObstructions
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SquareMaskGraph

/-! Every realized contact mask is contained in a four-cycle of realized masks.
The cycle is witnessed by a single shared exterior row. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EveryContactEdgeSquare

open Finset
open BalancedCriticalSpectrum (Q flip)
open Q9SharedContactNormalized (LocalRules)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9IsotropicHuang (parity)
open Q9ContactFibreSmallObstructions (shared_row_second)
open private differingAxes mem_minimumDisplacements parity_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private row_contact minimumDisplacements_swap_two from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter
open private diff_pair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar
open private differingAxes_right_inj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactComplement

open Classical in
/-- The two occupied neighbors on each side of a shared exterior row form
an actual alternating four-cycle in the graph of contact directions. -/
theorem every_realized_mask_on_four_cycle {C D : Finset (Q 9)} {b : Bool} {i j : Fin 9}
    (hl : LocalRules C) (hr : LocalRules D)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hroot : ({i,j} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2) :
    ∃ p q : Fin 9, p ≠ i ∧ q ≠ j ∧ p ≠ j ∧ q ≠ i ∧ p ≠ q ∧
      ({p,j} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 ∧
      ({i,q} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 ∧
      ({p,q} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 := by
  let F := minimumDisplacements C D b 2
  obtain ⟨x, hx, y, hy, hpar, hd, hxy⟩ := mem_minimumDisplacements.mp hroot
  have hij : i ≠ j := by
    intro he
    subst j
    change (differingAxes x y).card = 2 at hd
    rw [hxy] at hd
    simp at hd
  have hy' : y = flip (flip x i) j := differingAxes_right_inj (hxy.trans (diff_pair x hij).symm)
  let z := flip x i
  have hz : parity z = !b := by rw [show z = flip x i from rfl, parity_flip, hpar]
  have hi : flip z i ∈ C := by simpa only [z, BalancedCriticalSpectrum.flip_flip] using hx
  have hj : flip z j ∈ D := hy' ▸ hy
  obtain ⟨p, hpi, hpj, hpC⟩ := shared_row_second (F := F) hl hsep Subset.rfl hz hi hj
  have hs (u : Q 9) (hu : u ∈ D) (v : Q 9) (hv : v ∈ C) : 2 ≤ hammingDist u v := by
    rw [hammingDist_comm]
    exact hsep v hv u hu
  have ha : minimumDisplacements D C b 2 ⊆ F := by
    rw [minimumDisplacements_swap_two D C b]
  obtain ⟨q, hqj, hqi, hqD⟩ := shared_row_second hr hs ha hz hj hi
  have hne {a c : Fin 9} (hC : flip z a ∈ C) (hD : flip z c ∈ D) : a ≠ c := by
    intro he
    subst c
    have hb := hsep _ hC _ hD
    simp at hb
  have hpq := hne hpC hqD
  have hpb : parity (flip z p) = b := by rw [parity_flip, hz]; cases b <;> rfl
  exact ⟨p,q,hpi,hqj,hne hpC hj,(hne hi hqD).symm,hpq,hpj,
    by simpa only [Finset.pair_comm] using hqi,row_contact hpC hqD hpq hpb⟩

#print axioms every_realized_mask_on_four_cycle

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EveryContactEdgeSquare
