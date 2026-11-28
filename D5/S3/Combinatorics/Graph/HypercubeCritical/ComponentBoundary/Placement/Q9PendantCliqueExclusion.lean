import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9PendantCliqueActual
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9PendantK4StarsReplay

/-! A four-axis contact block with three closed axes contradicts the local opposing-star
geometry after a common signed coordinate action. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9PendantCliqueExclusion

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
local notation "flip" => BalancedCriticalSpectrum.flip
open Q9IsotropicHuang (parity weightedLinear)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9TightDistanceTwoNormalized (baseAxes)
open Q9PendantCliqueActual (pendant_block_gives_normalized_stars)
open Q9PendantK4StarsReplay (pendant_k4_stars_excluded)
open private differingAxes mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private diff_pair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar

open Classical in
/-- No realized distance-two contact between two closed axes can lie in a
four-axis block with at most one attachment axis
of the contact graph of a weighted-saturated balanced component pair. -/
theorem no_four_axis_block_with_three_closed_axes {C D : Finset (Q 9)} {b : Bool}
    {A : Finset (Fin 9)} {i j hub : Fin 9} (hA : A.card = 4) (hi : i ∈ A) (hj : j ∈ A)
    (hHub : hub ∈ A) (hiHub : i ≠ hub) (hjHub : j ≠ hub)
    (hroot : ({i,j} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2)
    (hclosed : ∀ k l : Fin 9, ({k,l} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 →
      (k ∈ A → k ≠ hub → l ∈ A) ∧ (l ∈ A → l ≠ hub → k ∈ A))
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hC : ∀ j, ∃ f : Q 9 → ℝ,
      (∀ z, f z ≠ 0 ↔ z ∈ C ∧ parity z = b) ∧
      (∀ z ∉ C, weightedLinear (fun k => if k = j then 2 else 1) f z = 0))
    (hD : ∃ g : Q 9 → ℝ,
      (∀ z, g z ≠ 0 ↔ z ∈ D ∧ parity z = b) ∧
      (∀ z ∉ D, weightedLinear (fun _ => 1) g z = 0)) : False := by
  obtain ⟨X,Y,m,hm,hleft,hright,hl,hr,hsep',hclosed'⟩ :=
    pendant_block_gives_normalized_stars hA hi hj hHub hiHub hjHub hroot hclosed hsep hrC hrD hbC hbD hC hD
  apply pendant_k4_stars_excluded hm
  refine ⟨hleft, hright, hl, hr, hsep', ?_⟩
  intro x hx hp k hk l hl hy
  have hkl : k ≠ l := fun he => hl (he ▸ ((show ∀ r : Fin 9, r.val < 3 → r ∈ baseAxes by decide) k hk))
  have hd : hammingDist x (flip (flip x k) l) = 2 := by
    change (differingAxes x (flip (flip x k) l)).card = 2
    rw [diff_pair x hkl, card_pair hkl]
  have hmask : ({k,l} : Finset (Fin 9)) ∈ minimumDisplacements X Y true 2 :=
    mem_minimumDisplacements.mpr ⟨x, hx, _, hy, hp, hd, diff_pair x hkl⟩
  exact hl ((hclosed' k l hmask).1 hk)

#print axioms no_four_axis_block_with_three_closed_axes

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9PendantCliqueExclusion
