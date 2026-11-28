import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SquareMaskGraph

/-!
An edge between cubic contact axes cannot have exactly one common partner.
The translations along the two endpoints then force an exterior row with
only one neighbor on the opposite support.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
namespace Q9CubicContactCommonPartner

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip)
open BalancedCubeComponentBoundary (directions mem_directions)
open BalancedCubeGirth (flip_comm)
open Q9IsotropicHuang (parity weightedLinear)
open Q9ActualMinimumDisplacements (exists_both_parity_supported_of_signed_defect_singular)
open Q9DegreeThreeContactOrbit (translated_contact_of_three_partners exterior_midpoint_directions)
open Q9MinimumDistanceOperator (RidgeContact minimumDisplacements)
open Q9WeightedSaturation (defect signedBiadjacency)
open private differingAxes parity_flip mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private differingAxes_right_inj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactComplement
open private diff_pair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar
open private row_contact minimumDisplacements_swap_two from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter

open Classical in
/-- The partner triples `{j,a,d}` and `{i,c,d}` cannot occur at a realized
distance-two edge `{i,j}` when the five listed axes are distinct. -/
theorem no_single_common_partner
    {C D : Finset (Q 9)} {b : Bool} {i j a c d : Fin 9}
    (hij : i ≠ j) (hic : i ≠ c) (hca : c ≠ a) (hcj : c ≠ j)
    (had : a ≠ d) (hcd : c ≠ d)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (hroot : ({i, j} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2)
    (hi : ∀ k, ({i, k} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 →
      k = j ∨ k = a ∨ k = d)
    (hj : ∀ k, ({j, k} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 →
      k = i ∨ k = c ∨ k = d) : False := by
  obtain ⟨x, hx, y, hy, hp, _, he⟩ := mem_minimumDisplacements.mp hroot
  have hy' : y = flip (flip x i) j := differingAxes_right_inj ((he.trans (diff_pair x hij).symm))
  have hcross : RidgeContact C D b [i] j x := ⟨by simpa using hij.symm, hx, hp, hy' ▸ hy⟩
  have hcross' : RidgeContact C D b [j] i x :=
    ⟨by simpa using hij, hx, hp, by
      change flip (flip x j) i ∈ D
      rw [flip_comm x j i]
      exact hcross.2.2.2⟩
  have getC (k : Fin 9) :
      ∃ f : Q 9 → ℝ, (∀ z, f z ≠ 0 ↔ z ∈ C ∧ parity z = b) ∧
        (∀ z ∉ C, weightedLinear (fun t => if t = k then 2 else 1) f z = 0) := by
    let w (t : Fin 9) : ℝ := if t = k then 2 else 1
    have hw (t : Fin 9) : 0 < w t := by dsimp only [w]; split <;> norm_num
    exact exists_both_parity_supported_of_signed_defect_singular C hrC hcC hbC w hw (hdetC w) b
  obtain ⟨f, hf, hAf⟩ := getC j
  obtain ⟨f', hf', hAf'⟩ := getC i
  obtain ⟨g, hg, hAg⟩ :=
    exists_both_parity_supported_of_signed_defect_singular D hrD hcD hbD
      (fun _ => 1) (fun _ => by norm_num) (hdetD fun _ => 1) b
  have ha := translated_contact_of_three_partners had hsep hi f g hf hg hAf hAg hcross
  have hc := translated_contact_of_three_partners hcd hsep hj f' g hf' hg hAf' hAg hcross'
  let u := flip (flip x a) d
  let v := flip (flip x c) d
  have hu : u ∈ C := ha.2.1
  have hv : v ∈ C := hc.2.1
  have hu' : parity u = b := ha.2.2.1
  have hD : flip (flip v i) j ∈ D := by
    rw [flip_comm v i j]
    exact hc.2.2.2
  let z := flip v i
  let y' := flip z j
  have hy'D : y' ∈ D := hD
  have hv' : parity v = b := hc.2.2.1
  have hy'b : parity y' = b := by
    simp only [y', z, parity_flip, Bool.not_not, hv']
  have hy'C : flip (flip y' j) i ∈ C := by
    simpa only [y', z, BalancedCriticalSpectrum.flip_flip] using hv
  have hI (k : Fin 9) (hk : ({i, k} : Finset (Fin 9)) ∈ minimumDisplacements D C b 2) :
      k ∈ ({j, a, d} : Finset (Fin 9)) := by
    rw [minimumDisplacements_swap_two D C b] at hk
    simpa only [mem_insert, mem_singleton] using hi k hk
  have hcap : ({j, a, d} : Finset (Fin 9)).card ≤ 3 := by
    calc
      _ ≤ ({a, d} : Finset (Fin 9)).card + 1 := card_insert_le j _
      _ = 3 := by rw [card_pair had]
  obtain ⟨hsub, hcard⟩ := exterior_midpoint_directions hcap hI
    (fun y hy x hx => by rw [hammingDist_comm]; exact hsep x hx y hy)
    hrD hbD hy'b hy'D hy'C
  rw [show flip y' j = z by simp only [y', BalancedCriticalSpectrum.flip_flip]] at hsub hcard
  obtain ⟨k, hk, hkj⟩ := exists_mem_ne (by rw [hcard]; decide) j
  have hDz := (mem_directions D z k).mp hk
  have hmissing : ({i, c} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2 :=
    fun h => (hi c h).elim hcj (fun h => h.elim hca hcd)
  have hpairs (t : Q 9) (ht : t ∈ C) (hp : parity t = b)
      (hd : flip (flip t i) c ∈ D) : False :=
    hmissing (row_contact (show flip (flip t i) i ∈ C by simpa only [BalancedCriticalSpectrum.flip_flip] using ht) hd hic
      (by simpa only [BalancedCriticalSpectrum.flip_flip] using hp))
  have hk' : k = a ∨ k = d := by
    simpa only [mem_insert, mem_singleton, hkj, false_or] using hsub hk
  rcases hk' with hka | hkd
  · subst k
    apply hpairs u hu hu'
    have e : flip z a = flip (flip u i) c := by
      dsimp only [z, v, u]
      rw [flip_comm (flip (flip x c) d) i a, flip_comm (flip x c) d a,
        flip_comm x c a, flip_comm (flip x a) c d, flip_comm (flip (flip x a) d) c i]
    exact e ▸ hDz
  · subst k
    apply hpairs x hx hp
    dsimp only [z, v] at hDz
    rw [flip_comm (flip x c) d i, BalancedCriticalSpectrum.flip_flip, flip_comm x c i] at hDz
    exact hDz

#print axioms no_single_common_partner

end Q9CubicContactCommonPartner
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
