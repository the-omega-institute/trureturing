import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9PendantCliqueNormalization
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9WeightedCoordinateAction
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskRootNormalization
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangBalancedSymmetry

/-! Carry an arbitrary isolated four-axis block into the rooted opposing-star
geometry using the same action on the weighted Huang operators. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9PendantCliqueActual

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
local notation "flip" => BalancedCriticalSpectrum.flip
open Q9IsotropicHuang (parity weightedLinear)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9SharedContactNormalized (LocalRules)
open Q9TightDistanceTwoNormalized (baseAxes rightCenter DirectStar)
open Q9PendantCliqueNormalization (exists_normalized_rooted_pendant_stars)
open Q9WeightedCoordinateAction (normalize_weighted_exterior_solution)
open Q9TenMaskRootNormalization (normalize_root_mapped)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
  (normalize origin)
open private normalize_flip_axis from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoNormalized
open private mem_minimumDisplacements differingAxes from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private swap_mem_iff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisMissingContact


private theorem exists_block_frame {A : Finset (Fin 9)} {i j : Fin 9}
    (hA : A.card = 4) (hi : i ∈ A) (hj : j ∈ A) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 9), (∀ k, σ k ∈ A ↔ k ∈ baseAxes) ∧ σ 0 = i ∧ σ 1 = j := by
  have hc : baseAxes.card = A.card := (show baseAxes.card = 4 by decide).trans hA.symm
  obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_map_finset_eq baseAxes A hc
  have hmem (k : Fin 9) : ρ k ∈ A ↔ k ∈ baseAxes := by
    rw [← hρ, mem_map_equiv, Equiv.symm_apply_apply]
  let ρ₁ := ρ.trans (Equiv.swap (ρ 0) i)
  have hρ₁ (k : Fin 9) : ρ₁ k ∈ A ↔ k ∈ baseAxes :=
    (swap_mem_iff ((hmem 0).mpr (by decide)) hi (ρ k)).trans (hmem k)
  have hρ₁0 : ρ₁ 0 = i := Equiv.swap_apply_left _ _
  let σ := ρ₁.trans (Equiv.swap (ρ₁ 1) j)
  have hσ (k : Fin 9) : σ k ∈ A ↔ k ∈ baseAxes :=
    (swap_mem_iff ((hρ₁ 1).mpr (by decide)) hj (ρ₁ k)).trans (hρ₁ k)
  have hne : i ≠ ρ₁ 1 := by
    rw [← hρ₁0]
    exact fun h => (by decide : (0 : Fin 9) ≠ 1) (ρ₁.injective h)
  refine ⟨σ, hσ, ?_, Equiv.swap_apply_left _ _⟩
  change Equiv.swap (ρ₁ 1) j (ρ₁ 0) = i
  rw [hρ₁0, Equiv.swap_apply_of_ne_of_ne hne hij]

open Classical in
/-- A realized contact in any four-axis block with three closed axes gives normalized
opposing-star supports. Exterior weighted solutions transport with the
contact frame, so the conclusion applies to the actual balanced components. -/
theorem pendant_block_gives_normalized_stars {C D : Finset (Q 9)} {b : Bool}
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
      (∀ z ∉ D, weightedLinear (fun _ => 1) g z = 0)) :
    ∃ (C' D' : Finset (Q 9)) (m : Fin 9), (m = 4 ∨ m = 5) ∧
      DirectStar C' origin 4 ∧ DirectStar D' rightCenter m ∧
      LocalRules C' ∧ LocalRules D' ∧
      (∀ x ∈ C', ∀ y ∈ D', 2 ≤ hammingDist x y) ∧
      (∀ i j : Fin 9, ({i,j} : Finset (Fin 9)) ∈ minimumDisplacements C' D' true 2 →
        (i.val < 3 → j ∈ baseAxes) ∧ (j.val < 3 → i ∈ baseAxes)) := by
  obtain ⟨x, hx, y, hy, hp, hd, hxy⟩ := mem_minimumDisplacements.mp hroot
  have hij : i ≠ j := by
    intro he
    subst j
    change (differingAxes x y).card = 2 at hd
    rw [hxy] at hd
    simp at hd
  obtain ⟨ρ, hρ, hρ0, hρ1⟩ := exists_block_frame hA hi hj hij
  have hρ3 : ρ 3 ∈ A := (hρ 3).mpr (by decide)
  let σ := ρ.trans (Equiv.swap (ρ 3) hub)
  have hσ (k : Fin 9) : σ k ∈ A ↔ k ∈ baseAxes :=
    (swap_mem_iff hρ3 hHub (ρ k)).trans (hρ k)
  have hσHub : σ 3 = hub := Equiv.swap_apply_left _ _
  have hσ0 : σ 0 = i := by
    change Equiv.swap (ρ 3) hub (ρ 0) = i
    rw [Equiv.swap_apply_of_ne_of_ne (ρ.injective.ne (by decide)) (show ρ 0 ≠ hub by rw [hρ0]; exact hiHub), hρ0]
  have hσ1 : σ 1 = j := by
    change Equiv.swap (ρ 3) hub (ρ 1) = j
    rw [Equiv.swap_apply_of_ne_of_ne (ρ.injective.ne (by decide)) (show ρ 1 ≠ hub by rw [hρ1]; exact hjHub), hρ1]
  have hxy' : differingAxes x y = {σ 0, σ 1} := by rwa [hσ0, hσ1]
  let e := normalize σ x
  let X := C.map e.toEmbedding
  let Y := D.map e.toEmbedding
  obtain ⟨hgeo, hmap⟩ := normalize_root_mapped σ hx hy hp hxy' hsep hrC hrD hbC hbD
  have he (z : Q 9) (k : Fin 9) : e (flip z k) = flip (e z) (σ.symm k) := by
    simpa only [Equiv.apply_symm_apply] using normalize_flip_axis σ x z (σ.symm k)
  have hrX : ((hypercube 9).induce (X : Set (Q 9))).IsRegularOfDegree 3 ∧ IsBalanced X := by
    have hEq : X = C.image e := Finset.map_eq_image _ _
    rw [hEq]
    exact HuangBalancedSymmetry.cube_action_regular_balanced e σ.symm he hrC hbC
  have hrY : ((hypercube 9).induce (Y : Set (Q 9))).IsRegularOfDegree 3 ∧ IsBalanced Y := by
    have hEq : Y = D.image e := Finset.map_eq_image _ _
    rw [hEq]
    exact HuangBalancedSymmetry.cube_action_regular_balanced e σ.symm he hrD hbD
  have hshift : b + parity x = false := by rw [hp]; cases b <;> rfl
  have hCX : ∀ j, ∃ f : Q 9 → ℝ,
      (∀ z, f z ≠ 0 ↔ z ∈ X ∧ parity z = false) ∧
      (∀ z ∉ X, weightedLinear (fun k => if k = j then 2 else 1) f z = 0) := by
    intro j
    obtain ⟨f, hf, hAf⟩ := hC (σ j)
    have hzero : ∀ z ∉ C, weightedLinear (fun k => if σ.symm k = j then 2 else 1) f z = 0 := by
      intro z hz
      have heq : (fun k : Fin 9 => if σ.symm k = j then (2 : ℝ) else 1) =
          fun k => if k = σ j then 2 else 1 := by
        funext k
        simp only [Equiv.symm_apply_eq]
      rw [heq]
      exact hAf z hz
    simpa only [X, e, hshift] using normalize_weighted_exterior_solution C σ x b
      (fun k => if k = j then 2 else 1) f hf hzero
  have hDY : ∃ g : Q 9 → ℝ,
      (∀ z, g z ≠ 0 ↔ z ∈ Y ∧ parity z = false) ∧
      (∀ z ∉ Y, weightedLinear (fun _ => 1) g z = 0) := by
    obtain ⟨g, hg, hAg⟩ := hD
    simpa only [Y, e, hshift] using normalize_weighted_exterior_solution D σ x b
      (fun _ => 1) g hg hAg
  have hclosed' (k l : Fin 9) (hm : ({k,l} : Finset (Fin 9)) ∈ minimumDisplacements X Y false 2) :
      (k.val < 3 → l ∈ baseAxes) ∧ (l.val < 3 → k ∈ baseAxes) := by
    change ({k,l} : Finset (Fin 9)) ∈ minimumDisplacements
      (C.map (normalize σ x).toEmbedding) (D.map (normalize σ x).toEmbedding) false 2 at hm
    rw [hmap] at hm
    obtain ⟨M, hM, hMmap⟩ := mem_map.mp hm
    have hM' : M = {σ k, σ l} := by
      apply Finset.map_injective (f := σ.symm.toEmbedding)
      simpa using hMmap
    rw [hM'] at hM
    have hlow (r : Fin 9) (hr : r.val < 3) : σ r ∈ A ∧ σ r ≠ hub := by
      refine ⟨(hσ r).mpr ((show ∀ s : Fin 9, s.val < 3 → s ∈ baseAxes by decide) r hr), ?_⟩
      intro he
      have he' := σ.injective (he.trans hσHub.symm)
      subst r
      omega
    have h := hclosed (σ k) (σ l) hM
    exact ⟨fun hk => (hσ l).mp (h.1 (hlow k hk).1 (hlow k hk).2),
      fun hl => (hσ k).mp (h.2 (hlow l hl).1 (hlow l hl).2)⟩
  exact exists_normalized_rooted_pendant_stars hgeo hrX.1 hrY.1 hrX.2 hrY.2 hCX hDY hclosed'

#print axioms pendant_block_gives_normalized_stars

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9PendantCliqueActual
