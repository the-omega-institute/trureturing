import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DegreeThreeContactOrbit
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoNormalized

/-! A rooted cube isometry transports the forced translation of a contact
from the actual supports to a prescribed labeling of the mask graph. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
namespace Q9NormalizedContactTranslations

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
local notation "flip" => BalancedCriticalSpectrum.flip
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
  (normalize)
open private normalize_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
open Q9IsotropicHuang (parity)
open Q9MinimumDistanceOperator (minimumDisplacements RidgeContact)
open Q9ActualMinimumDisplacements (exists_both_parity_supported_of_signed_defect_singular)
open Q9WeightedSaturation (defect signedBiadjacency)
open Q9DegreeThreeContactOrbit (translated_contact_of_three_partners)
open Q9TightDistanceTwoNormalized (normalize_minimumDisplacements)
open private parity_normalize_eq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoNormalized

open Classical in
/-- In normalized coordinates the other two partners of a cubic axis act
by simultaneously flipping these coordinates at the contact endpoints. -/
theorem normalized_contact_translation
    {C D : Finset (Q 9)} (σ : Equiv.Perm (Fin 9)) (o : Q 9)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0) :
    let e := normalize σ o
    let X := C.map e.toEmbedding
    let Y := D.map e.toEmbedding
    ∀ ⦃i j p q : Fin 9⦄ ⦃x : Q 9⦄, p ≠ q →
      (∀ k, ({i, k} : Finset (Fin 9)) ∈ minimumDisplacements X Y false 2 →
        k = j ∨ k = p ∨ k = q) →
      RidgeContact X Y false [i] j x →
      RidgeContact X Y false [i] j (flip (flip x p) q) := by
  let e := normalize σ o
  let X := C.map e.toEmbedding
  let Y := D.map e.toEmbedding
  change ∀ ⦃i j p q : Fin 9⦄ ⦃x : Q 9⦄, p ≠ q → _ → _ → _
  intro i j p q x hpq hpartners hx
  have hflip (v : Q 9) (k : Fin 9) : e (flip v (σ k)) = flip (e v) k := by
    simpa [e] using normalize_flip σ.symm o v (σ k)
  have hpar : parity o + parity o = false := by cases parity o <;> rfl
  have hmem := hx.2.1
  change x ∈ X at hmem
  obtain ⟨u, hu, hu'⟩ := mem_map.mp hmem
  change e u = x at hu'
  subst x
  have huParity : parity u = parity o := by
    apply (parity_normalize_eq σ o u (parity o)).mp
    exact hx.2.2.1.trans hpar.symm
  have hv : flip (flip u (σ i)) (σ j) ∈ D := by
    have hm : e (flip (flip u (σ i)) (σ j)) ∈ Y := by
      rw [hflip, hflip]
      exact hx.2.2.2
    simpa [Y, mem_map_equiv] using hm
  have hmap : minimumDisplacements X Y false 2 =
      (minimumDisplacements C D (parity o) 2).map (mapEmbedding σ.symm.toEmbedding).toEmbedding := by
    simpa only [X, Y, e, hpar] using normalize_minimumDisplacements σ o C D (parity o) 2
  have hpart (k : Fin 9)
      (hk : ({σ i, k} : Finset (Fin 9)) ∈ minimumDisplacements C D (parity o) 2) :
      k = σ j ∨ k = σ p ∨ k = σ q := by
    have hm : ({i, σ.symm k} : Finset (Fin 9)) ∈ minimumDisplacements X Y false 2 := by
      rw [hmap]
      exact mem_map.mpr ⟨_, hk, by simp [Finset.mapEmbedding_apply]⟩
    simpa only [Equiv.symm_apply_eq] using hpartners (σ.symm k) hm
  let w (k : Fin 9) : ℝ := if k = σ j then 2 else 1
  have hw (k : Fin 9) : 0 < w k := by
    dsimp only [w]
    split <;> norm_num
  obtain ⟨f, hf, hAf⟩ := exists_both_parity_supported_of_signed_defect_singular
    C hrC hcC hbC w hw (hdetC w) (parity o)
  obtain ⟨g, hg, hAg⟩ := exists_both_parity_supported_of_signed_defect_singular
    D hrD hcD hbD (fun _ => 1) (fun _ => by norm_num) (hdetD fun _ => 1) (parity o)
  have hcontact : RidgeContact C D (parity o) [σ i] (σ j) u :=
    ⟨fun h => hx.1 (by simpa using σ.injective (List.mem_singleton.mp h)), hu, huParity, hv⟩
  obtain ⟨_, hCu, hCuParity, hDuv⟩ := translated_contact_of_three_partners
    (σ.injective.ne hpq) hsep hpart f g hf hg hAf hAg hcontact
  let t := flip (flip u (σ p)) (σ q)
  have he : e t = flip (flip (e u) p) q := by simp only [t, hflip]
  refine ⟨hx.1, mem_map.mpr ⟨t, hCu, he⟩, ?_, ?_⟩
  · rw [← he]
    have h := (parity_normalize_eq σ o t (parity o)).mpr hCuParity
    exact h.trans hpar
  · rw [← he]
    refine mem_map.mpr ⟨flip (flip t (σ i)) (σ j), hDuv, ?_⟩
    change e (flip (flip t (σ i)) (σ j)) = flip (flip (e t) i) j
    rw [hflip, hflip]

#print axioms normalized_contact_translation

end Q9NormalizedContactTranslations
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
