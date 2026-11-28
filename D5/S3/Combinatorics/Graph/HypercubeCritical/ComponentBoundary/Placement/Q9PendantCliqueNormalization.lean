import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoNormalized
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9PendantCliqueParity

/-! Normalizing opposing stars with one possible attachment axis, preserving
that axis under the frame action. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9PendantCliqueNormalization

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip IsBalanced)
open BalancedCubeComponentBoundary (directions mem_directions)
open Q9IsotropicHuang (parity weightedLinear)
open Q9MinimumDistanceOperator (minimumDisplacements RidgeContact)
open Q9FiveAxisMissingContact (Geometry)
open Q9DegreeThreeContactOrbit (translated_contact_of_three_partners)
open Q9PendantCliqueParity (opposing_stars_full_geometry)
open private axes from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9PendantCliqueParity
open Q9SharedContactNormalized (LocalRules)
open Q9TightDistanceTwoNormalized (baseAxes rightCenter DirectStar exists_ordered_axis_permutation
  normalize_minimumDisplacements)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
  (normalize origin)
open private normalize_center from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
open private normalize_local_rules normalize_hammingDist from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactNormalized
open private normalize_flip_axis mem_normalize_map normalize_axis_eq normalize_directions
  normalize_rightCenter from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoNormalized

open private swap_mem_iff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisMissingContact

private theorem normalize_star_sides {S : Finset (Q 9)} {A : Finset (Fin 9)} {o z : Q 9}
    {t m : Fin 9} (σ : Equiv.Perm (Fin 9)) (hσ : ∀ i, σ i ∈ A ↔ i ∈ baseAxes)
    (hm : σ m = t) (hbase : ∀ u, (∀ i ∉ A, u i = z i) → (u ∈ S ↔ ∃ i ∈ A, flip z i = u)) (hd : directions S z = univ.erase t) :
    DirectStar (S.map (normalize σ o).toEmbedding) (normalize σ o z) m := by
  constructor
  · intro u hu
    obtain ⟨x, rfl⟩ := (normalize σ o).surjective u
    have hx : ∀ j ∉ A, x j = z j := by
      intro j hj
      have hi : σ.symm j ∉ baseAxes := by
        intro hi
        exact hj (by simpa only [Equiv.apply_symm_apply] using (hσ (σ.symm j)).mpr hi)
      have he := (normalize_axis_eq σ o x z (σ.symm j)).mp (hu _ hi)
      simpa only [Equiv.apply_symm_apply] using he
    rw [mem_normalize_map, hbase x hx]
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨σ.symm j, (hσ _).mp (by simpa only [Equiv.apply_symm_apply] using hj), ?_⟩
      symm
      simpa only [Equiv.apply_symm_apply] using normalize_flip_axis σ o z (σ.symm j)
    · rintro ⟨i, hi, he⟩
      exact ⟨σ i, (hσ i).mpr hi, (normalize σ o).injective
        ((normalize_flip_axis σ o z i).trans he)⟩
  · rw [normalize_directions, hd, map_erase, univ_map_equiv_to_embedding]
    change univ.erase (σ.symm t) = univ.erase m
    rw [← hm, Equiv.symm_apply_apply]

private theorem missing_axis {S : Finset (Q 9)} {A : Finset (Fin 9)} {z : Q 9}
    (hsub : A ⊆ directions S z) (h8 : (directions S z).card = 8) :
    ∃ t ∉ A, directions S z = univ.erase t := by
  have h1 : ((univ : Finset (Fin 9)) \ directions S z).card = 1 := by
    rw [card_sdiff_of_subset (subset_univ _), h8] <;> simp
  obtain ⟨t, ht⟩ := card_eq_one.mp h1
  have htS : t ∉ directions S z := (mem_sdiff.mp (ht.symm ▸ mem_singleton_self t)).2
  refine ⟨t, fun h => htS (hsub h), ?_⟩
  ext j
  have he : j = t ↔ j ∉ directions S z := by
    have h := Finset.ext_iff.mp ht j
    simpa only [mem_sdiff, mem_univ, true_and, mem_singleton] using h.symm
  simp only [mem_erase, mem_univ, and_true]
  exact not_not.symm.trans (not_congr he).symm

open Classical in
/-- Normalize the star centres and missing outside axes using one cube
translation and one axis permutation. The distinguished attachment axis is preserved by the coordinate permutation. -/
theorem exists_normalized_pendant_stars {C D : Finset (Q 9)}
    {A : Finset (Fin 9)} {hub : Fin 9} {b : Bool} {z : Q 9}
    (hA : A.card = 4) (hHub : hub ∈ A) (hz : parity z = !b)
    (hclosed : ∀ i j : Fin 9, ({i,j} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 →
      (i ∈ A → i ≠ hub → j ∈ A) ∧ (j ∈ A → j ≠ hub → i ∈ A))
    (hC : ∀ u, (∀ i ∉ A, u i = z i) → (u ∈ C ↔ ∃ i ∈ A, flip z i = u))
    (hD : ∀ u, (∀ i ∉ A, u i = A.toList.foldl flip z i) →
      (u ∈ D ↔ ∃ i ∈ A, flip (A.toList.foldl flip z) i = u))
    (hsubC : A ⊆ directions C z) (hsubD : A ⊆ directions D (A.toList.foldl flip z))
    (h8C : (directions C z).card = 8) (h8D : (directions D (A.toList.foldl flip z)).card = 8)
    (hlC : LocalRules C) (hlD : LocalRules D)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y) :
    ∃ (C' D' : Finset (Q 9)) (m : Fin 9), (m = 4 ∨ m = 5) ∧
      DirectStar C' origin 4 ∧ DirectStar D' rightCenter m ∧
      LocalRules C' ∧ LocalRules D' ∧
      (∀ x ∈ C', ∀ y ∈ D', 2 ≤ hammingDist x y) ∧
      (∀ i j : Fin 9, ({i,j} : Finset (Fin 9)) ∈ minimumDisplacements C' D' true 2 →
        (i.val < 3 → j ∈ baseAxes) ∧ (j.val < 3 → i ∈ baseAxes)) := by
  obtain ⟨tC, htC, hdC⟩ := missing_axis hsubC h8C
  obtain ⟨tD, htD, hdD⟩ := missing_axis hsubD h8D
  obtain ⟨ρ, hρ, hρC, hρD⟩ := exists_ordered_axis_permutation hA htC htD
  have hρ3 : ρ 3 ∈ A := (hρ 3).mpr (by decide)
  let σ := ρ.trans (Equiv.swap (ρ 3) hub)
  have hσ (i : Fin 9) : σ i ∈ A ↔ i ∈ baseAxes :=
    (swap_mem_iff hρ3 hHub (ρ i)).trans (hρ i)
  have hσHub : σ 3 = hub := Equiv.swap_apply_left _ _
  have hσC : σ 4 = tC := by
    change Equiv.swap (ρ 3) hub (ρ 4) = tC
    have hn3 : tC ≠ ρ 3 := by
      intro he
      exact htC (he.symm ▸ hρ3)
    have hnHub : tC ≠ hub := by
      intro he
      exact htC (he.symm ▸ hHub)
    rw [hρC, Equiv.swap_apply_of_ne_of_ne hn3 hnHub]
  have hσD : σ (if tC = tD then 4 else 5) = tD := by
    change Equiv.swap (ρ 3) hub (ρ (if tC = tD then 4 else 5)) = tD
    have hn3 : tD ≠ ρ 3 := by
      intro he
      exact htD (he.symm ▸ hρ3)
    have hnHub : tD ≠ hub := by
      intro he
      exact htD (he.symm ▸ hHub)
    rw [hρD, Equiv.swap_apply_of_ne_of_ne hn3 hnHub]
  let m : Fin 9 := if tC = tD then 4 else 5
  have hm : m = 4 ∨ m = 5 := by by_cases he : tC = tD <;> simp [m, he]
  have hshift : b + parity z = true := by rw [hz]; cases b <;> rfl
  let e := normalize σ z
  let C' := C.map e.toEmbedding
  let D' := D.map e.toEmbedding
  refine ⟨C', D', m, hm, ?_, ?_, normalize_local_rules σ z C hlC,
    normalize_local_rules σ z D hlD, ?_, ?_⟩
  · simpa only [normalize_center] using normalize_star_sides (o := z) σ hσ hσC hC hdC
  · simpa only [normalize_rightCenter σ z A hσ] using
      normalize_star_sides (o := z) σ hσ hσD hD hdD
  · intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hy
    change 2 ≤ hammingDist (normalize σ z u) (normalize σ z v)
    rw [normalize_hammingDist]
    exact hsep u hu v hv
  · intro i j hm
    change ({i,j} : Finset (Fin 9)) ∈ minimumDisplacements
      (C.map e.toEmbedding) (D.map e.toEmbedding) true 2 at hm
    rw [← hshift, normalize_minimumDisplacements] at hm
    have hmap : ({σ i, σ j} : Finset (Fin 9)).map σ.symm.toEmbedding = {i,j} := by simp
    have hm' : ({σ i, σ j} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 := by
      obtain ⟨M, hM, he⟩ := mem_map.mp hm
      have hM' : M = {σ i, σ j} := by
        apply Finset.map_injective (f := σ.symm.toEmbedding)
        simpa [hmap] using he
      rwa [← hM']
    have hlow (k : Fin 9) (hk : k.val < 3) : σ k ∈ A ∧ σ k ≠ hub := by
      refine ⟨(hσ k).mpr ((show ∀ r : Fin 9, r.val < 3 → r ∈ baseAxes by decide) k hk), ?_⟩
      intro he
      have he' := σ.injective (he.trans hσHub.symm)
      subst k
      omega
    have h := hclosed (σ i) (σ j) hm'
    exact ⟨fun hi => (hσ j).mp (h.1 (hlow i hi).1 (hlow i hi).2),
      fun hj => (hσ i).mp (h.2 (hlow j hj).1 (hlow j hj).2)⟩

open Classical in
/-- The rooted contact in a low-four-axis block with three closed axes forces the two
normalized opposing stars, including their outside missing axes. -/
theorem exists_normalized_rooted_pendant_stars {C D : Finset (Q 9)}
    (h : Geometry C D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hC : ∀ j, ∃ f : Q 9 → ℝ,
      (∀ z, f z ≠ 0 ↔ z ∈ C ∧ parity z = false) ∧
      (∀ z ∉ C, weightedLinear (fun k => if k = j then 2 else 1) f z = 0))
    (hD : ∃ g : Q 9 → ℝ,
      (∀ z, g z ≠ 0 ↔ z ∈ D ∧ parity z = false) ∧
      (∀ z ∉ D, weightedLinear (fun _ => 1) g z = 0))
    (hclosed : ∀ i j : Fin 9, ({i,j} : Finset (Fin 9)) ∈ minimumDisplacements C D false 2 →
      (i.val < 3 → j ∈ baseAxes) ∧ (j.val < 3 → i ∈ baseAxes)) :
    ∃ (C' D' : Finset (Q 9)) (m : Fin 9), (m = 4 ∨ m = 5) ∧
      DirectStar C' origin 4 ∧ DirectStar D' rightCenter m ∧
      LocalRules C' ∧ LocalRules D' ∧
      (∀ x ∈ C', ∀ y ∈ D', 2 ≤ hammingDist x y) ∧
      (∀ i j : Fin 9, ({i,j} : Finset (Fin 9)) ∈ minimumDisplacements C' D' true 2 →
        (i.val < 3 → j ∈ baseAxes) ∧ (j.val < 3 → i ∈ baseAxes)) := by
  have haxes : axes = baseAxes := by decide +kernel
  have hclosed' : ∀ i j : Fin 9, ({i,j} : Finset (Fin 9)) ∈ minimumDisplacements C D false 2 →
      (i.val < 3 → j ∈ axes) ∧ (j.val < 3 → i ∈ axes) := by simpa only [haxes] using hclosed
  have htrans : ∀ ⦃i j p q : Fin 9⦄ ⦃x : Q 9⦄, p ≠ q →
      (∀ k, ({i,k} : Finset (Fin 9)) ∈ minimumDisplacements C D false 2 → k = j ∨ k = p ∨ k = q) →
      RidgeContact C D false [i] j x → RidgeContact C D false [i] j (flip (flip x p) q) := by
    intro i j p q x hpq hpartners hx
    obtain ⟨f, hf, hAf⟩ := hC j
    obtain ⟨g, hg, hAg⟩ := hD
    exact translated_contact_of_three_partners hpq h.separated hpartners f g hf hg hAf hAg hx
  obtain ⟨z, hz, hbaseC, hbaseD, hsubC, hsubD, h8C, h8D⟩ :=
    opposing_stars_full_geometry h hrC hrD hbC hbD hclosed' htrans
  have hweak (i j : Fin 9) (hm : ({i,j} : Finset (Fin 9)) ∈ minimumDisplacements C D false 2) :
      (i ∈ axes → i ≠ 3 → j ∈ axes) ∧ (j ∈ axes → j ≠ 3 → i ∈ axes) := by
    have hlow : ∀ k : Fin 9, k ∈ axes → k ≠ 3 → k.val < 3 := by decide +kernel
    exact ⟨fun hi hn => (hclosed' i j hm).1 (hlow i hi hn),
      fun hj hn => (hclosed' i j hm).2 (hlow j hj hn)⟩
  exact exists_normalized_pendant_stars (A := axes) (hub := 3) (b := false) (by decide +kernel)
    (by decide) (by simpa using hz) hweak hbaseC hbaseD hsubC hsubD h8C h8D
    h.left_rules h.right_rules h.separated

#print axioms exists_normalized_rooted_pendant_stars

#print axioms exists_normalized_pendant_stars

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9PendantCliqueNormalization
