/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9NormalizeNineMasks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9NormalizeNineMasks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Fixing a low-high contact sends the absent mask to the same two coordinates in every actual five-axis family. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisMissingContact
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SquareMaskGraph

/-! Fix a realized low-high mask in the five-axis nine-mask case. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9NormalizeNineMasks

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9FiveAxisMissingContact (Geometry firstFiveAxes missingMask)
open Q9IsotropicHuang (parity)
open Q9TightDistanceTwoNormalized (normalize_minimumDisplacements)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
  (normalize)
open private normalize_chosen_realized_mask from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisMissingContact

open Q9SquareMaskGraph (activeAxes maskGraph card_edges)
open private mem_axes from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.MinimumContactDisplacementCount

open Classical in
/-- Nine edges and minimum degree three leave two shapes to consider. Either
six axes are active, or five are active and exactly one pair is missing. -/
theorem six_axes_or_delete_one
    (F : Finset (Finset (Fin 9))) (hF : F.card = 9)
    (hsize : ∀ T ∈ F, T.card = 2)
    (hdeg : ∀ a, 3 ≤ (maskGraph F).degree a) :
    (activeAxes F).card = 6 ∨ ∃ P ∈ (activeAxes F).powersetCard 2,
      (activeAxes F).card = 5 ∧ F = (activeAxes F).powersetCard 2 \ {P} := by
  let A := activeAxes F
  let G := maskGraph F
  have hsub : F ⊆ A.powersetCard 2 := fun T hT =>
    mem_powersetCard.mpr ⟨fun i hi => mem_axes.mpr ⟨T, hT, hi⟩, hsize T hT⟩
  have hcap := card_le_card hsub
  rw [card_powersetCard, hF] at hcap
  have hlower : 5 ≤ A.card := by
    by_contra! hs
    have hc := Nat.choose_le_choose 2 (show A.card ≤ 4 by omega)
    have he : Nat.choose 4 2 = 6 := by decide
    rw [he] at hc
    omega
  have hupper : A.card ≤ 6 := by
    have hsum : (∑ a : A, 3) ≤ ∑ a : A, G.degree a :=
      sum_le_sum fun a _ => hdeg a
    rw [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul,
      G.sum_degrees_eq_twice_card_edges, card_edges F hsize, hF] at hsum
    change A.card * 3 ≤ 2 * 9 at hsum
    omega
  by_cases hs : A.card = 6
  · exact Or.inl hs
  have hA : A.card = 5 := by omega
  have hrem : (A.powersetCard 2 \ F).card = 1 := by
    rw [card_sdiff_of_subset hsub, card_powersetCard, hA, hF]
    decide
  obtain ⟨P, hP⟩ := card_eq_one.mp hrem
  have hp : P ∈ A.powersetCard 2 := (mem_sdiff.mp (hP.symm ▸ mem_singleton_self P)).1
  refine Or.inr ⟨P, hp, hA, ?_⟩
  change F = A.powersetCard 2 \ {P}
  rw [← hP, Finset.sdiff_sdiff_eq_self hsub]

open Classical in
/-- Choose a contact through one endpoint of the missing mask. Coordinate
permutation and translation then put the missing mask at axes 1 and 2 and
the realized root contact at axes 0 and 1. -/
theorem exists_normalized_nine_mask_contact
    {C D : Finset (Q 9)} {b : Bool} {A P : Finset (Fin 9)}
    (hA : A.card = 5) (hP : P ∈ A.powersetCard 2)
    (hfamily : minimumDisplacements C D b 2 = A.powersetCard 2 \ {P})
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) :
    ∃ (x : Q 9) (σ : Equiv.Perm (Fin 9)),
      let X := C.map (normalize σ x).toEmbedding
      let Y := D.map (normalize σ x).toEmbedding
      parity x = b ∧ Geometry X Y ∧
        minimumDisplacements X Y false 2 = firstFiveAxes.powersetCard 2 \ {missingMask} := by
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hP
  have hpositive : 0 < (A \ P).card := by
    rw [card_sdiff_of_subset hsub, hA, hcard]
    decide
  obtain ⟨k, hk⟩ := card_pos.mp hpositive
  obtain ⟨hkA, hkP⟩ := mem_sdiff.mp hk
  obtain ⟨i, j, hij, hpair⟩ := card_eq_two.mp hcard
  have hiP : i ∈ P := by simp [hpair]
  have hjP : j ∈ P := by simp [hpair]
  have hki : k ≠ i := fun h => hkP (h.symm ▸ hiP)
  have hkj : k ≠ j := fun h => hkP (h.symm ▸ hjP)
  have ht : ({k, i} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 := by
    rw [hfamily]
    refine mem_sdiff.mpr ⟨mem_powersetCard.mpr
      ⟨insert_subset hkA (singleton_subset_iff.mpr (hsub hiP)), card_pair hki⟩, ?_⟩
    intro he
    exact hkP ((mem_singleton.mp he) ▸ mem_insert_self _ _)
  obtain ⟨x, _, σ, _, _, hpar, _, _, _, hAmap, hPmap, _, _, _, hgeometry⟩ :=
    normalize_chosen_realized_mask hA hkA (hsub hiP) (hsub hjP)
      hki hkj hij hpair ht hsep hrC hrD hbC hbD
  refine ⟨x, σ, hpar, hgeometry, ?_⟩
  have hshift : b + parity x = false := by rw [hpar]; cases b <;> rfl
  rw [← hshift, normalize_minimumDisplacements, hfamily, Finset.map_sdiff, ← powersetCard_map]
  simp only [map_singleton, hAmap]
  change firstFiveAxes.powersetCard 2 \ {P.map σ.symm.toEmbedding} =
    firstFiveAxes.powersetCard 2 \ {missingMask}
  rw [hPmap]

#print axioms exists_normalized_nine_mask_contact

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9NormalizeNineMasks
