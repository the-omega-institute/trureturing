/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisMissingContact
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisMissingContact
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Normalize a realized eight-mask contact by the cube isometry group. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoNormalized

/-! The five-axis distance-two normalization for Hong–Wu–Xia Q9 Problem 2. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisMissingContact

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip)
open BalancedCubeComponentBoundary (regular_directions exterior_even)
open BalancedCubeGirth (no_selected_square)
open Q9IsotropicHuang (parity)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9SharedContactNormalized (LocalRules)
open Q9TightDistanceTwoNormalized (normalize_differingAxes normalize_minimumDisplacements)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
  (normalize origin)
open private normalize_center from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
open private normalize_local_rules normalize_hammingDist from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactNormalized
open private differingAxes mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private diff_pair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar
/-- The axes permitted for contacts in the normalized even slice. -/
def firstFiveAxes : Finset (Fin 9) := {0, 1, 2, 3, 4}

private def rootMask : Finset (Fin 9) := {0, 1}

def missingMask : Finset (Fin 9) := {1, 2}

/-- The right endpoint of the chosen contact, encoded by the integer mask three. -/
def rightRoot : Q 9 := flip (flip origin 0) 1

/-- The normalized roots, local support rules, and separation for the refutation. -/
structure Geometry (C D : Finset (Q 9)) : Prop where
  left_root : origin ∈ C
  right_root : rightRoot ∈ D
  left_rules : LocalRules C
  right_rules : LocalRules D
  separated : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y

private theorem swap_mem_iff {A : Finset (Fin 9)} {a b : Fin 9}
    (ha : a ∈ A) (hb : b ∈ A) (i : Fin 9) : Equiv.swap a b i ∈ A ↔ i ∈ A := by
  by_cases hia : i = a
  · subst i
    simp [ha, hb]
  · by_cases hib : i = b
    · subst i
      simp [ha, hb]
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib]

private theorem exists_axis_permutation {A : Finset (Fin 9)} {a b c : Fin 9}
    (hA : A.card = 5) (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ σ : Equiv.Perm (Fin 9), (∀ i, σ i ∈ A ↔ i ∈ firstFiveAxes) ∧
      σ 0 = a ∧ σ 1 = b ∧ σ 2 = c := by
  have hcard : firstFiveAxes.card = A.card :=
    (show firstFiveAxes.card = 5 by decide).trans hA.symm
  obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_map_finset_eq firstFiveAxes A hcard
  have hmem (i : Fin 9) : ρ i ∈ A ↔ i ∈ firstFiveAxes := by
    rw [← hρ, mem_map_equiv, Equiv.symm_apply_apply]
  let ρ₀ := ρ.trans (Equiv.swap (ρ 0) a)
  have hmem₀ (i : Fin 9) : ρ₀ i ∈ A ↔ i ∈ firstFiveAxes :=
    (swap_mem_iff ((hmem 0).mpr (by decide)) ha (ρ i)).trans (hmem i)
  have h₀ : ρ₀ 0 = a := Equiv.swap_apply_left _ _
  let ρ₁ := ρ₀.trans (Equiv.swap (ρ₀ 1) b)
  have hmem₁ (i : Fin 9) : ρ₁ i ∈ A ↔ i ∈ firstFiveAxes :=
    (swap_mem_iff ((hmem₀ 1).mpr (by decide)) hb (ρ₀ i)).trans (hmem₀ i)
  have h₁₀ : ρ₁ 0 = a := by
    change Equiv.swap (ρ₀ 1) b (ρ₀ 0) = a
    have hne : ρ₀ 0 ≠ ρ₀ 1 := fun h => (by decide : (0 : Fin 9) ≠ 1) (ρ₀.injective h)
    have hnb : ρ₀ 0 ≠ b := by simpa only [h₀] using hab
    rw [Equiv.swap_apply_of_ne_of_ne hne hnb, h₀]
  have h₁ : ρ₁ 1 = b := Equiv.swap_apply_left _ _
  let σ := ρ₁.trans (Equiv.swap (ρ₁ 2) c)
  have hmem₂ (i : Fin 9) : σ i ∈ A ↔ i ∈ firstFiveAxes :=
    (swap_mem_iff ((hmem₁ 2).mpr (by decide)) hc (ρ₁ i)).trans (hmem₁ i)
  have hfix (i : Fin 9) (hi : i ≠ 2) (hic : ρ₁ i ≠ c) : σ i = ρ₁ i :=
    Equiv.swap_apply_of_ne_of_ne (fun h => hi (ρ₁.injective h)) hic
  exact ⟨σ, hmem₂, (hfix 0 (by decide) (by rwa [h₁₀])).trans h₁₀,
    (hfix 1 (by decide) (by rwa [h₁])).trans h₁, Equiv.swap_apply_left _ _⟩

open Classical in
private theorem normalize_chosen_realized_mask
    {C D : Finset (Q 9)} {b : Bool} {A M : Finset (Fin 9)}
    (hA : A.card = 5)
    {i j k : Fin 9} (hkA : k ∈ A) (hiA : i ∈ A) (hjA : j ∈ A)
    (hki : k ≠ i) (hkj : k ≠ j) (hij : i ≠ j) (hpair : M = {i, j})
    (hT : ({k, i} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) :
    ∃ (x y : Q 9) (σ : Equiv.Perm (Fin 9)),
      let e := normalize σ x
      x ∈ C ∧ y ∈ D ∧ parity x = b ∧ hammingDist x y = 2 ∧
      e x = origin ∧ e y = rightRoot ∧
      A.map σ.symm.toEmbedding = firstFiveAxes ∧
      M.map σ.symm.toEmbedding = missingMask ∧ σ 0 = k ∧ σ 1 = i ∧ σ 2 = j ∧
      Geometry (C.map e.toEmbedding) (D.map e.toEmbedding) := by
  obtain ⟨x, hx, y, hy, hp, hd, hxy⟩ := mem_minimumDisplacements.mp hT
  obtain ⟨σ, hσ, hσ₀, hσ₁, hσ₂⟩ :=
    exists_axis_permutation hA hkA hiA hjA hki hkj hij
  let e := normalize σ x
  have hAmap : A.map σ.symm.toEmbedding = firstFiveAxes := by
    ext t
    rw [mem_map_equiv, Equiv.symm_symm]
    exact hσ t
  have hmapPair (u v : Fin 9) :
      ({σ u, σ v} : Finset (Fin 9)).map σ.symm.toEmbedding = {u, v} := by
    simp only [map_insert, map_singleton, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
  have hTmap : ({k, i} : Finset (Fin 9)).map σ.symm.toEmbedding = rootMask := by
    simpa only [hσ₀, hσ₁, rootMask] using hmapPair 0 1
  have hMmap : M.map σ.symm.toEmbedding = missingMask := by
    simpa only [hσ₁, hσ₂, ← hpair, missingMask] using hmapPair 1 2
  have heleft : e x = origin := normalize_center σ x
  have hrootMask : differingAxes origin rightRoot = rootMask :=
    diff_pair origin (by decide : (0 : Fin 9) ≠ 1)
  have heright : e y = rightRoot := by
    have hh : differingAxes origin (e y) = differingAxes origin rightRoot := by
      calc
        differingAxes origin (e y) = differingAxes (e x) (e y) := by rw [heleft]
        _ = ({k, i} : Finset (Fin 9)).map σ.symm.toEmbedding := by
          change differingAxes (normalize σ x x) (normalize σ x y) = _
          rw [normalize_differingAxes, hxy]
        _ = differingAxes origin rightRoot := hTmap.trans hrootMask.symm
    funext t
    have ht : t ∈ differingAxes origin (e y) ↔ t ∈ differingAxes origin rightRoot := by rw [hh]
    change (t ∈ univ.filter (fun z => false ≠ e y z) ↔
      t ∈ univ.filter (fun z => false ≠ rightRoot z)) at ht
    simp only [mem_filter, mem_univ, true_and] at ht
    cases h₁ : e y t <;> cases h₂ : rightRoot t <;> simp [h₁, h₂] at ht ⊢
  have hlocal {S : Finset (Q 9)}
      (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
      (hb : IsBalanced S) : LocalRules (S.map e.toEmbedding) :=
    normalize_local_rules σ x S
      ⟨fun _ hs => regular_directions S hr hs, exterior_even S hr hb,
        fun _ _ _ hij' hs hi hj hs' => no_selected_square hb hij' hs hi hj hs'⟩
  refine ⟨x, y, σ, hx, hy, hp, hd, heleft, heright, hAmap, hMmap, hσ₀, hσ₁, hσ₂, ?_⟩
  refine ⟨mem_map.mpr ⟨x, hx, heleft⟩, mem_map.mpr ⟨y, hy, heright⟩,
    hlocal hrC hbC, hlocal hrD hbD, ?_⟩
  intro u hu v hv
  obtain ⟨u', hu', rfl⟩ := mem_map.mp hu
  obtain ⟨v', hv', rfl⟩ := mem_map.mp hv
  change 2 ≤ hammingDist (normalize σ x u') (normalize σ x v')
  rw [normalize_hammingDist]
  exact hsep u' hu' v' hv'

/-- Mask zero and all one-bit masks are forbidden at every left endpoint. -/
theorem Geometry.forbidden_close {C D : Finset (Q 9)} (h : Geometry C D)
    {x y : Q 9} (hx : x ∈ C) (hd : hammingDist x y ≤ 1) : y ∉ D := by
  intro hy
  have hsep := h.separated x hx y hy
  omega

open Classical in
/-- Choose a contact through the unique axis outside both deleted edges.
This sends an eight-mask family to a single labelled configuration. -/
theorem exists_normalized_eight_mask_contact
    {C D : Finset (Q 9)} {b : Bool} {A P R : Finset (Fin 9)}
    (hA : A.card = 5) (hP : P ∈ A.powersetCard 2) (hR : R ∈ A.powersetCard 2)
    (hPR : Disjoint P R)
    (hfamily : minimumDisplacements C D b 2 = A.powersetCard 2 \ {P, R})
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) :
    ∃ (x : Q 9) (σ : Equiv.Perm (Fin 9)),
      let X := C.map (normalize σ x).toEmbedding
      let Y := D.map (normalize σ x).toEmbedding
      Geometry X Y ∧ minimumDisplacements X Y false 2 =
        firstFiveAxes.powersetCard 2 \ {missingMask, ({3, 4} : Finset (Fin 9))} := by
  have hsP := (mem_powersetCard.mp hP).1
  have hsR := (mem_powersetCard.mp hR).1
  have hcardP := (mem_powersetCard.mp hP).2
  have hcardR := (mem_powersetCard.mp hR).2
  have hpositive : 0 < (A \ (P ∪ R)).card := by
    rw [card_sdiff_of_subset (union_subset hsP hsR), card_union_of_disjoint hPR,
      hA, hcardP, hcardR]
    decide
  obtain ⟨k, hk⟩ := card_pos.mp hpositive
  obtain ⟨hkA, hkoutside⟩ := mem_sdiff.mp hk
  have hkP : k ∉ P := fun h => hkoutside (mem_union_left _ h)
  have hkR : k ∉ R := fun h => hkoutside (mem_union_right _ h)
  obtain ⟨i, j, hij, hpair⟩ := card_eq_two.mp hcardP
  have hiP : i ∈ P := by rw [hpair]; simp
  have hjP : j ∈ P := by rw [hpair]; simp
  have hki : k ≠ i := fun h => hkP (h.symm ▸ hiP)
  have hkj : k ≠ j := fun h => hkP (h.symm ▸ hjP)
  have ht : ({k, i} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 := by
    rw [hfamily]
    refine mem_sdiff.mpr ⟨mem_powersetCard.mpr
      ⟨insert_subset hkA (singleton_subset_iff.mpr (hsP hiP)), card_pair hki⟩, ?_⟩
    intro h
    rcases mem_insert.mp h with he | he
    · exact hkP (he ▸ mem_insert_self _ _)
    · exact hkR ((mem_singleton.mp he) ▸ mem_insert_self _ _)
  obtain ⟨x, _, σ, _, _, hpar, _, _, _, hAmap, hPmap, hσ₀, hσ₁, hσ₂, hgeometry⟩ :=
    normalize_chosen_realized_mask hA hkA (hsP hiP) (hsP hjP)
      hki hkj hij hpair ht hsep hrC hrD hbC hbD
  refine ⟨x, σ, hgeometry, ?_⟩
  have hRmap : R.map σ.symm.toEmbedding = ({3, 4} : Finset (Fin 9)) := by
    apply eq_of_subset_of_card_le
    · intro t ht
      rw [mem_map_equiv, Equiv.symm_symm] at ht
      have htA : t ∈ firstFiveAxes := by
        rw [← hAmap, mem_map_equiv, Equiv.symm_symm]
        exact hsR ht
      have ht₀ : t ≠ 0 := fun h => hkR (hσ₀ ▸ (h ▸ ht))
      have ht₁ : t ≠ 1 := fun h => disjoint_left.mp hPR hiP (hσ₁ ▸ (h ▸ ht))
      have ht₂ : t ≠ 2 := fun h => disjoint_left.mp hPR hjP (hσ₂ ▸ (h ▸ ht))
      simpa [firstFiveAxes, ht₀, ht₁, ht₂] using htA
    · rw [card_map, hcardR]
      decide
  have hshift : b + parity x = false := by rw [hpar]; cases b <;> rfl
  rw [← hshift, normalize_minimumDisplacements, hfamily, Finset.map_sdiff, ← powersetCard_map]
  simp only [map_insert, map_singleton, hAmap]
  change firstFiveAxes.powersetCard 2 \ {P.map σ.symm.toEmbedding, R.map σ.symm.toEmbedding} =
    firstFiveAxes.powersetCard 2 \ {missingMask, ({3, 4} : Finset (Fin 9))}
  rw [hPmap, hRmap]

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisMissingContact
