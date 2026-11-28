import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisMissingContact
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.Sum

/-! Extend a labeling of the active axes and translate a chosen contact to the roots. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskRootNormalization

open Finset
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeComponentBoundary (regular_directions exterior_even)
open BalancedCubeGirth (no_selected_square)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
  (normalize origin)
open Q9FiveAxisMissingContact (Geometry rightRoot)
open Q9IsotropicHuang (parity)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9SharedContactNormalized (LocalRules)
open Q9TightDistanceTwoNormalized (normalize_differingAxes normalize_minimumDisplacements)
open private normalize_center from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
open private normalize_hammingDist normalize_local_rules from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactNormalized
open private differingAxes mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private diff_pair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar

private theorem extend_axes {k : ℕ} (hk : k ≤ 9) (e : Fin k ↪ Fin 9) :
    ∃ σ : Equiv.Perm (Fin 9), ∀ i, σ (Fin.castLEEmb hk i) = e i := by
  let s := (univ : Finset (Fin k)).map (Fin.castLEEmb hk)
  let f (a : Fin 9) : Fin 9 := if ha : a.val < k then e ⟨a.val, ha⟩ else a
  have hcard : Fintype.card (Fin 9) = (univ : Finset (Fin 9)).card :=
    card_univ.symm
  have hinj : Set.InjOn f (s : Set (Fin 9)) := by
    intro a ha b hb he
    obtain ⟨i, _, rfl⟩ := mem_map.mp (show a ∈ s from ha)
    obtain ⟨j, _, rfl⟩ := mem_map.mp (show b ∈ s from hb)
    have h : e i = e j := by
      simpa only [f, Fin.castLEEmb, Function.Embedding.coeFn_mk, Fin.castLE,
        dif_pos i.isLt, dif_pos j.isLt] using he
    exact congrArg (Fin.castLEEmb hk) (e.injective h)
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq hcard
    (s := s) (f := f) (subset_univ _) hinj
  refine ⟨g.trans (Equiv.subtypeUnivEquiv Finset.mem_univ), fun i => ?_⟩
  have h := hg (Fin.castLEEmb hk i) (mem_map.mpr ⟨i, mem_univ _, rfl⟩)
  exact h.trans (dif_pos i.isLt)

open Classical in
/-- Retain the coordinate frame of the actual contact, allowing further
invariants of the two supports to be carried by the same cube isometry. -/
theorem normalize_root_mapped
    {C D : Finset (Q 9)} {b : Bool} (σ : Equiv.Perm (Fin 9)) {x y : Q 9}
    (hx : x ∈ C) (hy : y ∈ D) (hp : parity x = b)
    (hxy : differingAxes x y = {σ 0, σ 1})
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) :
    let e := normalize σ x
    Geometry (C.map e.toEmbedding) (D.map e.toEmbedding) ∧
      minimumDisplacements (C.map e.toEmbedding) (D.map e.toEmbedding) false 2 =
        (minimumDisplacements C D b 2).map (mapEmbedding σ.symm.toEmbedding).toEmbedding := by
  let e := normalize σ x
  have hleft : e x = origin := normalize_center σ x
  have hmask : differingAxes origin (e y) = differingAxes origin rightRoot := by
    calc
      _ = differingAxes (e x) (e y) := by rw [hleft]
      _ = ({σ 0, σ 1} : Finset (Fin 9)).map σ.symm.toEmbedding := by
        change differingAxes (normalize σ x x) (normalize σ x y) = _
        rw [normalize_differingAxes, hxy]
      _ = differingAxes origin rightRoot := by
        rw [rightRoot, diff_pair origin (by decide : (0 : Fin 9) ≠ 1)]
        simp only [map_insert, map_singleton, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
  have hright : e y = rightRoot := by
    funext i
    have hi : i ∈ differingAxes origin (e y) ↔ i ∈ differingAxes origin rightRoot := by
      rw [hmask]
    change (i ∈ univ.filter (fun z => false ≠ e y z) ↔
      i ∈ univ.filter (fun z => false ≠ rightRoot z)) at hi
    simp only [mem_filter, mem_univ, true_and] at hi
    cases h₁ : e y i <;> cases h₂ : rightRoot i <;> simp [h₁, h₂] at hi ⊢
  have hlocal {S : Finset (Q 9)}
      (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
      (hb : IsBalanced S) : LocalRules (S.map e.toEmbedding) :=
    normalize_local_rules σ x S
      ⟨fun _ hs => regular_directions S hr hs, exterior_even S hr hb,
        fun _ _ _ hij hs hi hj hs' => no_selected_square hb hij hs hi hj hs'⟩
  refine ⟨⟨mem_map.mpr ⟨x, hx, hleft⟩, mem_map.mpr ⟨y, hy, hright⟩,
      hlocal hrC hbC, hlocal hrD hbD, ?_⟩, ?_⟩
  · intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := mem_map.mp hu
    obtain ⟨v', hv', rfl⟩ := mem_map.mp hv
    change 2 ≤ hammingDist (normalize σ x u') (normalize σ x v')
    rw [normalize_hammingDist]
    exact hsep u' hu' v' hv'
  · have hshift : b + parity x = false := by rw [hp]; cases b <;> rfl
    rw [← hshift, normalize_minimumDisplacements]

open Classical in
/-- Any prescribed labeling placing a realized mask at axes zero and one
transports all the local rules and the entire mask family in one step. -/
theorem normalize_root
    {C D : Finset (Q 9)} {b : Bool} (σ : Equiv.Perm (Fin 9))
    (hroot : ({σ 0, σ 1} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) :
    ∃ X Y : Finset (Q 9), Geometry X Y ∧
      minimumDisplacements X Y false 2 =
        (minimumDisplacements C D b 2).map (mapEmbedding σ.symm.toEmbedding).toEmbedding := by
  obtain ⟨x, hx, y, hy, hp, _, hxy⟩ := mem_minimumDisplacements.mp hroot
  exact ⟨_, _, normalize_root_mapped σ hx hy hp hxy hsep hrC hrD hbC hbD⟩

open Classical in
/-- A checked list of contact masks determines the entire family if it has the
same cardinality. Normalization carries both the list and the local geometry. -/
theorem normalize_labelled_family
    {C D : Finset (Q 9)} {b : Bool} (σ : Equiv.Perm (Fin 9))
    (M : Finset (Finset (Fin 9)))
    (hroot : ({σ 0, σ 1} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2)
    (hM : ∀ t ∈ M, t.map σ.toEmbedding ∈ minimumDisplacements C D b 2)
    (hcard : M.card = (minimumDisplacements C D b 2).card)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) :
    ∃ X Y : Finset (Q 9), Geometry X Y ∧ minimumDisplacements X Y false 2 = M := by
  obtain ⟨X, Y, hgeo, hmap⟩ := normalize_root σ hroot hsep hrC hrD hbC hbD
  refine ⟨X, Y, hgeo, (eq_of_subset_of_card_le ?_ ?_).symm⟩
  · intro t ht
    rw [hmap]
    refine mem_map.mpr ⟨t.map σ.toEmbedding, hM t ht, ?_⟩
    ext i
    simp [Finset.mapEmbedding_apply]
  · rw [hmap, card_map, hcard]

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskRootNormalization
