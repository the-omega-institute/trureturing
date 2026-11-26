/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoNormalized
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoNormalized
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Cube translations and axis permutations give two opposing-star cases for tight distance-two contact. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactNormalized
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter

/-! Cube normalization for the two direct tight opposing-star degree cases. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoNormalized

open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip IsBalanced)
open BalancedCubeComponentBoundary (directions mem_directions regular_directions exterior_even)
open BalancedCubeGirth (no_selected_square)
open Q9IsotropicHuang (parity)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9SharedContactNormalized (LocalRules)
open Q9TightDistanceTwoCenter (TightStarSide tight_distance_two_cell_of_signed_defect)
open Q9WeightedSaturation (defect signedBiadjacency)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
  (normalize origin)
open private normalize_center normalize_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
open private normalize_hammingDist normalize_local_rules from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactNormalized
open private differingAxes foldl_flip_apply mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private diff_pair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar

/-- The low four axes of the direct certificate encoding. -/
def baseAxes : Finset (Fin 9) := univ.filter (fun i => i.val < 4)

/-- The vertex with mask fifteen in the direct encoding. -/
def rightCenter : Q 9 := fun i => decide (i ∈ baseAxes)

/-- The number of exterior bits in a normalized vertex. -/
def exteriorShell (x : Q 9) : ℕ := (differingAxes origin x \ baseAxes).card

theorem exteriorShell_eq_zero_iff (x : Q 9) :
    exteriorShell x = 0 ↔ ∀ i ∉ baseAxes, x i = false := by
  unfold exteriorShell
  rw [card_eq_zero, eq_empty_iff_forall_notMem]
  simp only [mem_sdiff]
  have haxis (i : Fin 9) : i ∈ differingAxes origin x ↔ false ≠ x i := by
    exact ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  constructor
  · intro h i hi
    by_contra hne
    exact h i ⟨(haxis i).mpr (Ne.symm hne), hi⟩
  · rintro h i ⟨hd, hi⟩
    exact (haxis i).mp hd (h i hi).symm

private theorem swap_mem_iff_of_not_mem {A : Finset (Fin 9)} {a b : Fin 9}
    (ha : a ∉ A) (hb : b ∉ A) (i : Fin 9) : Equiv.swap a b i ∈ A ↔ i ∈ A := by
  by_cases hia : i = a
  · subst i
    simp [ha, hb]
  · by_cases hib : i = b
    · subst i
      simp [ha, hb]
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib]

/-- The axis permutation sends the low four axes to `A`. It sends the ordered
missing axes at positions four and either four or five to their actual labels. -/
theorem exists_ordered_axis_permutation {A : Finset (Fin 9)} {tC tD : Fin 9}
    (hA : A.card = 4) (htC : tC ∉ A) (htD : tD ∉ A) :
    ∃ σ : Equiv.Perm (Fin 9), (∀ i, σ i ∈ A ↔ i ∈ baseAxes) ∧
      σ 4 = tC ∧ σ (if tC = tD then 4 else 5) = tD := by
  have hcard : baseAxes.card = A.card := (show baseAxes.card = 4 by decide).trans hA.symm
  obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_map_finset_eq baseAxes A hcard
  have hmem (i : Fin 9) : ρ i ∈ A ↔ i ∈ baseAxes := by
    rw [← hρ, mem_map_equiv, Equiv.symm_apply_apply]
  have h4 : (4 : Fin 9) ∉ baseAxes := by decide
  have h5 : (5 : Fin 9) ∉ baseAxes := by decide
  let ρ₁ := ρ.trans (Equiv.swap (ρ 4) tC)
  have hρ₁ (i : Fin 9) : ρ₁ i ∈ A ↔ i ∈ baseAxes :=
    (swap_mem_iff_of_not_mem (fun h => h4 ((hmem 4).mp h)) htC (ρ i)).trans (hmem i)
  have hρ₁4 : ρ₁ 4 = tC := Equiv.swap_apply_left _ _
  by_cases he : tC = tD
  · exact ⟨ρ₁, hρ₁, hρ₁4, by simpa only [ite_eq_left he] using hρ₁4.trans he⟩
  · let σ := ρ₁.trans (Equiv.swap (ρ₁ 5) tD)
    have hne : tC ≠ ρ₁ 5 := by
      rw [← hρ₁4]
      exact fun h => (by decide : (4 : Fin 9) ≠ 5) (ρ₁.injective h)
    refine ⟨σ, fun i => ?_, ?_, ?_⟩
    · exact (swap_mem_iff_of_not_mem (fun h => h5 ((hρ₁ 5).mp h)) htD (ρ₁ i)).trans (hρ₁ i)
    · change Equiv.swap (ρ₁ 5) tD (ρ₁ 4) = tC
      rw [hρ₁4, Equiv.swap_apply_of_ne_of_ne hne he]
    · rw [ite_eq_right he]
      exact Equiv.swap_apply_left _ _

private theorem normalize_flip_axis (σ : Equiv.Perm (Fin 9)) (o x : Q 9) (i : Fin 9) :
    normalize σ o (flip x (σ i)) = flip (normalize σ o x) i := by
  simpa only [Equiv.symm_symm, Equiv.symm_apply_apply] using normalize_flip σ.symm o x (σ i)

private theorem mem_normalize_map (σ : Equiv.Perm (Fin 9)) (o : Q 9)
    (S : Finset (Q 9)) (x : Q 9) :
    normalize σ o x ∈ S.map (normalize σ o).toEmbedding ↔ x ∈ S := by
  rw [mem_map_equiv, Equiv.symm_apply_apply]

private theorem normalize_axis_eq (σ : Equiv.Perm (Fin 9)) (o x y : Q 9) (i : Fin 9) :
    normalize σ o x i = normalize σ o y i ↔ x (σ i) = y (σ i) := by
  change ((x (σ i) != o (σ i)) = (y (σ i) != o (σ i))) ↔ _
  cases x (σ i) <;> cases y (σ i) <;> cases o (σ i) <;> decide

theorem normalize_differingAxes (σ : Equiv.Perm (Fin 9)) (o x y : Q 9) :
    differingAxes (normalize σ o x) (normalize σ o y) =
      (differingAxes x y).map σ.symm.toEmbedding := by
  ext i
  rw [mem_map_equiv, Equiv.symm_symm]
  simp only [differingAxes, mem_filter, mem_univ, true_and]
  exact not_congr (normalize_axis_eq σ o x y i)

theorem parity_normalize (σ : Equiv.Perm (Fin 9)) (o x : Q 9) :
    parity (normalize σ o x) = parity x + parity o := by
  change (∑ i : Fin 9, (x (σ i) != o (σ i))) = (∑ i : Fin 9, x i) + (∑ i : Fin 9, o i)
  calc
    _ = ∑ i : Fin 9, (x (σ i) + o (σ i)) := by
      apply sum_congr rfl
      intro i _
      cases x (σ i) <;> cases o (σ i) <;> rfl
    _ = _ := by rw [sum_add_distrib, Equiv.sum_comp σ x, Equiv.sum_comp σ o]

private theorem parity_normalize_eq (σ : Equiv.Perm (Fin 9)) (o x : Q 9) (b : Bool) :
    parity (normalize σ o x) = b + parity o ↔ parity x = b := by
  rw [parity_normalize]
  generalize parity x = p
  generalize parity o = q
  cases p <;> cases q <;> cases b <;> decide

/-- A contact family is transported by the inverse axis permutation and the
parity shift of the chosen origin. This applies at every contact distance. -/
theorem normalize_minimumDisplacements (σ : Equiv.Perm (Fin 9)) (o : Q 9)
    (C D : Finset (Q 9)) (b : Bool) (d : ℕ) :
    minimumDisplacements (C.map (normalize σ o).toEmbedding)
        (D.map (normalize σ o).toEmbedding) (b + parity o) d =
      (minimumDisplacements C D b d).map (mapEmbedding σ.symm.toEmbedding).toEmbedding := by
  ext M
  rw [mem_map (s := minimumDisplacements C D b d), mem_minimumDisplacements]
  constructor
  · rintro ⟨u, hu, v, hv, hp, hd, hm⟩
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hu
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hv
    exact ⟨differingAxes x y, mem_minimumDisplacements.mpr ⟨x, hx, y, hy,
      (parity_normalize_eq σ o x b).mp hp, (normalize_hammingDist σ o x y).symm.trans hd, rfl⟩,
      (normalize_differingAxes σ o x y).symm.trans hm⟩
  · rintro ⟨T, hT, hm⟩
    obtain ⟨x, hx, y, hy, hp, hd, he⟩ := mem_minimumDisplacements.mp hT
    have hmask : (differingAxes x y).map σ.symm.toEmbedding = M := by
      rw [he]
      exact hm
    exact ⟨normalize σ o x, (mem_normalize_map σ o C x).mpr hx,
      normalize σ o y, (mem_normalize_map σ o D y).mpr hy,
      (parity_normalize_eq σ o x b).mpr hp, (normalize_hammingDist σ o x y).trans hd,
      (normalize_differingAxes σ o x y).trans hmask⟩

private theorem normalize_directions (σ : Equiv.Perm (Fin 9)) (o x : Q 9) (C : Finset (Q 9)) :
    directions (C.map (normalize σ o).toEmbedding) (normalize σ o x) =
      (directions C x).map σ.symm.toEmbedding := by
  ext i
  rw [mem_directions, ← normalize_flip_axis, mem_normalize_map, mem_map_equiv, Equiv.symm_symm]
  exact (mem_directions C x (σ i)).symm

private theorem normalize_baseAxes (σ : Equiv.Perm (Fin 9)) (A : Finset (Fin 9))
    (hσ : ∀ i, σ i ∈ A ↔ i ∈ baseAxes) : A.map σ.symm.toEmbedding = baseAxes := by
  ext i
  rw [mem_map_equiv, Equiv.symm_symm]
  exact hσ i

private theorem normalize_rightCenter (σ : Equiv.Perm (Fin 9)) (z : Q 9) (A : Finset (Fin 9))
    (hσ : ∀ i, σ i ∈ A ↔ i ∈ baseAxes) :
    normalize σ z (A.toList.foldl flip z) = rightCenter := by
  funext i
  change ((A.toList.foldl flip z (σ i) != z (σ i)) = decide (i ∈ baseAxes))
  rw [foldl_flip_apply _ (nodup_toList _)]
  by_cases hi : i ∈ baseAxes
  · have hmem := mem_toList.mpr ((hσ i).mpr hi)
    rw [ite_eq_left hmem, decide_eq_true hi]
    cases z (σ i) <;> rfl
  · have hmem : σ i ∉ A.toList := fun hmem => hi ((hσ i).mp (mem_toList.mp hmem))
    rw [ite_eq_right hmem, decide_eq_false hi]
    cases z (σ i) <;> rfl

theorem normalize_exteriorShell (σ : Equiv.Perm (Fin 9)) (z x : Q 9) (A : Finset (Fin 9))
    (hσ : ∀ i, σ i ∈ A ↔ i ∈ baseAxes) :
    exteriorShell (normalize σ z x) = (differingAxes z x \ A).card := by
  unfold exteriorShell
  rw [← normalize_center σ z, normalize_differingAxes, ← normalize_baseAxes σ A hσ,
    ← Finset.map_sdiff, card_map]

/-- Unit-clause geometry for either star. `missing` is an absolute axis. -/
structure DirectStar (S : Finset (Q 9)) (root : Q 9) (missing : Fin 9) : Prop where
  base : ∀ x, (∀ i ∉ baseAxes, x i = root i) → (x ∈ S ↔ ∃ i ∈ baseAxes, flip root i = x)
  center_directions : directions S root = univ.erase missing

/-- The exterior unit clauses test whether the flip axis is the missing one. -/
theorem DirectStar.external_neighbor {S : Finset (Q 9)} {root : Q 9} {missing : Fin 9}
    (h : DirectStar S root missing) (i : Fin 9) : flip root i ∈ S ↔ i ≠ missing := by
  rw [← mem_directions, h.center_directions, mem_erase]
  simp

private theorem normalize_directStar {S : Finset (Q 9)} {A : Finset (Fin 9)} {o z : Q 9}
    {t m : Fin 9} (σ : Equiv.Perm (Fin 9)) (hσ : ∀ i, σ i ∈ A ↔ i ∈ baseAxes)
    (hm : σ m = t) (h : TightStarSide S A z) (hd : directions S z = univ.erase t) :
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
    rw [mem_normalize_map, h.base x hx]
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

/-- The geometric inputs of the direct degree clauses, valid on the entire
cube. In the generator the degree and square clauses use shell two and the
cross-side clauses use shell three. -/
structure DirectGeometry (C D : Finset (Q 9)) (rightMissing : Fin 9) : Prop where
  right_missing : rightMissing = 4 ∨ rightMissing = 5
  left_star : DirectStar C origin 4
  right_star : DirectStar D rightCenter rightMissing
  left_rules : LocalRules C
  right_rules : LocalRules D
  separated : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y
  odd_masks : minimumDisplacements C D true 2 = baseAxes.powersetCard 2

/-- Both sets of base unit clauses concern the same shell-zero cell. -/
theorem DirectGeometry.base_membership {C D : Finset (Q 9)} {m : Fin 9}
    (h : DirectGeometry C D m) {x : Q 9} (hx : exteriorShell x = 0) :
    (x ∈ C ↔ ∃ i ∈ baseAxes, flip origin i = x) ∧
    (x ∈ D ↔ ∃ i ∈ baseAxes, flip rightCenter i = x) := by
  have hzero := (exteriorShell_eq_zero_iff x).mp hx
  refine ⟨h.left_star.base x hzero, h.right_star.base x ?_⟩
  intro i hi
  simpa [rightCenter, hi] using hzero i hi

/-- The cross-side clauses for mask zero and all one-bit masks. -/
theorem DirectGeometry.forbidden_close {C D : Finset (Q 9)} {m : Fin 9}
    (h : DirectGeometry C D m) {x y : Q 9} (hx : x ∈ C) (hd : hammingDist x y ≤ 1) : y ∉ D := by
  intro hy
  have hsep := h.separated x hx y hy
  omega

/-- The parity of all nine neighbors is the occupancy bit. The intermediate
XOR variables in the direct clauses can use the prefix parities. -/
theorem occupied_iff_odd_degree {S : Finset (Q 9)} (h : LocalRules S) (x : Q 9) :
    x ∈ S ↔ Odd (directions S x).card := by
  constructor
  · intro hx
    rw [h.occupied_degree x hx]
    decide
  · intro ho
    by_contra hx
    exact (Nat.not_odd_iff_even.mpr (h.exterior_degree x hx)) ho

theorem DirectGeometry.odd_contact_axes {C D : Finset (Q 9)} {m : Fin 9}
    (h : DirectGeometry C D m) {x y : Q 9} (hx : x ∈ C) (hy : y ∈ D)
    (hp : parity x = true) (hd : hammingDist x y = 2) : differingAxes x y ⊆ baseAxes := by
  have hmem : differingAxes x y ∈ minimumDisplacements C D true 2 :=
    mem_minimumDisplacements.mpr ⟨x, hx, y, hy, hp, hd, rfl⟩
  rw [h.odd_masks] at hmem
  exact (mem_powersetCard.mp hmem).1

/-- The generator bans every two-bit mask with at least one exterior bit
when the left vertex is odd. -/
theorem DirectGeometry.forbidden_pair_flip {C D : Finset (Q 9)} {m : Fin 9}
    (h : DirectGeometry C D m) {x : Q 9} {i j : Fin 9} (hx : x ∈ C) (hp : parity x = true)
    (hij : i ≠ j) (hext : i ∉ baseAxes ∨ j ∉ baseAxes) : flip (flip x i) j ∉ D := by
  have hmask := diff_pair x hij
  have hd : hammingDist x (flip (flip x i) j) = 2 := by
    change (differingAxes x (flip (flip x i) j)).card = 2
    rw [hmask, card_pair hij]
  intro hy
  have hsub := h.odd_contact_axes hx hy hp hd
  rw [hmask] at hsub
  exact hext.elim (fun hi => hi (hsub (by simp))) (fun hj => hj (hsub (by simp)))

/-- One translation and one common axis permutation send the actual opposing
stars to the direct certificate geometry, with the ordered case recorded. -/
theorem exists_normalized_tight_distance_two {C D : Finset (Q 9)} {A : Finset (Fin 9)}
    {b : Bool} {z : Q 9} (hA : A.card = 4) (hz : parity z = !b)
    (hfamily : minimumDisplacements C D b 2 = A.powersetCard 2)
    (hC : TightStarSide C A z) (hD : TightStarSide D A (A.toList.foldl flip z))
    (hlC : LocalRules C) (hlD : LocalRules D)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y) :
    ∃ (tC tD : Fin 9) (σ : Equiv.Perm (Fin 9)),
      let m : Fin 9 := if tC = tD then 4 else 5
      let e := normalize σ z
      (∀ i, σ i ∈ A ↔ i ∈ baseAxes) ∧ σ 4 = tC ∧ σ m = tD ∧
      directions C z = univ.erase tC ∧ directions D (A.toList.foldl flip z) = univ.erase tD ∧
      e z = origin ∧ e (A.toList.foldl flip z) = rightCenter ∧
      (∀ x, parity (e x) = true ↔ parity x = b) ∧
      (∀ x, exteriorShell (e x) = (differingAxes z x \ A).card) ∧
      DirectGeometry (C.map e.toEmbedding) (D.map e.toEmbedding) m := by
  obtain ⟨tC, htC, hdC, _⟩ := hC.missing
  obtain ⟨tD, htD, hdD, _⟩ := hD.missing
  obtain ⟨σ, hσ, hσC, hσD⟩ := exists_ordered_axis_permutation hA htC htD
  let m : Fin 9 := if tC = tD then 4 else 5
  have hm : m = 4 ∨ m = 5 := by
    by_cases he : tC = tD <;> simp [m, he]
  have hleft := normalize_center σ z
  have hright := normalize_rightCenter σ z A hσ
  have hshift : b + parity z = true := by rw [hz]; cases b <;> rfl
  have hodd (x : Q 9) : parity (normalize σ z x) = true ↔ parity x = b :=
    (by rw [← hshift]; exact parity_normalize_eq σ z x b)
  refine ⟨tC, tD, σ, hσ, hσC, hσD, hdC, hdD, hleft, hright, hodd,
    fun x => normalize_exteriorShell σ z x A hσ, ?_⟩
  refine ⟨hm, ?_, ?_, normalize_local_rules σ z C hlC, normalize_local_rules σ z D hlD, ?_, ?_⟩
  · simpa only [hleft] using normalize_directStar (o := z) σ hσ hσC hC hdC
  · simpa only [hright] using normalize_directStar (o := z) σ hσ hσD hD hdD
  · intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hy
    change 2 ≤ hammingDist (normalize σ z u) (normalize σ z v)
    rw [normalize_hammingDist]
    exact hsep u hu v hv
  · rw [← hshift, normalize_minimumDisplacements, hfamily, ← powersetCard_map,
      normalize_baseAxes σ A hσ]

open Classical in
/-- A six-mask slice of balanced cubic components with universally singular
signed defects supplies one of the two normalized direct degree cases. -/
theorem exists_direct_geometry_of_signed_defect {C D : Finset (Q 9)} {b : Bool}
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (htight : (minimumDisplacements C D b 2).card = 6) :
    ∃ (z : Q 9) (σ : Equiv.Perm (Fin 9)) (m : Fin 9),
      DirectGeometry (C.map (normalize σ z).toEmbedding) (D.map (normalize σ z).toEmbedding) m := by
  have hlocal {S : Finset (Q 9)}
      (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
      (hb : IsBalanced S) : LocalRules S :=
    ⟨fun _ hx => regular_directions S hr hx, exterior_even S hr hb,
      fun _ _ _ hij hx hi hj hxy => no_selected_square hb hij hx hi hj hxy⟩
  obtain ⟨A, z, hA, hfamily, hz, hC, hD⟩ :=
    tight_distance_two_cell_of_signed_defect hsep hrC hrD hcC hcD hbC hbD hdetC hdetD htight
  obtain ⟨tC, tD, σ, _, _, _, _, _, _, _, _, _, h⟩ :=
    exists_normalized_tight_distance_two hA hz hfamily hC hD (hlocal hrC hbC) (hlocal hrD hbD) hsep
  exact ⟨z, σ, if tC = tD then 4 else 5, h⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoNormalized
