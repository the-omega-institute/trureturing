/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverSeparation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Distinct eightfold exterior edges in Q9 have separation at least four. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverLocal
import D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport

/-! Separation of eightfold covers of the same induced cubic support in the signed nine-cube. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverSeparation

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj gamma_apply IsSwitching)
open BalancedCubeGirth (gamma_anticommute)
open BalancedCubeComponentBoundary (directions regular_directions)
open Q9EightfoldCoverLocal (eightfold_corner_rule selectedCorners transverseSign)
open private adjacent_exists_flip flip_comm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private huangMatrix huangMatrix_symmetric from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private diff diff_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private two_flip_disagreements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MixedBoundaryCollisions
open private transverseSign_unit from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverLocal
open private switching_sq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

attribute [local instance] Classical.propDecidable

/-- An exterior edge with both endpoints translated into the support along every transverse axis. -/
def EightfoldCover (C : Finset (Q 9)) (x : Q 9) (k : Fin 9) : Prop :=
  x ∉ C ∧ flip x k ∉ C ∧ ∀ i ≠ k, flip x i ∈ C ∧ flip (flip x k) i ∈ C

variable {C : Finset (Q 9)} {sigma : Q 9 → ℝ}
variable {x y : Q 9} {k l : Fin 9}

private theorem EightfoldCover.reverse (hx : EightfoldCover C x k) :
    EightfoldCover C (flip x k) k :=
  ⟨hx.2.1, by simpa only [BalancedCriticalSpectrum.flip_flip] using hx.1,
    fun i hi => by simpa only [BalancedCriticalSpectrum.flip_flip] using (hx.2.2 i hi).symm⟩

private theorem EightfoldCover.exterior_neighbor (hx : EightfoldCover C x k)
    (hy : y ∉ C) (hxy : (hypercube 9).Adj x y) : y = flip x k := by
  obtain ⟨i, rfl⟩ := adjacent_exists_flip hxy
  by_cases hi : i = k
  · rw [hi]
  · exact (hy (hx.2.2 i hi).1).elim

private theorem diff_symm (x y : Q 9) : diff x y = diff y x := by
  ext i
  simp [diff, ne_comm]

private theorem flip_decreases_distance {i : Fin 9} (hi : i ∈ diff x y) :
    hammingDist (flip x i) y + 1 = hammingDist x y := by
  change (diff (flip x i) y).card + 1 = (diff x y).card
  rw [diff_flip, ite_eq_left hi, Finset.card_erase_add_one hi]

private theorem eq_double_flip {i j : Fin 9} (hij : i ≠ j) (h : diff x y = {i, j}) :
    y = flip (flip x i) j := by
  have hd : diff x y = diff x (flip (flip x i) j) :=
    h.trans (two_flip_disagreements x hij).symm
  funext t
  have ht := Finset.ext_iff.mp hd t
  simp only [diff, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  cases hxt : x t <;> simpa [hxt] using ht

-- The cross products pair contributions from the same selected vertex at the two ends.
private theorem cross_signs_neg {i j : Fin 9} (hij : i ≠ j)
    (hy : y = flip (flip x i) j) (hi : flip x i ∈ C) (hj : flip x j ∈ C)
    (hs : IsSwitching C sigma) :
    transverseSign sigma x i * transverseSign sigma y j =
      -(transverseSign sigma x j * transverseSign sigma y i) := by
  have hyj : flip y j = flip x i := by rw [hy, BalancedCriticalSpectrum.flip_flip]
  have hyi : flip y i = flip x j := by
    rw [hy, flip_comm x i j, BalancedCriticalSpectrum.flip_flip]
  have h := congrFun (gamma_anticommute hij (fun _ => 1)) x
  rw [Pi.neg_apply, gamma_apply i, gamma_apply j, gamma_apply j, gamma_apply i,
    mul_one, mul_one, ← hy, ← flip_comm x i j, ← hy] at h
  rw [transverseSign, transverseSign, transverseSign, transverseSign, hyj, hyi,
    huangMatrix_symmetric y (flip x i), huangMatrix_symmetric y (flip x j)]
  calc
    _ = (huangMatrix 9 x (flip x i) * huangMatrix 9 (flip x i) y) *
        sigma (flip x i) ^ 2 := by ring
    _ = -((huangMatrix 9 x (flip x j) * huangMatrix 9 (flip x j) y) *
        sigma (flip x j) ^ 2) := by
      rw [switching_sq hs hi, switching_sq hs hj, mul_one, mul_one, h]
    _ = _ := by ring

private theorem distance_two_impossible
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : EightfoldCover C x k) (hy : EightfoldCover C y l)
    (htransverse : ∀ i ∈ diff x y, i ≠ k ∧ i ≠ l)
    (hd : hammingDist x y = 2) : False := by
  obtain ⟨i, j, hij, haxes⟩ := Finset.card_eq_two.mp (show (diff x y).card = 2 from hd)
  obtain ⟨hik, hil⟩ := htransverse i (by simp [haxes])
  obtain ⟨hjk, hjl⟩ := htransverse j (by simp [haxes])
  have hxy := eq_double_flip hij haxes
  have hyx : flip (flip y i) j = x := by
    rw [hxy, flip_comm x i j, BalancedCriticalSpectrum.flip_flip,
      BalancedCriticalSpectrum.flip_flip]
  have hxRule := eightfold_corner_rule hr hs hx.1 hx.2.1 hx.2.2 hik hjk
  have hyRule := eightfold_corner_rule hr hs hy.1 hy.2.1 hy.2.2 hil hjl
  dsimp only at hxRule hyRule
  rw [← hxy] at hxRule
  rw [hyx] at hyRule
  have hcross := cross_signs_neg hij hxy (hx.2.2 i hik).1 (hx.2.2 j hjk).1 hs
  have heq : transverseSign sigma x i * transverseSign sigma y j =
      transverseSign sigma x j * transverseSign sigma y i := by
    by_cases hkl : k = l
    · subst l
      rw [hxRule.1.mpr ⟨hy.1, hy.2.1⟩, hyRule.1.mpr ⟨hx.1, hx.2.1⟩]
    · rw [hxRule.2.mpr (Or.inr ⟨hy.1, (hy.2.2 k hkl).1⟩),
        hyRule.2.mpr (Or.inr ⟨hx.1, (hx.2.2 l (Ne.symm hkl)).1⟩), neg_mul, mul_neg]
  have hzero : transverseSign sigma x i * transverseSign sigma y j = 0 := by
    rw [← heq] at hcross
    linarith only [hcross]
  have hunitX := transverseSign_unit hs (hx.2.2 i hik).1
  have hunitY := transverseSign_unit hs (hy.2.2 j hjl).1
  rcases hunitX with h | h <;> rcases hunitY with h' | h' <;> norm_num [h, h'] at hzero

private theorem distance_three_impossible
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : EightfoldCover C x k) (hy : EightfoldCover C y l)
    (htransverse : ∀ i ∈ diff x y, i ≠ k ∧ i ≠ l)
    (hd : hammingDist x y = 3) : False := by
  have impossible {i j t : Fin 9} (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t)
      (haxes : diff x y = {i, j, t})
      (heq : transverseSign sigma x i = transverseSign sigma x j) : False := by
    obtain ⟨hik, _⟩ := htransverse i (by simp [haxes])
    obtain ⟨hjk, _⟩ := htransverse j (by simp [haxes])
    have ht : t ∈ diff x y := by simp [haxes]
    have htl := (htransverse t ht).2
    have ht' : t ∈ diff y x := by rwa [← diff_symm x y]
    have hpair : diff x (flip y t) = {i, j} := by
      rw [diff_symm x, diff_flip, ite_eq_left ht', ← diff_symm x y, haxes]
      ext u
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hu, hui | huj | hut⟩
        · exact Or.inl hui
        · exact Or.inr huj
        · exact (hu hut).elim
      · rintro (rfl | rfl)
        · exact ⟨hit, Or.inl rfl⟩
        · exact ⟨hjt, Or.inr (Or.inl rfl)⟩
    have hout := ((eightfold_corner_rule hr hs hx.1 hx.2.1 hx.2.2 hik hjk).1.mp heq).1
    exact hout (eq_double_flip hij hpair ▸ (hy.2.2 t htl).1)
  obtain ⟨i, j, t, hij, hit, hjt, haxes⟩ :=
    Finset.card_eq_three.mp (show (diff x y).card = 3 from hd)
  by_cases hijSign : transverseSign sigma x i = transverseSign sigma x j
  · exact impossible hij hit hjt haxes hijSign
  by_cases hitSign : transverseSign sigma x i = transverseSign sigma x t
  · exact impossible hit hij hjt.symm (by rw [haxes, Finset.pair_comm j t]) hitSign
  have hunit (u : Fin 9) (hu : u ∈ diff x y) :=
    transverseSign_unit hs (hx.2.2 u (htransverse u hu).1).1
  have hjtSign : transverseSign sigma x j = transverseSign sigma x t := by
    rcases hunit i (by simp [haxes]) with hi | hi
    · rw [(hunit j (by simp [haxes])).resolve_left (fun hj => hijSign (hi.trans hj.symm)),
        (hunit t (by simp [haxes])).resolve_left (fun ht => hitSign (hi.trans ht.symm))]
    · rw [(hunit j (by simp [haxes])).resolve_right (fun hj => hijSign (hi.trans hj.symm)),
        (hunit t (by simp [haxes])).resolve_right (fun ht => hitSign (hi.trans ht.symm))]
  apply impossible hjt hij.symm hit.symm _ hjtSign
  rw [haxes]
  ext u
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem closest_endpoints_distance_ge_four
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : EightfoldCover C x k) (hy : EightfoldCover C y l)
    (hne : ({x, flip x k} : Finset (Q 9)) ≠ {y, flip y l})
    (hminX : hammingDist x y ≤ hammingDist (flip x k) y)
    (hminY : hammingDist x y ≤ hammingDist x (flip y l)) :
    4 ≤ hammingDist x y := by
  have htransverse (i : Fin 9) (hi : i ∈ diff x y) : i ≠ k ∧ i ≠ l := by
    constructor
    · rintro rfl
      have h := flip_decreases_distance hi
      omega
    · rintro rfl
      rw [diff_symm x y] at hi
      have h := flip_decreases_distance hi
      rw [hammingDist_comm (flip y i) x, hammingDist_comm y x] at h
      omega
  by_contra! hlt
  have hd : hammingDist x y = 0 ∨ hammingDist x y = 1 ∨
      hammingDist x y = 2 ∨ hammingDist x y = 3 := by omega
  rcases hd with hd | hd | hd | hd
  · obtain rfl := hammingDist_eq_zero.mp hd
    have he := hx.exterior_neighbor hy.2.1 (flip_adj x l)
    exact hne (by rw [he])
  · have hmate := hx.exterior_neighbor hy.1 hd
    have hmate' := hy.exterior_neighbor hx.1 (show (hypercube 9).Adj y x from
      (hammingDist_comm y x).trans hd)
    exact hne (by rw [← hmate, ← hmate', Finset.pair_comm])
  · exact distance_two_impossible hr hs hx hy htransverse hd
  · exact distance_three_impossible hr hs hx hy htransverse hd

private theorem cover_at_endpoint {u : Q 9} (hx : EightfoldCover C x k)
    (hu : u ∈ ({x, flip x k} : Finset (Q 9))) :
    EightfoldCover C u k ∧ ({u, flip u k} : Finset (Q 9)) = {x, flip x k} := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl
  · exact ⟨hx, rfl⟩
  · exact ⟨hx.reverse, by rw [BalancedCriticalSpectrum.flip_flip, Finset.pair_comm]⟩

/-- Every pair of endpoints of distinct eightfold exterior edges has Hamming distance at least four. -/
theorem eightfold_cover_distance_ge_four
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : EightfoldCover C x k) (hy : EightfoldCover C y l)
    (hne : ({x, flip x k} : Finset (Q 9)) ≠ {y, flip y l})
    {u v : Q 9} (hu : u ∈ ({x, flip x k} : Finset (Q 9)))
    (hv : v ∈ ({y, flip y l} : Finset (Q 9))) :
    4 ≤ hammingDist u v := by
  let X : Finset (Q 9) := {x, flip x k}
  let Y : Finset (Q 9) := {y, flip y l}
  obtain ⟨⟨a, b⟩, hab, hmin⟩ := Finset.exists_min_image (X.product Y)
    (fun p => hammingDist p.1 p.2) ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩⟩
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  obtain ⟨haCover, haEdge⟩ := cover_at_endpoint hx ha
  obtain ⟨hbCover, hbEdge⟩ := cover_at_endpoint hy hb
  have haMate : flip a k ∈ X := by
    change flip a k ∈ ({x, flip x k} : Finset (Q 9))
    rw [← haEdge]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hbMate : flip b l ∈ Y := by
    change flip b l ∈ ({y, flip y l} : Finset (Q 9))
    rw [← hbEdge]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have h := closest_endpoints_distance_ge_four hr hs haCover hbCover
    (by rwa [haEdge, hbEdge]) (hmin (flip a k, b) (Finset.mem_product.mpr ⟨haMate, hb⟩))
    (hmin (a, flip b l) (Finset.mem_product.mpr ⟨ha, hbMate⟩))
  exact h.trans (hmin (u, v) (Finset.mem_product.mpr ⟨hu, hv⟩))

/-- The vertices reached by a transverse flip from either endpoint. -/
def firstShell (x : Q 9) (k : Fin 9) : Finset (Q 9) :=
  ({x, flip x k} : Finset (Q 9)).biUnion fun u => (Finset.univ.erase k).image (flip u)

private theorem mem_firstShell {p : Q 9} :
    p ∈ firstShell x k ↔ ∃ u ∈ ({x, flip x k} : Finset (Q 9)), ∃ i ≠ k, flip u i = p := by
  simp only [firstShell, Finset.mem_biUnion, Finset.mem_image, Finset.mem_erase, Finset.mem_univ,
    and_true]

private theorem firstShell_subset (hx : EightfoldCover C x k) : firstShell x k ⊆ C := by
  intro p hp
  obtain ⟨u, hu, i, hi, rfl⟩ := mem_firstShell.mp hp
  exact ((cover_at_endpoint hx hu).1.2.2 i hi).1

private theorem corner_at_endpoint {p : Q 9} (hp : p ∈ selectedCorners C x k) :
    ∃ u ∈ ({x, flip x k} : Finset (Q 9)), ∃ i j : Fin 9,
      i ≠ k ∧ j ≠ k ∧ i ≠ j ∧ p = flip (flip u i) j := by
  obtain ⟨_, i, j, hik, hjk, hij, he | he⟩ :=
    Finset.mem_filter.mp (show p ∈ C.filter _ from hp)
  · exact ⟨x, Finset.mem_insert_self _ _, i, j, hik, hjk, hij, he⟩
  · refine ⟨flip x k, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
      i, j, hik, hjk, hij, ?_⟩
    rw [he, flip_comm (flip x i) j k, flip_comm x i k]

private theorem shell_union_near {p : Q 9}
    (hp : p ∈ firstShell x k ∪ selectedCorners C x k) :
    ∃ u ∈ ({x, flip x k} : Finset (Q 9)), hammingDist u p ≤ 2 := by
  rcases Finset.mem_union.mp hp with hp | hp
  · obtain ⟨u, hu, i, _, rfl⟩ := mem_firstShell.mp hp
    exact ⟨u, hu, (show hammingDist u (flip u i) = 1 from flip_adj u i).le.trans (by decide)⟩
  · obtain ⟨u, hu, i, j, _, _, _, rfl⟩ := corner_at_endpoint hp
    refine ⟨u, hu, (hammingDist_triangle u (flip u i) (flip (flip u i) j)).trans ?_⟩
    have hi : hammingDist u (flip u i) = 1 := flip_adj u i
    have hj : hammingDist (flip u i) (flip (flip u i) j) = 1 := flip_adj (flip u i) j
    simp [hi, hj]

private theorem firstShell_disjoint_shell_union
    (hsep : ∀ u ∈ ({x, flip x k} : Finset (Q 9)), ∀ v ∈ ({y, flip y l} : Finset (Q 9)),
      4 ≤ hammingDist u v) :
    Disjoint (firstShell x k) (firstShell y l ∪ selectedCorners C y l) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨u, hu, i, _, rfl⟩ := mem_firstShell.mp hp
  obtain ⟨v, hv, hnear⟩ := shell_union_near hq
  have hfar := hsep u hu v hv
  have hstep : hammingDist u (flip u i) = 1 := flip_adj u i
  have htri := hammingDist_triangle u (flip u i) v
  rw [hammingDist_comm (flip u i) v, hstep] at htri
  omega

private theorem card_corner_firstShell_directions_ge_two
    (hx : EightfoldCover C x k) {p : Q 9} (hp : p ∈ selectedCorners C x k) :
    2 ≤ ((directions C p).filter fun i => flip p i ∈ firstShell x k).card := by
  obtain ⟨u, hu, i, j, hik, hjk, hij, rfl⟩ := corner_at_endpoint hp
  have hi : flip (flip (flip u i) j) i ∈ firstShell x k := by
    rw [flip_comm u i j, BalancedCriticalSpectrum.flip_flip]
    exact mem_firstShell.mpr ⟨u, hu, j, hjk, rfl⟩
  have hj : flip (flip (flip u i) j) j ∈ firstShell x k := by
    rw [BalancedCriticalSpectrum.flip_flip]
    exact mem_firstShell.mpr ⟨u, hu, i, hik, rfl⟩
  rw [← Finset.card_pair hij]
  apply Finset.card_le_card
  intro t ht
  have hm : flip (flip (flip u i) j) t ∈ firstShell x k := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hi
    · exact hj
  exact Finset.mem_filter.mpr ⟨(mem_directions _ _ _).mpr (firstShell_subset hx hm), hm⟩

/-- The unions of the first shell and selected corners of distinct eightfold covers are disjoint. -/
theorem eightfold_cover_shells_disjoint
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : EightfoldCover C x k) (hy : EightfoldCover C y l)
    (hne : ({x, flip x k} : Finset (Q 9)) ≠ {y, flip y l}) :
    Disjoint (firstShell x k ∪ selectedCorners C x k) (firstShell y l ∪ selectedCorners C y l) := by
  have hXY := firstShell_disjoint_shell_union (C := C)
    (fun u hu v hv => eightfold_cover_distance_ge_four hr hs hx hy hne hu hv)
  have hYX := firstShell_disjoint_shell_union (C := C)
    (fun u hu v hv => eightfold_cover_distance_ge_four hr hs hy hx hne.symm hu hv)
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hpCorner := (Finset.mem_union.mp hp).resolve_left
    (fun h => Finset.disjoint_left.mp hXY h hq)
  have hqCorner := (Finset.mem_union.mp hq).resolve_left
    (fun h => Finset.disjoint_left.mp hYX h hp)
  let A := (directions C p).filter fun i => flip p i ∈ firstShell x k
  let B := (directions C p).filter fun i => flip p i ∈ firstShell y l
  have hA : 2 ≤ A.card := card_corner_firstShell_directions_ge_two hx hpCorner
  have hB : 2 ≤ B.card := card_corner_firstShell_directions_ge_two hy hqCorner
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Finset.disjoint_left.mp hXY (Finset.mem_filter.mp hi).2
      (Finset.mem_union_left _ (Finset.mem_filter.mp hj).2)
  have hcard := Finset.card_le_card (Finset.union_subset
    (Finset.filter_subset _ (directions C p)) (Finset.filter_subset _ (directions C p)) :
    A ∪ B ⊆ directions C p)
  have hpC := (Finset.mem_filter.mp (show p ∈ C.filter _ from hpCorner)).1
  rw [Finset.card_union_of_disjoint hdisj, regular_directions C hr hpC] at hcard
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverSeparation
