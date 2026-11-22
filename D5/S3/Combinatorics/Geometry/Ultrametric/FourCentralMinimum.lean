/- GID: D5/S3/Combinatorics/Geometry/Ultrametric/FourCentralMinimum
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/Ultrametric/FourCentralMinimum
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Four-central n-point ultrametrics exist only for n ≥ 8 and have at least 6n-16-4⌊n/4⌋+⌈n/2⌉ central edges, sharply. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#438)
escape_witness: four_le_class (every class of points below the diameter from a point has at
  least four points), ball_bound (a closed b-ball K carries at least 4|K|-8 incidences of
  length b) and middle_bound (the middle central length has at least 2n-4⌊n/4⌋ edges), with
  diameter_bound and tree_edges_le (the seven-level ultrametric has at most
  6n-16-4⌊n/4⌋+⌈n/2⌉ central edges).
proof_shape:
  sph, bl, blk, part, half, comp, pos, lv, val, td, FourTree, oneEdge, firstHalves:
    definitions; consumers: the lemmas below and the theorem.
  two_le_card, center_shape: content; consumers: ultra_four_central_minimum.
  edges_split: content; consumer: general.
  four_le_class: content; consumer: diameter_bound.
  diameter_bound: content; consumer: general.
  sum_sph: content; consumer: middle_bound.
  ball_bound: content; consumer: middle_bound.
  middle_bound: content; consumer: general.
  general: content; consumer: ultra_four_central_minimum.
  lv_ge, lv_min, td_ultra, td_central, tree_center, tree_edges_le, one_hit,
    mem_firstHalves, firstHalves_card: content; consumers: the FourTree instances,
    tree_center_card, tree_edges_le and the theorem.
  iso, mem_bl_iff, val_anti, val_bounds, lv_comm, td_self, td_comm, td_pos, td_nonneg,
    td_triangle, td_eq_four, td_eq_two, td_eq_one, td_row_zero, tree_center_card,
    firstHalves_sub, blk_le, half_cases, half_zero: bind-only helpers; consumers: the lemmas
    above and the theorem.
  ultra_four_central_minimum: content.
Direct frozen dependencies: D5/S3/Combinatorics/Geometry/CentralEdgeCover (len, lengthEdges,
  lengthEdges_card; sha256:54ac76512900791871a24a3c74780b9c806a77fb46f1c6eee4ce183b9b861dbb),
  D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders (exists_central_bound;
  sha256:702d824403ed80e0b34ce27c4ef15999afdb07331ba529e31bcf21638cd8a6a9),
  D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges (center, centralGraph;
  sha256:846beddcd39fdb877075256f79f15ee0060283f2ccd0f5f6bad09d7f46dd7bc0),
  D5/S3/Combinatorics/Geometry/UltrametricThreeCentralMinimum (mem_lengthEdges_iff,
  mem_lengthEdges_D, image_pairs_card; made public here).
Search record (§3.1): the per-length cover bound, the central maximum distance and the
  cross-class pair count are reused from the frozen modules above; Mathlib supplies the
  handshake identity SimpleGraph.sum_degrees_eq_twice_card_edges, the fiberwise sums
  Finset.sum_fiberwise_of_maps_to and Finset.card_eq_sum_card_fiberwise, and the isosceles
  rule IsUltrametricDist.dist_eq_max_of_dist_ne_dist. No frozen module bounds the edges of a
  middle central length or treats four central values.
-/

import D5.S3.Combinatorics.Geometry.UltrametricThreeCentralMinimum

/-! # The sharp four-central ultrametric minimum

A four-central ultrametric on `n` points has center `{0, a, b, D}` with `0 < a < b < D` and `D`
its diameter. The points at distance below `D` from a fixed point contain the point, an
`a`-neighbour, a `b`-neighbour and the `a`-neighbour of that, so the class and its complement
have at least four points each: there are at least `4 (n - 4)` edges of length `D`, and
`n ≥ 8`. The closed balls of radius `b` partition the space; a ball `K` splits into the open
`b`-ball `U` of one of its points and the rest, each of size at least two, and every point of
`U` is at distance `b` from every point of `K \ U`. So the ball carries at least `4 |K| - 8`
incidences of length `b`, there are at most `⌊n / 4⌋` balls, and the length `b` has at least
`2n - 4 ⌊n / 4⌋` edges. The length `a` has at least `⌈n / 2⌉` edges. A seven-level hierarchical
ultrametric with noncentral intermediate distances attains all three bounds at once.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Geometry.Ultrametric.FourCentralMinimum

open D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges
open D5.S3.Combinatorics.Geometry.CentralEdgeCover
open D5.S3.Combinatorics.Geometry.UltrametricThreeCentralMinimum

noncomputable section

section General

variable {X : Type} [Fintype X] [MetricSpace X] [IsUltrametricDist X]

omit [IsUltrametricDist X] in
/-- The center of a finite metric space with at most one point is not of size four. -/
private lemma two_le_card (hk : Nat.card (center X) = 4) : 2 ≤ Fintype.card X := by
  by_contra hlt
  push Not at hlt
  rcases isEmpty_or_nonempty X with hX | ⟨⟨p⟩⟩
  · have hC : center X = Set.Ici 0 := by
      ext t
      simp only [center, Set.mem_ofPred_eq, Set.mem_Ici]
      exact ⟨fun h => h.1, fun h => ⟨h, fun x => isEmptyElim x⟩⟩
    rw [Nat.card_coe_set_eq, hC, (Set.Ici_infinite (0 : ℝ)).ncard] at hk
    omega
  · have hsub : center X ⊆ {0} := by
      intro t ht
      obtain ⟨y, hy⟩ := ht.2 p
      have hyp : y = p := Fintype.card_le_one_iff.mp (by omega) y p
      rw [hyp, dist_self] at hy
      exact hy.symm
    have := Set.ncard_le_ncard hsub (Set.finite_singleton 0)
    rw [Set.ncard_singleton, ← Nat.card_coe_set_eq, hk] at this
    omega

/-- In a finite ultrametric with four central values, the center is `{0, a, b, D}` with
`0 < a < b < D` and all distances at most `D`. -/
private lemma center_shape (hk : Nat.card (center X) = 4) :
    ∃ a b D : ℝ, 0 < a ∧ a < b ∧ b < D ∧ center X = {0, a, b, D} ∧
      ∀ x y : X, dist x y ≤ D := by
  have hX := two_le_card hk
  have : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨D, hD, hbound⟩ := UltrametricCenterSphereOrders.exists_central_bound (X := X)
  obtain ⟨p⟩ := ‹Nonempty X›
  have hfin : (center X).Finite :=
    (Set.finite_range fun y => dist y p).subset (fun t ht => ht.2 p)
  have h0 : (0 : ℝ) ∈ center X := ⟨le_rfl, fun x => ⟨x, dist_self x⟩⟩
  obtain ⟨u, v, huv⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card X)
  have hDpos : 0 < D := lt_of_lt_of_le (dist_pos.mpr huv) (hbound u v)
  have hk' : (center X).ncard = 4 := by rwa [← Nat.card_coe_set_eq]
  have hsub : ({0, D} : Set ℝ) ⊆ center X := by
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact h0
    · exact hD
  have hT : (center X \ {0, D}).ncard = 2 := by
    rw [Set.ncard_sdiff hsub, hk', Set.ncard_pair hDpos.ne]
  have hmem : ∀ t ∈ center X \ {0, D}, t ∈ center X ∧ 0 < t ∧ t < D := by
    intro t ht
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
    obtain ⟨htc, hne0, hneD⟩ := ht
    obtain ⟨y, hy⟩ := htc.2 p
    exact ⟨htc, lt_of_le_of_ne htc.1 (Ne.symm hne0), lt_of_le_of_ne (hy ▸ hbound y p) hneD⟩
  obtain ⟨a, b, hab, hTeq⟩ : ∃ a b : ℝ, a < b ∧ center X \ {0, D} = {a, b} := by
    obtain ⟨u', v', huv', hTeq⟩ := Set.ncard_eq_two.mp hT
    rcases lt_or_gt_of_ne huv' with h | h
    · exact ⟨u', v', h, hTeq⟩
    · exact ⟨v', u', h, by rw [hTeq, Set.pair_comm]⟩
  obtain ⟨haC, ha0, -⟩ := hmem a (by rw [hTeq]; simp)
  obtain ⟨hbC, -, hbD⟩ := hmem b (by rw [hTeq]; simp)
  refine ⟨a, b, D, ha0, hab, hbD, ?_, hbound⟩
  ext t
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro ht
    by_cases h0t : t = 0
    · exact Or.inl h0t
    by_cases hDt : t = D
    · exact Or.inr (Or.inr (Or.inr hDt))
    have : t ∈ center X \ {0, D} := by simp [ht, h0t, hDt]
    rw [hTeq] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · rintro (rfl | rfl | rfl | rfl)
    · exact h0
    · exact haC
    · exact hbC
    · exact hD

omit [IsUltrametricDist X] in
open Classical in
/-- The central edges split into those of lengths `D`, `b` and `a`. -/
private lemma edges_split {a b D : ℝ} (hab : a < b) (hbD : b < D)
    (hC : center X = {0, a, b, D}) :
    (centralGraph X).edgeFinset.card =
      (lengthEdges X D).card + (lengthEdges X b).card + (lengthEdges X a).card := by
  have hmaps : ∀ e ∈ (centralGraph X).edgeFinset, len e ∈ ({a, b, D} : Finset ℝ) := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have hxy : x ≠ y := he.ne
      have hmem : dist x y ∈ center X := by
        simp only [centralGraph, SimpleGraph.fromRel_adj] at he
        rcases he.2 with h | h
        · exact h
        · rwa [dist_comm] at h
      rw [hC] at hmem
      simp only [len, Sym2.lift_mk, Finset.mem_insert, Finset.mem_singleton]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h | h
      · exact absurd (dist_eq_zero.mp h) hxy
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_insert (by simp; constructor <;>
    linarith), Finset.sum_insert (by simp; linarith), Finset.sum_singleton]
  simp only [lengthEdges]
  omega

omit [Fintype X] in
/-- The isosceles property: a point at distance `t` from `y`, where `y` is at distance `s ≠ t`
from `x`, is at distance `max s t` from `x`. -/
private lemma iso {x y z : X} (h : dist x y ≠ dist y z) : dist x z = max (dist x y) (dist y z) :=
  IsUltrametricDist.dist_eq_max_of_dist_ne_dist x y z h

open Classical in
/-- Every class of points at distance below `D` from a point has at least four points. -/
private lemma four_le_class {a b D : ℝ} (ha : 0 < a) (hab : a < b) (hbD : b < D)
    (haC : a ∈ center X) (hbC : b ∈ center X) (x : X) :
    4 ≤ (Finset.univ.filter fun y => dist x y < D).card := by
  obtain ⟨x1, hx1⟩ := haC.2 x
  obtain ⟨y, hy⟩ := hbC.2 x
  obtain ⟨y1, hy1⟩ := haC.2 y
  rw [dist_comm] at hx1 hy hy1
  have hxy1 : dist x y1 = b := by
    rw [iso (by rw [hy, hy1]; exact hab.ne'), hy, hy1, max_eq_left hab.le]
  have hne : ∀ {u v : X}, dist x u ≠ dist x v → u ≠ v := fun h e => h (e ▸ rfl)
  have hsub : ({x, x1, y, y1} : Finset X) ⊆ Finset.univ.filter fun z => dist x z < D := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hz with rfl | rfl | rfl | rfl
    · rw [dist_self]; linarith
    · rw [hx1]; linarith
    · rw [hy]; exact hbD
    · rw [hxy1]; exact hbD
  have h4 : ({x, x1, y, y1} : Finset X).card = 4 := by
    have hxx1 : x ≠ x1 := hne (by rw [dist_self, hx1]; exact ha.ne)
    have hxy : x ≠ y := hne (by rw [dist_self, hy]; linarith)
    have hxy1' : x ≠ y1 := hne (by rw [dist_self, hxy1]; linarith)
    have hx1y : x1 ≠ y := hne (by rw [hx1, hy]; exact hab.ne)
    have hx1y1 : x1 ≠ y1 := hne (by rw [hx1, hxy1]; exact hab.ne)
    have hyy1 : y ≠ y1 := by
      rintro rfl
      rw [dist_self] at hy1
      linarith
    rw [Finset.card_insert_of_notMem (by simp [hxx1, hxy, hxy1']),
      Finset.card_insert_of_notMem (by simp [hx1y, hx1y1]), Finset.card_pair hyy1]
  exact h4 ▸ Finset.card_le_card hsub

open Classical in
/-- The diameter edges number at least `4 (n - 4)`, and `n ≥ 8`. -/
private lemma diameter_bound {a b D : ℝ} (ha : 0 < a) (hab : a < b) (hbD : b < D)
    (haC : a ∈ center X) (hbC : b ∈ center X) (hDC : D ∈ center X)
    (hbound : ∀ x y : X, dist x y ≤ D) (p : X) :
    8 ≤ Fintype.card X ∧ 4 * (Fintype.card X - 4) ≤ (lengthEdges X D).card := by
  set S := Finset.univ.filter fun y => dist p y < D with hSdef
  have hS4 : 4 ≤ S.card := four_le_class ha hab hbD haC hbC p
  have hSc4 : 4 ≤ Sᶜ.card := by
    obtain ⟨z, hz⟩ := hDC.2 p
    rw [dist_comm] at hz
    refine (four_le_class ha hab hbD haC hbC z).trans (Finset.card_le_card ?_)
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [hSdef, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    rw [iso (by rw [hz]; exact hy.ne'), hz]
    exact le_max_left _ _
  have hsum : S.card + Sᶜ.card = Fintype.card X := Finset.card_add_card_compl S
  have hsub : (S ×ˢ Sᶜ).image (fun q => s(q.1, q.2)) ⊆ lengthEdges X D := by
    intro e he
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    simp only [hSdef, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      not_lt] at hu hv
    have hd : dist u v = D := by
      refine le_antisymm (hbound u v) ?_
      by_contra hlt
      push Not at hlt
      have := IsUltrametricDist.dist_triangle_max p u v
      have : max (dist p u) (dist u v) < D := max_lt hu hlt
      linarith
    have hne : u ≠ v := by
      rintro rfl
      rw [dist_self] at hd
      linarith
    exact mem_lengthEdges_D hDC hne hd
  have hED := Finset.card_le_card hsub
  rw [image_pairs_card] at hED
  refine ⟨by omega, le_trans ?_ hED⟩
  obtain ⟨s', hs'⟩ : ∃ s', S.card = s' + 4 := ⟨S.card - 4, by omega⟩
  obtain ⟨t', ht'⟩ : ∃ t', Sᶜ.card = t' + 4 := ⟨Sᶜ.card - 4, by omega⟩
  rw [hs', ht']
  have : Fintype.card X - 4 = s' + t' + 4 := by omega
  rw [this]
  nlinarith

open Classical in
/-- The points at distance `t` from `x`. -/
private def sph (t : ℝ) (x : X) : Finset X := Finset.univ.filter fun y => dist x y = t

omit [IsUltrametricDist X] in
open Classical in
/-- Twice the number of central edges of length `t > 0` is the total size of the `t`-spheres. -/
private lemma sum_sph {t : ℝ} (ht : 0 < t) (htC : t ∈ center X) :
    ∑ x : X, (sph t x).card = 2 * (lengthEdges X t).card := by
  let G : SimpleGraph X := SimpleGraph.fromRel fun x y => dist x y = t
  have hdeg : ∀ x, G.degree x = (sph t x).card := by
    intro x
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    congr 1
    ext y
    simp only [sph, Finset.mem_filter, Finset.mem_univ, true_and, G,
      SimpleGraph.fromRel_adj, dist_comm y x, or_self]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rintro rfl
      rw [dist_self] at h
      exact ht.ne h
  have hedges : G.edgeFinset = lengthEdges X t := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, mem_lengthEdges_iff]
      simp only [G, centralGraph, SimpleGraph.fromRel_adj, dist_comm y x, or_self]
      constructor
      · rintro ⟨hxy, h⟩
        exact ⟨⟨hxy, h ▸ htC⟩, h⟩
      · rintro ⟨⟨hxy, _⟩, h⟩
        exact ⟨hxy, h⟩
  simp_rw [← hdeg]
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hedges]

open Classical in
/-- The closed ball of radius `b`, as a finite set. -/
private def bl (b : ℝ) (x : X) : Finset X := Finset.univ.filter fun y => dist x y ≤ b

open Classical in
private lemma mem_bl_iff {b : ℝ} (hb : 0 ≤ b) (x y : X) : y ∈ bl b x ↔ bl b y = bl b x := by
  constructor
  · intro hy
    simp only [bl, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    ext z
    simp only [bl, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hz
      exact (IsUltrametricDist.dist_triangle_max x y z).trans (max_le hy hz)
    · intro hz
      rw [dist_comm] at hy
      exact (IsUltrametricDist.dist_triangle_max y x z).trans (max_le hy hz)
  · intro h
    rw [← h]
    simp only [bl, Finset.mem_filter, Finset.mem_univ, true_and, dist_self]
    exact hb

open Classical in
/-- A closed `b`-ball `K` carries at least `4 |K| - 8` incidences of length `b`, and has at least
four points. -/
private lemma ball_bound {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (haC : a ∈ center X) (hbC : b ∈ center X) (x0 : X) :
    4 * (bl b x0).card ≤ ∑ x ∈ bl b x0, (sph b x).card + 8 ∧ 4 ≤ (bl b x0).card := by
  set K := bl b x0 with hK
  set U := Finset.univ.filter fun y => dist x0 y < b with hU
  have hUK : U ⊆ K := by
    intro y hy
    simp only [hU, hK, bl, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy.le
  have hmemW : ∀ y, y ∈ K \ U ↔ dist x0 y = b := by
    intro y
    simp only [hU, hK, bl, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      not_lt]
    constructor
    · exact fun h => le_antisymm h.1 h.2
    · exact fun h => ⟨h.le, h.ge⟩
  have hcross : ∀ u ∈ U, ∀ v ∈ K \ U, dist u v = b := by
    intro u hu v hv
    simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have hv' := (hmemW v).mp hv
    rw [dist_comm] at hu
    rw [iso (by rw [hv']; exact hu.ne), hv', max_eq_right hu.le]
  have hU2 : 2 ≤ U.card := by
    obtain ⟨x1, hx1⟩ := haC.2 x0
    rw [dist_comm] at hx1
    have hne : x0 ≠ x1 := by rintro rfl; rw [dist_self] at hx1; linarith
    have hsub : ({x0, x1} : Finset X) ⊆ U := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hz with rfl | rfl
      · rw [dist_self]; linarith
      · rw [hx1]; exact hab
    exact (Finset.card_pair hne).symm.le.trans (Finset.card_le_card hsub)
  have hW2 : 2 ≤ (K \ U).card := by
    obtain ⟨y, hy⟩ := hbC.2 x0
    obtain ⟨y1, hy1⟩ := haC.2 y
    rw [dist_comm] at hy hy1
    have hxy1 : dist x0 y1 = b := by
      rw [iso (by rw [hy, hy1]; exact hab.ne'), hy, hy1, max_eq_left hab.le]
    have hne : y ≠ y1 := by rintro rfl; rw [dist_self] at hy1; linarith
    have hsub : ({y, y1} : Finset X) ⊆ K \ U := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact (hmemW _).mpr hy
      · exact (hmemW _).mpr hxy1
    exact (Finset.card_pair hne).symm.le.trans (Finset.card_le_card hsub)
  have hsplit : (K \ U).card + U.card = K.card := Finset.card_sdiff_add_card_eq_card hUK
  have hsum : ∑ x ∈ K, (sph b x).card =
      ∑ x ∈ K \ U, (sph b x).card + ∑ x ∈ U, (sph b x).card :=
    (Finset.sum_sdiff hUK).symm
  have h1 : ∀ x ∈ U, (K \ U).card ≤ (sph b x).card := fun x hx =>
    Finset.card_le_card fun y hy => by
      simp only [sph, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hcross x hx y hy
  have h2 : ∀ x ∈ K \ U, U.card ≤ (sph b x).card := fun x hx =>
    Finset.card_le_card fun y hy => by
      simp only [sph, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [dist_comm]
      exact hcross y hy x hx
  have hs1 := Finset.card_nsmul_le_sum U _ _ h1
  have hs2 := Finset.card_nsmul_le_sum (K \ U) _ _ h2
  simp only [smul_eq_mul] at hs1 hs2
  refine ⟨?_, by omega⟩
  rw [hsum, ← hsplit]
  obtain ⟨t', ht'⟩ : ∃ t', U.card = t' + 2 := ⟨U.card - 2, by omega⟩
  obtain ⟨w', hw'⟩ : ∃ w', (K \ U).card = w' + 2 := ⟨(K \ U).card - 2, by omega⟩
  rw [ht', hw'] at hs1 hs2
  rw [ht', hw']
  nlinarith

open Classical in
/-- The middle length `b` has at least `2n - 4 ⌊n / 4⌋` central edges. -/
private lemma middle_bound {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (haC : a ∈ center X) (hbC : b ∈ center X) :
    2 * Fintype.card X - 4 * (Fintype.card X / 4) ≤ (lengthEdges X b).card := by
  have hb : 0 < b := ha.trans hab
  set T := (Finset.univ : Finset X).image (bl b) with hT
  have hmaps : ∀ x ∈ (Finset.univ : Finset X), bl b x ∈ T :=
    fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x)
  have hfib : ∀ K ∈ T, (Finset.univ.filter fun x => bl b x = K) = K := by
    intro K hK
    obtain ⟨x0, -, rfl⟩ := Finset.mem_image.mp hK
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (mem_bl_iff hb.le x0 y).symm
  have hdeg : ∑ x : X, (sph b x).card = ∑ K ∈ T, ∑ x ∈ K, (sph b x).card := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    exact Finset.sum_congr rfl fun K hK => by rw [hfib K hK]
  have hcard : Fintype.card X = ∑ K ∈ T, K.card := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise hmaps]
    exact Finset.sum_congr rfl fun K hK => by rw [hfib K hK]
  have hKb : ∀ K ∈ T, 4 * K.card ≤ ∑ x ∈ K, (sph b x).card + 8 ∧ 4 ≤ K.card := by
    intro K hK
    obtain ⟨x0, -, rfl⟩ := Finset.mem_image.mp hK
    exact ball_bound ha hab haC hbC x0
  have hle1 : 4 * Fintype.card X ≤ ∑ x : X, (sph b x).card + 8 * T.card := by
    rw [hdeg, hcard, Finset.mul_sum]
    calc ∑ K ∈ T, 4 * K.card ≤ ∑ K ∈ T, (∑ x ∈ K, (sph b x).card + 8) :=
          Finset.sum_le_sum fun K hK => (hKb K hK).1
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
  have hle2 : T.card * 4 ≤ Fintype.card X := by
    rw [hcard]
    exact (smul_eq_mul _ _).symm.le.trans
      (Finset.card_nsmul_le_sum T _ 4 fun K hK => (hKb K hK).2)
  have h2 := sum_sph hb hbC
  omega

open Classical in
/-- The general lower bounds, length by length. -/
private lemma general {a b D : ℝ} (ha : 0 < a) (hab : a < b) (hbD : b < D)
    (hC : center X = {0, a, b, D}) (p : X) :
    8 ≤ Fintype.card X ∧
    (centralGraph X).edgeFinset.card =
      (lengthEdges X D).card + (lengthEdges X b).card + (lengthEdges X a).card ∧
    4 * (Fintype.card X - 4) ≤ (lengthEdges X D).card ∧
    2 * Fintype.card X - 4 * (Fintype.card X / 4) ≤ (lengthEdges X b).card ∧
    (Fintype.card X + 1) / 2 ≤ (lengthEdges X a).card := by
  have haC : a ∈ center X := by rw [hC]; simp
  have hbC : b ∈ center X := by rw [hC]; simp
  have hDC : D ∈ center X := by rw [hC]; simp
  have : Nonempty X := ⟨p⟩
  have hbound : ∀ x y : X, dist x y ≤ D := by
    obtain ⟨D', hD', hb'⟩ := UltrametricCenterSphereOrders.exists_central_bound (X := X)
    obtain ⟨y, hy⟩ := hDC.2 p
    have hDD' : D ≤ D' := hy ▸ hb' y p
    rw [hC] at hD'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hD'
    intro x z
    refine (hb' x z).trans ?_
    rcases hD' with h | h | h | h <;> linarith
  obtain ⟨h8, hDb⟩ := diameter_bound ha hab hbD haC hbC hDC hbound p
  exact ⟨h8, edges_split hab hbD hC, hDb, middle_bound ha hab haC hbC,
    lengthEdges_card X haC ha.ne'⟩

end General

/-! ### The attaining ultrametric -/

section Tree

variable (n : ℕ)

/-- The block of a point: the blocks `{4k, …, 4k+3}`, the last absorbing the remaining
`n mod 4` points. -/
private def blk (i : ℕ) : ℕ := if i / 4 < n / 4 then i / 4 else n / 4 - 1

/-- The part of a point: the block `{0, 1, 2, 3}` against the rest. -/
private def part (i : ℕ) : ℕ := if i < 4 then 0 else 1

/-- The half of a point inside its block: the first two points against the rest. -/
private def half (i : ℕ) : ℕ := if i < 4 * blk n i + 2 then 0 else 1

/-- The component of a point: the pairs `{2k, 2k+1}`, and for odd `n` the triple
`{n-3, n-2, n-1}`. -/
private def comp (i : ℕ) : ℕ := if n % 2 = 1 ∧ n - 3 ≤ i then n else i / 2

/-- The position inside a component; in the triple, `n - 3` is designated. -/
private def pos (i : ℕ) : ℕ :=
  if n % 2 = 1 ∧ n - 3 ≤ i then (if i = n - 3 then 0 else 1) else i % 2

/-- The first level at which two points differ: `0` part, `1` block, `2` half, `3` component,
`4` position, `5` none. -/
private def lv (i j : ℕ) : ℕ :=
  if part i ≠ part j then 0
  else if blk n i ≠ blk n j then 1
  else if half n i ≠ half n j then 2
  else if comp n i ≠ comp n j then 3
  else if pos n i ≠ pos n j then 4
  else 5

/-- The distance attached to a level: `4`, `3`, `2`, `3/2`, `1`, `1/2`. -/
private def val (l : ℕ) : ℝ :=
  if l = 0 then 4 else if l = 1 then 3 else if l = 2 then 2 else if l = 3 then 3 / 2
  else if l = 4 then 1 else 1 / 2

/-- The seven-level distance: `4` across parts, `3` across blocks, `2` across halves, `3/2`
across components, `1` across positions, `1/2` inside the triple's undesignated pair. -/
private def td (x y : Fin n) : ℝ := if x = y then 0 else val (lv n x.1 y.1)

private lemma lv_ge (k i j : ℕ) : k ≤ lv n i j ↔
    (0 < k → part i = part j) ∧ (1 < k → blk n i = blk n j) ∧
    (2 < k → half n i = half n j) ∧ (3 < k → comp n i = comp n j) ∧
    (4 < k → pos n i = pos n j) ∧ k ≤ 5 := by
  unfold lv
  split_ifs <;> omega

private lemma lv_min (i j l : ℕ) : min (lv n i j) (lv n j l) ≤ lv n i l := by
  have h1 := (lv_ge n (min (lv n i j) (lv n j l)) i j).mp (min_le_left _ _)
  have h2 := (lv_ge n (min (lv n i j) (lv n j l)) j l).mp (min_le_right _ _)
  rw [lv_ge]
  omega

private lemma val_anti {l l' : ℕ} (h : l ≤ l') : val l' ≤ val l := by
  unfold val
  split_ifs <;> first | (exfalso; omega) | norm_num

private lemma val_bounds (l : ℕ) : 1 / 2 ≤ val l ∧ val l ≤ 4 := by
  unfold val
  split_ifs <;> norm_num

private lemma td_self (x : Fin n) : td n x x = 0 := by unfold td; simp only [↓reduceIte]

private lemma lv_comm (i j : ℕ) : lv n i j = lv n j i := by
  unfold lv
  simp only [ne_comm]

private lemma td_comm (x y : Fin n) : td n x y = td n y x := by
  unfold td
  by_cases h : x = y
  · subst h; rfl
  · simp only [h, Ne.symm h, ↓reduceIte, lv_comm n x.1 y.1]

private lemma td_pos {x y : Fin n} (h : x ≠ y) : 1 / 2 ≤ td n x y ∧ td n x y ≤ 4 := by
  unfold td
  simp only [h, ↓reduceIte]
  exact val_bounds _

private lemma td_ultra (x y z : Fin n) : td n x z ≤ max (td n x y) (td n y z) := by
  by_cases hxz : x = z
  · rw [hxz, td_self]
    exact le_max_of_le_left (by
      by_cases hzy : z = y
      · rw [hzy, td_self]
      · exact le_trans (by norm_num) (td_pos n hzy).1)
  by_cases hxy : x = y
  · subst hxy; rw [td_self, max_eq_right (by
      exact le_trans (by norm_num) (td_pos n hxz).1)]
  by_cases hyz : y = z
  · subst hyz; rw [td_self, max_eq_left (by
      exact le_trans (by norm_num) (td_pos n hxy).1)]
  unfold td
  simp only [hxz, hxy, hyz, ↓reduceIte]
  have hm := lv_min n x.1 y.1 z.1
  rcases le_total (lv n x.1 y.1) (lv n y.1 z.1) with h | h
  · rw [min_eq_left h] at hm
    exact le_max_of_le_left (val_anti hm)
  · rw [min_eq_right h] at hm
    exact le_max_of_le_right (val_anti hm)

private lemma td_nonneg (x y : Fin n) : 0 ≤ td n x y := by
  by_cases h : x = y
  · rw [h, td_self]
  · exact le_trans (by norm_num) (td_pos n h).1

private lemma td_triangle (x y z : Fin n) : td n x z ≤ td n x y + td n y z :=
  (td_ultra n x y z).trans (max_le_add_of_nonneg (td_nonneg n x y) (td_nonneg n y z))

private lemma td_eq_four {x y : Fin n} (h : part x.1 ≠ part y.1) : td n x y = 4 := by
  have hxy : x ≠ y := by rintro rfl; exact h rfl
  unfold td lv val; simp only [hxy, h, ↓reduceIte, ne_eq, not_false_eq_true]

private lemma td_eq_two {x y : Fin n} (hxy : x ≠ y) (hp : part x.1 = part y.1)
    (hb : blk n x.1 = blk n y.1) (hh : half n x.1 ≠ half n y.1) : td n x y = 2 := by
  unfold td lv val; simp only [hxy, hp, hb, hh, ↓reduceIte, ne_eq, not_true_eq_false,
    not_false_eq_true, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]

private lemma td_eq_one {x y : Fin n} (hxy : x ≠ y) (hp : part x.1 = part y.1)
    (hb : blk n x.1 = blk n y.1) (hh : half n x.1 = half n y.1)
    (hc : comp n x.1 = comp n y.1) (hq : pos n x.1 ≠ pos n y.1) : td n x y = 1 := by
  unfold td lv val; simp only [hxy, hp, hb, hh, hc, hq, ↓reduceIte, ne_eq, not_true_eq_false,
    not_false_eq_true, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
  norm_num

/-- Distinct points at a distance among `1`, `2`, `4` lie in different parts, or in one block at
different halves, or in one component at different positions. -/
private lemma td_central {x y : Fin n} (hxy : x ≠ y)
    (h : td n x y = 1 ∨ td n x y = 2 ∨ td n x y = 4) :
    part x.1 ≠ part y.1 ∨
      (part x.1 = part y.1 ∧ blk n x.1 = blk n y.1 ∧ half n x.1 ≠ half n y.1) ∨
      (part x.1 = part y.1 ∧ blk n x.1 = blk n y.1 ∧ half n x.1 = half n y.1 ∧
        comp n x.1 = comp n y.1 ∧ pos n x.1 ≠ pos n y.1) := by
  unfold td at h
  simp only [hxy, ↓reduceIte] at h
  have hl : lv n x.1 y.1 = 4 ∨ lv n x.1 y.1 = 2 ∨ lv n x.1 y.1 = 0 := by
    unfold val at h
    split_ifs at h <;> norm_num at h <;> omega
  rcases hl with hl | hl | hl
  · obtain ⟨hp, hb, hh, hc, -, -⟩ := (lv_ge n 4 x.1 y.1).mp (by omega)
    refine Or.inr (Or.inr ⟨hp (by norm_num), hb (by norm_num), hh (by norm_num),
      hc (by norm_num), fun hq => ?_⟩)
    have := (lv_ge n 5 x.1 y.1).mpr ⟨fun _ => hp (by norm_num), fun _ => hb (by norm_num),
      fun _ => hh (by norm_num), fun _ => hc (by norm_num), fun _ => hq, le_rfl⟩
    omega
  · obtain ⟨hp, hb, -, -, -, -⟩ := (lv_ge n 2 x.1 y.1).mp (by omega)
    refine Or.inr (Or.inl ⟨hp (by norm_num), hb (by norm_num), fun hh => ?_⟩)
    have := (lv_ge n 3 x.1 y.1).mpr ⟨fun _ => hp (by norm_num), fun _ => hb (by norm_num),
      fun _ => hh, fun h => absurd h (by omega), fun h => absurd h (by omega),
      by norm_num⟩
    omega
  · refine Or.inl fun hp => ?_
    have := (lv_ge n 1 x.1 y.1).mpr ⟨fun _ => hp, fun h => absurd h (by omega),
      fun h => absurd h (by omega), fun h => absurd h (by omega),
      fun h => absurd h (by omega), by norm_num⟩
    omega

/-- The points of `Fin n` with the seven-level ultrametric. -/
def FourTree : Type := Fin n

instance : Fintype (FourTree n) := inferInstanceAs (Fintype (Fin n))

noncomputable instance : MetricSpace (FourTree n) where
  dist x y := td n x y
  dist_self x := td_self n x
  dist_comm x y := td_comm n x y
  dist_triangle x y z := td_triangle n x y z
  eq_of_dist_eq_zero {x y} h := by
    by_contra hne
    have := (td_pos n hne).1
    change td n x y = 0 at h
    linarith

instance : IsUltrametricDist (FourTree n) := ⟨fun x y z => td_ultra n x y z⟩

/-- The distances from the point `0` are `0`, `1`, `2` and `4`. -/
private lemma td_row_zero (hn : 8 ≤ n) (y : Fin n) :
    td n y ⟨0, by omega⟩ = 0 ∨ td n y ⟨0, by omega⟩ = 1 ∨ td n y ⟨0, by omega⟩ = 2 ∨
      td n y ⟨0, by omega⟩ = 4 := by
  obtain ⟨i, hi⟩ := y
  by_cases h0 : i = 0
  · subst h0; left; exact td_self n _
  by_cases h1 : i = 1
  · subst h1
    right; left
    apply td_eq_one n (by simp) <;> simp only [part, blk, half, comp, pos] <;>
      split_ifs <;> omega
  by_cases h4 : i < 4
  · right; right; left
    apply td_eq_two n (by simp; omega) <;> simp only [part, blk, half] <;> split_ifs <;> omega
  · right; right; right
    apply td_eq_four n
    simp only [part]; split_ifs <;> omega

private lemma tree_center (hn : 8 ≤ n) : center (FourTree n) = {0, 1, 2, 4} := by
  ext t
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, ht⟩
    obtain ⟨y, hy⟩ := ht (⟨0, by omega⟩ : Fin n)
    change td n y ⟨0, by omega⟩ = t at hy
    rw [← hy]
    exact td_row_zero n hn y
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨le_rfl, fun p => ⟨p, dist_self p⟩⟩
    · refine ⟨by norm_num, fun p => ?_⟩
      obtain ⟨i, hi⟩ := p
      have key : ∃ j, ∃ hj : j < n, td n ⟨j, hj⟩ ⟨i, hi⟩ = 1 := by
        by_cases htri : n % 2 = 1 ∧ n - 3 ≤ i
        · by_cases hd : i = n - 3
          · refine ⟨n - 2, by omega, td_eq_one n (by simp; omega) ?_ ?_ ?_ ?_ ?_⟩ <;>
              simp only [part, blk, half, comp, pos] <;> split_ifs <;> omega
          · refine ⟨n - 3, by omega, td_eq_one n (by simp; omega) ?_ ?_ ?_ ?_ ?_⟩ <;>
              simp only [part, blk, half, comp, pos] <;> split_ifs <;> omega
        · by_cases he : i % 2 = 0
          · refine ⟨i + 1, ?_, td_eq_one n (by simp [Fin.ext_iff]) ?_ ?_ ?_ ?_ ?_⟩
            · omega
            all_goals simp only [part, blk, half, comp, pos]; split_ifs <;> omega
          · refine ⟨i - 1, by omega, td_eq_one n (by simp; omega) ?_ ?_ ?_ ?_ ?_⟩ <;>
              simp only [part, blk, half, comp, pos] <;> split_ifs <;> omega
      obtain ⟨j, hj, h⟩ := key
      exact ⟨(⟨j, hj⟩ : Fin n), h⟩
    · refine ⟨by norm_num, fun p => ?_⟩
      obtain ⟨i, hi⟩ := p
      have key : ∃ j, ∃ hj : j < n, td n ⟨j, hj⟩ ⟨i, hi⟩ = 2 := by
        by_cases hl : i < 4 * blk n i + 2
        · refine ⟨4 * blk n i + 2, ?_, td_eq_two n ?_ ?_ ?_ ?_⟩
          · simp only [blk]; split_ifs <;> omega
          · simp only [blk] at hl ⊢; simp only [ne_eq, Fin.mk.injEq]; split_ifs at hl ⊢ <;> omega
          all_goals simp only [part, blk, half] at hl ⊢; split_ifs at hl ⊢ <;> omega
        · refine ⟨4 * blk n i, ?_, td_eq_two n ?_ ?_ ?_ ?_⟩
          · simp only [blk]; split_ifs <;> omega
          · simp only [blk] at hl ⊢; simp only [ne_eq, Fin.mk.injEq]; split_ifs at hl ⊢ <;> omega
          all_goals simp only [part, blk, half] at hl ⊢; split_ifs at hl ⊢ <;> omega
      obtain ⟨j, hj, h⟩ := key
      exact ⟨(⟨j, hj⟩ : Fin n), h⟩
    · refine ⟨by norm_num, fun p => ?_⟩
      obtain ⟨i, hi⟩ := p
      refine ⟨(⟨if i < 4 then 4 else 0, by split_ifs <;> omega⟩ : Fin n), ?_⟩
      change td n _ ⟨i, hi⟩ = 4
      apply td_eq_four n
      simp only [part]
      split_ifs <;> omega

private lemma tree_center_card (hn : 8 ≤ n) : Nat.card (center (FourTree n)) = 4 := by
  rw [tree_center n hn, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem (by norm_num),
    Set.ncard_insert_of_notMem (by norm_num), Set.ncard_pair (by norm_num)]

/-- The `t`-th distance-one edge. -/
private def oneEdge (t : ℕ) : Sym2 ℕ :=
  if n % 2 = 1 ∧ n - 3 ≤ 2 * t then
    (if 2 * t = n - 3 then s(n - 3, n - 2) else s(n - 3, n - 1))
  else s(2 * t, 2 * t + 1)

/-- A pair `i < j` in one component at different positions is a distance-one edge. -/
private lemma one_hit (i j : ℕ) (hij : i < j) (hj : j < n)
    (hc : comp n i = comp n j) (hq : pos n i ≠ pos n j) :
    ∃ t < (n + 1) / 2, oneEdge n t = s(i, j) := by
  have key : (n % 2 = 1 ∧ n - 3 ≤ i) ∨
      (j = i + 1 ∧ i % 2 = 0 ∧ ¬ (n % 2 = 1 ∧ n - 3 ≤ j)) := by
    unfold comp at hc
    split_ifs at hc <;> omega
  rcases key with htri | ⟨rfl, he, hnt⟩
  · have hi : i = n - 3 := by
      unfold pos at hq
      split_ifs at hq <;> omega
    refine ⟨j / 2, by omega, ?_⟩
    unfold oneEdge
    split_ifs <;> simp only [Sym2.eq_iff] <;> omega
  · refine ⟨i / 2, by omega, ?_⟩
    unfold oneEdge
    split_ifs <;> simp only [Sym2.eq_iff] <;> omega

/-- The first halves of the blocks. -/
private def firstHalves : Finset ℕ :=
  (Finset.range (n / 4) ×ˢ Finset.range 2).image fun q => 4 * q.1 + q.2

private lemma firstHalves_card : (firstHalves n).card = 2 * (n / 4) := by
  rw [firstHalves, Finset.card_image_of_injOn, Finset.card_product, Finset.card_range,
    Finset.card_range, mul_comm]
  rintro ⟨k, u⟩ hku ⟨k', u'⟩ hku' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio] at hku hku'
  simp only at h
  simp only [Prod.mk.injEq]
  omega

private lemma firstHalves_sub : firstHalves n ⊆ Finset.range n := by
  intro j hj
  obtain ⟨⟨k, u⟩, hku, rfl⟩ := Finset.mem_image.mp hj
  simp only [Finset.mem_product, Finset.mem_range] at hku ⊢
  omega

private lemma mem_firstHalves (hn : 8 ≤ n) (k : ℕ) : k ∈ firstHalves n ↔ k < n ∧ half n k = 0 := by
  simp only [firstHalves, Finset.mem_image, Finset.mem_product, Finset.mem_range,
    Prod.exists, half, blk]
  constructor
  · rintro ⟨k', u, ⟨hk', hu⟩, rfl⟩
    refine ⟨by omega, ?_⟩
    split_ifs <;> omega
  · rintro ⟨hk, h0⟩
    split_ifs at h0 with h1 h2
    · exact ⟨k / 4, k - 4 * (k / 4), ⟨h1, by omega⟩, by omega⟩
    · exact ⟨n / 4 - 1, k - 4 * (n / 4 - 1), ⟨by omega, by omega⟩, by omega⟩

private lemma blk_le (k : ℕ) : 4 * blk n k ≤ k := by
  simp only [blk]; split_ifs <;> omega

private lemma half_cases (k : ℕ) : half n k = 0 ∨ half n k = 1 := by
  simp only [half]; split_ifs <;> simp

private lemma half_zero (k : ℕ) (h : half n k = 0) : k - 4 * blk n k < 2 := by
  simp only [half] at h; split_ifs at h with h'; omega

open Classical in
private lemma tree_edges_le (hn : 8 ≤ n) :
    (centralGraph (FourTree n)).edgeFinset.card ≤
      6 * n - 16 - 4 * (n / 4) + (n + 1) / 2 := by
  have hinj : Function.Injective (Sym2.map (fun x : FourTree n => (x : Fin n).1)) :=
    Sym2.map.injective Fin.val_injective
  rw [← Finset.card_image_of_injective _ hinj]
  have hsub : (centralGraph (FourTree n)).edgeFinset.image
      (Sym2.map (fun x : FourTree n => (x : Fin n).1)) ⊆
      ((Finset.range 4 ×ˢ Finset.range (n - 4)).image (fun q => s(q.1, q.2 + 4))) ∪
      ((Finset.range 2 ×ˢ (Finset.range n \ firstHalves n)).image
        (fun q => s(4 * blk n q.2 + q.1, q.2))) ∪
      ((Finset.range ((n + 1) / 2)).image (oneEdge n)) := by
    intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    induction e' using Sym2.ind with
    | h x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he'
      rw [Sym2.map_mk]
      have hxy : x ≠ y := he'.ne
      have hmem : td n x y ∈ center (FourTree n) := by
        simp only [centralGraph, SimpleGraph.fromRel_adj] at he'
        rcases he'.2 with h | h
        · exact h
        · rwa [dist_comm] at h
      rw [tree_center n hn] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      have hmem' : td n x y = 1 ∨ td n x y = 2 ∨ td n x y = 4 := by
        rcases hmem with h | h
        · have := (td_pos n hxy).1
          exfalso
          linarith
        · exact h
      obtain ⟨i, hi⟩ := x
      obtain ⟨j, hj⟩ := y
      have hij : i ≠ j := fun e => hxy (Fin.ext e)
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_range,
        Finset.mem_sdiff, Prod.exists]
      rcases td_central n hxy hmem' with hp | ⟨hp, hb, hh⟩ | ⟨hp, hb, hh, hc, hq⟩
      · left; left
        simp only [part] at hp
        by_cases hi4 : i < 4
        · exact ⟨i, j - 4, ⟨hi4, by split_ifs at hp <;> omega⟩, by
            rw [show j - 4 + 4 = j by split_ifs at hp <;> omega]⟩
        · refine ⟨j, i - 4, ⟨by split_ifs at hp <;> omega, by omega⟩, ?_⟩
          rw [show i - 4 + 4 = i by omega, Sym2.eq_swap]
      · left; right
        rcases half_cases n i with h0 | h0
        · have hj1 : half n j ≠ 0 := fun h => hh (h0.trans h.symm)
          refine ⟨i - 4 * blk n i, j, ⟨half_zero n i h0, hj,
            fun hjf => hj1 ((mem_firstHalves n hn j).mp hjf).2⟩, ?_⟩
          rw [← hb, show 4 * blk n i + (i - 4 * blk n i) = i by have := blk_le n i; omega]
        · have hj0 : half n j = 0 := by
            rcases half_cases n j with h | h
            · exact h
            · exact absurd (h0.trans h.symm) hh
          have hi1 : half n i ≠ 0 := by rw [h0]; norm_num
          refine ⟨j - 4 * blk n j, i, ⟨half_zero n j hj0, hi,
            fun hif => hi1 ((mem_firstHalves n hn i).mp hif).2⟩, ?_⟩
          rw [hb, show 4 * blk n j + (j - 4 * blk n j) = j by have := blk_le n j; omega,
            Sym2.eq_swap]
      · right
        rcases lt_or_gt_of_ne hij with hlt | hlt
        · exact one_hit n i j hlt hj hc hq
        · obtain ⟨t, ht, he⟩ := one_hit n j i hlt hi hc.symm (Ne.symm hq)
          exact ⟨t, ht, by rw [he, Sym2.eq_swap]⟩
  have hS1 : (Finset.range n \ firstHalves n).card = n - 2 * (n / 4) := by
    have := Finset.card_sdiff_add_card_eq_card (firstHalves_sub n)
    rw [Finset.card_range, firstHalves_card] at this
    omega
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (Finset.range 4 ×ˢ Finset.range (n - 4)).card +
          (Finset.range 2 ×ˢ (Finset.range n \ firstHalves n)).card +
          (Finset.range ((n + 1) / 2)).card :=
        Nat.add_le_add (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
          Finset.card_image_le
    _ = 6 * n - 16 - 4 * (n / 4) + (n + 1) / 2 := by
        rw [Finset.card_product, Finset.card_product, hS1, Finset.card_range,
          Finset.card_range, Finset.card_range, Finset.card_range]
        omega

end Tree

open Classical in
/-- For every `n`, a four-central ultrametric on `n` points has `n ≥ 8` and at least
`6n - 16 - 4 ⌊n / 4⌋ + ⌈n / 2⌉` central edges: writing its center as `{0, a, b, D}` with
`0 < a < b < D`, the central edges split by length, the length `D` has at least `4 (n - 4)`,
the length `b` at least `2n - 4 ⌊n / 4⌋` and the length `a` at least `⌈n / 2⌉` edges. For every
`n ≥ 8` a seven-level hierarchical ultrametric attains the bound. -/
theorem ultra_four_central_minimum (n : ℕ) :
    (∀ (X : Type) [Fintype X] [MetricSpace X] [IsUltrametricDist X], Fintype.card X = n →
      Nat.card (center X) = 4 →
      8 ≤ n ∧ 6 * n - 16 - 4 * (n / 4) + (n + 1) / 2 ≤ (centralGraph X).edgeFinset.card ∧
      ∀ a b D : ℝ, 0 < a → a < b → b < D → center X = {0, a, b, D} →
        (centralGraph X).edgeFinset.card =
          (lengthEdges X D).card + (lengthEdges X b).card + (lengthEdges X a).card ∧
        4 * (n - 4) ≤ (lengthEdges X D).card ∧ 2 * n - 4 * (n / 4) ≤ (lengthEdges X b).card ∧
        (n + 1) / 2 ≤ (lengthEdges X a).card) ∧
    (8 ≤ n → ∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X) (_ : IsUltrametricDist X),
      Fintype.card X = n ∧ Nat.card (center X) = 4 ∧
      (centralGraph X).edgeFinset.card = 6 * n - 16 - 4 * (n / 4) + (n + 1) / 2) := by
  refine ⟨fun X _ _ _ hX hk => ?_, fun hn => ?_⟩
  · have hX2 := two_le_card hk
    obtain ⟨p⟩ : Nonempty X := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨a, b, D, ha, hab, hbD, hC, -⟩ := center_shape hk
    obtain ⟨h8, hsplit, hDb, hbb, hA⟩ := general ha hab hbD hC p
    rw [hX] at h8 hDb hbb hA
    refine ⟨h8, by omega, fun a' b' D' ha' hab' hbD' hC' => ?_⟩
    obtain ⟨-, hsplit', hDb', hbb', hA'⟩ := general ha' hab' hbD' hC' p
    rw [hX] at hDb' hbb' hA'
    exact ⟨hsplit', hDb', hbb', hA'⟩
  · have hcard : Fintype.card (FourTree n) = n := Fintype.card_fin n
    refine ⟨FourTree n, inferInstance, inferInstance, inferInstance, hcard,
      tree_center_card n hn, le_antisymm (tree_edges_le n hn) ?_⟩
    obtain ⟨-, hsplit, hDb, hbb, hA⟩ := general (X := FourTree n) (a := 1) (b := 2) (D := 4)
      (by norm_num) (by norm_num) (by norm_num) (tree_center n hn) ⟨0, by omega⟩
    rw [hcard] at hDb hbb hA
    omega

end

end D5.S3.Combinatorics.Geometry.Ultrametric.FourCentralMinimum
