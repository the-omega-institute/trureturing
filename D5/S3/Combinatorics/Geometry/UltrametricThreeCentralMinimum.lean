/- GID: D5/S3/Combinatorics/Geometry/UltrametricThreeCentralMinimum
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/UltrametricThreeCentralMinimum
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Three-central n-point ultrametrics have at least 2n-4+⌈n/2⌉ central edges, sharply. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#320)
escape_witness: class_bound (the class of points below the diameter from a fixed point is fully
  joined to its complement at the diameter, and both have at least two points), with general
  (the equality analysis: a class product of exactly 2(n-2) forces parts of sizes 2 and n-2) and
  tree_edges_le (the hierarchical ultrametric has at most 2n-4+⌈n/2⌉ central edges).
proof_shape:
  part, comp, pos, td, Tree, oneEdge: definitions; consumers: the Tree lemmas and the theorem.
  center_shape, class_bound: content; consumer: general.
  general: content; consumer: ultra_three_central_minimum.
  td_ultra: content; consumers: td_triangle, the IsUltrametricDist instance.
  tree_center: content; consumers: tree_center_card, tree_edges_le.
  one_hit: content; consumer: tree_edges_le.
  tree_edges_le: content; consumer: ultra_three_central_minimum.
  edges_split, mem_lengthEdges_iff, mem_lengthEdges_D, mem_image_pairs, image_pairs_card,
    diam_adj_iff, sdiff_edges, td_self, td_comm, td_pos, td_nonneg, td_triangle, td_eq_two,
    td_eq_one, td_central, td_row_zero, tree_center_card: bind-only helpers; consumers:
    class_bound, general, the Tree instances, tree_center, tree_edges_le and the theorem.
  ultra_three_central_minimum: content.
Direct frozen dependencies: D5/S3/Combinatorics/Geometry/CentralEdgeCover (len, lengthEdges,
  lengthEdges_card; made public here and re-pinned),
  D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders (exists_central_bound; made public
  here and re-pinned), D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges (center,
  centralGraph, diametricalGraph).
Search record (§3.1): the maximum distance of a finite ultrametric being central and the
  per-length cover bound were private in frozen modules and are made public instead of
  re-proved; no frozen module bounds the diameter edges of an ultrametric.
  UltrametricConstantJoin (ConstantCrossDistance.Join, crossDist_triangle_max, center_eq) was
  considered for building Tree n as nested joins, but the number of components depends on n
  and odd n needs the triple with an inner distance, so the four-level metric is direct.
-/

import D5.S3.Combinatorics.Geometry.CentralEdgeCover
import D5.S3.Combinatorics.Geometry.UltrametricCenterSphereOrders

/-! # The sharp three-central ultrametric minimum

For `n ≥ 4`, a three-central ultrametric on `n` points has center `{0, a, D}` with `D` its
diameter. The points at distance below `D` from a fixed point form a class `S` that is joined to
its complement entirely at distance `D`; both `S` and its complement have at least two points, so
there are at least `|S| (n - |S|) ≥ 2 (n - 2)` diameter edges, and the length `a` contributes at
least `⌈n / 2⌉` further edges. Equality holds exactly when the diametrical graph is complete
bipartite with parts of sizes `2` and `n - 2` and the length `a` has exactly `⌈n / 2⌉` edges.
A four-level hierarchical ultrametric attains the bound.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Geometry.UltrametricThreeCentralMinimum

open D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges
open D5.S3.Combinatorics.Geometry.CentralEdgeCover

noncomputable section

section General

variable {X : Type} [Fintype X] [MetricSpace X] [IsUltrametricDist X]

/-- In a finite ultrametric with three central values, the center is `{0, a, D}` with
`0 < a < D`, all distances are at most `D`, and `D` is the diameter. -/
private lemma center_shape (hX : 2 ≤ Fintype.card X) (hk : Nat.card (center X) = 3) :
    ∃ a D : ℝ, 0 < a ∧ a < D ∧ center X = {0, a, D} ∧ (∀ x y : X, dist x y ≤ D) ∧
      Metric.diam (Set.univ : Set X) = D := by
  have : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨D, hD, hbound⟩ := UltrametricCenterSphereOrders.exists_central_bound (X := X)
  have hfin : (center X).Finite := by
    obtain ⟨p⟩ := ‹Nonempty X›
    exact (Set.finite_range fun y => dist y p).subset (fun t ht => ht.2 p)
  have h0 : (0 : ℝ) ∈ center X := ⟨le_rfl, fun x => ⟨x, dist_self x⟩⟩
  obtain ⟨u, v, huv⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card X)
  have hDpos : 0 < D := lt_of_lt_of_le (dist_pos.mpr huv) (hbound u v)
  have hk' : (center X).ncard = 3 := by rwa [← Nat.card_coe_set_eq]
  obtain ⟨a, ha, hane⟩ : ∃ a ∈ center X, a ∉ ({0, D} : Set ℝ) := by
    by_contra hcon
    push Not at hcon
    have := Set.ncard_le_ncard (show center X ⊆ {0, D} from hcon) (Set.toFinite _)
    rw [Set.ncard_pair hDpos.ne] at this
    omega
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hane
  obtain ⟨p⟩ := ‹Nonempty X›
  obtain ⟨y, hy⟩ := ha.2 p
  have haD : a < D := lt_of_le_of_ne (hy ▸ hbound y p) hane.2
  have hapos : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm hane.1)
  refine ⟨a, D, hapos, haD, ?_, hbound, ?_⟩
  · symm
    apply Set.eq_of_subset_of_ncard_le
    · intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl
      · exact h0
      · exact ha
      · exact hD
    · rw [hk', Set.ncard_insert_of_notMem (by simp; constructor <;> linarith),
        Set.ncard_pair haD.ne]
    · exact hfin
  · apply le_antisymm
    · exact Metric.diam_le_of_forall_dist_le hDpos.le fun x _ y _ => hbound x y
    · obtain ⟨z, hz⟩ := hD.2 p
      rw [← hz]
      exact Metric.dist_le_diam_of_mem (Set.toFinite _).isBounded (Set.mem_univ _)
        (Set.mem_univ _)

omit [IsUltrametricDist X] in
open Classical in
/-- The central edges split into those of length `D` and those of length `a`. -/
private lemma edges_split {a D : ℝ} (haD : a < D) (hC : center X = {0, a, D}) :
    (centralGraph X).edgeFinset.card = (lengthEdges X D).card + (lengthEdges X a).card := by
  rw [← Finset.card_filter_add_card_filter_not (fun e => len e = D)]
  congr 1
  apply congrArg Finset.card
  ext e
  simp only [lengthEdges, Finset.mem_filter]
  constructor
  · rintro ⟨he, hne⟩
    refine ⟨he, ?_⟩
    induction e using Sym2.ind with
    | h x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      simp only [len, Sym2.lift_mk] at hne ⊢
      have hxy : x ≠ y := he.ne
      have hmem : dist x y ∈ center X := by
        simp only [centralGraph, SimpleGraph.fromRel_adj] at he
        rcases he.2 with h | h
        · exact h
        · rwa [dist_comm] at h
      rw [hC] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h
      · exact absurd (dist_eq_zero.mp h) hxy
      · exact h
      · exact absurd h hne
  · rintro ⟨he, h⟩
    exact ⟨he, by rw [h]; exact haD.ne⟩

omit [IsUltrametricDist X] in
open Classical in
private lemma mem_lengthEdges_iff {t : ℝ} (x y : X) :
    s(x, y) ∈ lengthEdges X t ↔ (centralGraph X).Adj x y ∧ dist x y = t := by
  unfold lengthEdges
  rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  simp only [len, Sym2.lift_mk]

omit [IsUltrametricDist X] in
open Classical in
/-- A diameter edge is a central edge of length `D`. -/
private lemma mem_lengthEdges_D {D : ℝ} (hD : D ∈ center X) {u v : X} (huv : u ≠ v)
    (h : dist u v = D) : s(u, v) ∈ lengthEdges X D := by
  rw [mem_lengthEdges_iff]
  refine ⟨?_, h⟩
  simp only [centralGraph, SimpleGraph.fromRel_adj]
  exact ⟨huv, Or.inl (h ▸ hD)⟩

omit [Fintype X] [MetricSpace X] [IsUltrametricDist X] in
/-- The pairs across a set and its complement. -/
private lemma mem_image_pairs [Fintype X] [DecidableEq X] (A : Finset X) (x y : X) :
    s(x, y) ∈ (A ×ˢ Aᶜ).image (fun q => s(q.1, q.2)) ↔ (x ∈ A ↔ y ∉ A) := by
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_compl, Prod.exists, Sym2.eq_iff]
  constructor
  · rintro ⟨u, v, ⟨hu, hv⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨fun _ => hv, fun _ => hu⟩
    · exact ⟨fun h => absurd h hv, fun h => absurd hu h⟩
  · intro h
    by_cases hx : x ∈ A
    · exact ⟨x, y, ⟨hx, h.mp hx⟩, Or.inl ⟨rfl, rfl⟩⟩
    · have hy : y ∈ A := by by_contra hy; exact hx (h.mpr hy)
      exact ⟨y, x, ⟨hy, hx⟩, Or.inr ⟨rfl, rfl⟩⟩

omit [Fintype X] [MetricSpace X] [IsUltrametricDist X] in
private lemma image_pairs_card [Fintype X] [DecidableEq X] (A : Finset X) :
    ((A ×ˢ Aᶜ).image (fun q => s(q.1, q.2))).card = A.card * Aᶜ.card := by
  rw [Finset.card_image_of_injOn, Finset.card_product]
  rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at huv huv'
  simp only [Sym2.eq_iff] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd huv.1 (Finset.mem_compl.mp huv'.2)

open Classical in
/-- The class `S` of a point at distance below `D` and its complement are fully joined at
distance `D`, so there are at least `|S| (n - |S|)` edges of length `D`. -/
private lemma class_bound {a D : ℝ} (ha : 0 < a) (haD : a < D) (hC : center X = {0, a, D})
    (hbound : ∀ x y : X, dist x y ≤ D) (p : X) :
    let S := Finset.univ.filter fun y => dist p y < D
    2 ≤ S.card ∧ 2 ≤ Sᶜ.card ∧ (S ×ˢ Sᶜ).image (fun q => s(q.1, q.2)) ⊆ lengthEdges X D ∧
      ((S ×ˢ Sᶜ).image (fun q => s(q.1, q.2))).card = S.card * Sᶜ.card := by
  intro S
  have haC : a ∈ center X := by rw [hC]; simp
  have hDC : D ∈ center X := by rw [hC]; simp
  have hcross : ∀ u ∈ S, ∀ v ∈ Sᶜ, u ≠ v ∧ dist u v = D := by
    intro u hu v hv
    simp only [S, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      not_lt] at hu hv
    have huv : dist u v = D := by
      refine le_antisymm (hbound u v) ?_
      by_contra hlt
      push Not at hlt
      have := IsUltrametricDist.dist_triangle_max p u v
      have : max (dist p u) (dist u v) < D := max_lt hu hlt
      linarith
    refine ⟨?_, huv⟩
    rintro rfl
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := haC.2 p
    have hyp : y ≠ p := by rintro rfl; rw [dist_self] at hy; linarith
    have : ({p, y} : Finset X) ⊆ S := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hz with rfl | rfl
      · rw [dist_self]; linarith
      · rw [dist_comm, hy]; exact haD
    calc 2 = ({p, y} : Finset X).card := (Finset.card_pair (Ne.symm hyp)).symm
      _ ≤ S.card := Finset.card_le_card this
  · obtain ⟨z, hz⟩ := hDC.2 p
    obtain ⟨w, hw⟩ := haC.2 z
    have hwz : w ≠ z := by rintro rfl; rw [dist_self] at hw; linarith
    have hzS : z ∈ Sᶜ := by
      simp only [S, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      rw [dist_comm, hz]
    have hwS : w ∈ Sᶜ := by
      simp only [S, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      by_contra hlt
      push Not at hlt
      have := IsUltrametricDist.dist_triangle_max p w z
      have : max (dist p w) (dist w z) < D := max_lt hlt (hw ▸ haD)
      rw [dist_comm p z, hz] at *
      linarith
    have : ({z, w} : Finset X) ⊆ Sᶜ := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hzS
      · exact hwS
    calc 2 = ({z, w} : Finset X).card := (Finset.card_pair (Ne.symm hwz)).symm
      _ ≤ Sᶜ.card := Finset.card_le_card this
  · intro e he
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    obtain ⟨hne, hd⟩ := hcross u hu v hv
    exact mem_lengthEdges_D hDC hne hd
  · exact image_pairs_card S

omit [IsUltrametricDist X] in
open Classical in
/-- Diametrical adjacency is membership among the central edges of length `D`. -/
private lemma diam_adj_iff {D : ℝ} (hD : D ∈ center X)
    (hdiam : Metric.diam (Set.univ : Set X) = D) (x y : X) :
    (diametricalGraph X).Adj x y ↔ s(x, y) ∈ lengthEdges X D := by
  rw [mem_lengthEdges_iff]
  simp only [diametricalGraph, centralGraph, SimpleGraph.fromRel_adj, hdiam, dist_comm y x,
    or_self]
  constructor
  · rintro ⟨hxy, h⟩
    exact ⟨⟨hxy, h ▸ hD⟩, h⟩
  · rintro ⟨⟨hxy, _⟩, h⟩
    exact ⟨hxy, h⟩

omit [IsUltrametricDist X] in
open Classical in
/-- The non-diametrical central edges are the central edges of length `a`. -/
private lemma sdiff_edges {a D : ℝ} (haD : a < D) (hC : center X = {0, a, D})
    (hdiam : Metric.diam (Set.univ : Set X) = D) :
    (centralGraph X \ diametricalGraph X).edgeFinset = lengthEdges X a := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.sdiff_adj,
      mem_lengthEdges_iff]
    have hcd : (centralGraph X).Adj x y → dist x y = a ∨ dist x y = D := by
      intro hc
      have hxy : x ≠ y := hc.ne
      have hmem : dist x y ∈ center X := by
        simp only [centralGraph, SimpleGraph.fromRel_adj] at hc
        rcases hc.2 with h | h
        · exact h
        · rwa [dist_comm] at h
      rw [hC] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h
      · exact absurd (dist_eq_zero.mp h) hxy
      · exact Or.inl h
      · exact Or.inr h
    have hdg : (diametricalGraph X).Adj x y ↔ x ≠ y ∧ dist x y = D := by
      simp only [diametricalGraph, SimpleGraph.fromRel_adj, hdiam, dist_comm y x, or_self]
    rw [hdg]
    constructor
    · rintro ⟨hc, hnd⟩
      refine ⟨hc, ?_⟩
      rcases hcd hc with h | h
      · exact h
      · exact absurd ⟨hc.ne, h⟩ hnd
    · rintro ⟨hc, h⟩
      exact ⟨hc, fun ⟨_, h'⟩ => haD.ne (h.symm.trans h')⟩

open Classical in
/-- The general lower bound together with its equality analysis. -/
private lemma general (n : ℕ) (hn : 4 ≤ n) (hX : Fintype.card X = n)
    (hk : Nat.card (center X) = 3) :
    2 * n - 4 + (n + 1) / 2 ≤ (centralGraph X).edgeFinset.card ∧
      ((centralGraph X).edgeFinset.card = 2 * n - 4 + (n + 1) / 2 ↔
        (∃ A : Finset X, A.card = 2 ∧
          ∀ x y : X, (diametricalGraph X).Adj x y ↔ (x ∈ A ↔ y ∉ A)) ∧
        (centralGraph X \ diametricalGraph X).edgeFinset.card = (n + 1) / 2) := by
  obtain ⟨a, D, ha, haD, hC, hbound, hdiam⟩ := center_shape (by omega) hk
  have haC : a ∈ center X := by rw [hC]; simp
  have hDC : D ∈ center X := by rw [hC]; simp
  have hsplit := edges_split haD hC
  have hEa := lengthEdges_card X haC ha.ne'
  rw [hX] at hEa
  obtain ⟨p⟩ : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨hS2, hSc2, hsub, hcard⟩ := class_bound ha haD hC hbound p
  set S := Finset.univ.filter fun y => dist p y < D with hSdef
  have hsum : S.card + Sᶜ.card = n := by rw [Finset.card_add_card_compl, hX]
  have hED : S.card * Sᶜ.card ≤ (lengthEdges X D).card := hcard ▸ Finset.card_le_card hsub
  have hprod : 2 * (n - 2) ≤ S.card * Sᶜ.card := by
    obtain ⟨s', hs'⟩ : ∃ s', S.card = s' + 2 := ⟨S.card - 2, by omega⟩
    obtain ⟨t', ht'⟩ : ∃ t', Sᶜ.card = t' + 2 := ⟨Sᶜ.card - 2, by omega⟩
    rw [hs', ht']
    have : n - 2 = s' + t' + 2 := by omega
    rw [this]
    nlinarith
  have hsd := sdiff_edges haD hC hdiam
  refine ⟨by omega, ⟨fun heq => ?_, fun ⟨⟨A, hA, hadj⟩, hcnt⟩ => ?_⟩⟩
  · have hD2 : (lengthEdges X D).card = 2 * (n - 2) := by omega
    have hEa' : (lengthEdges X a).card = (n + 1) / 2 := by omega
    have hst : S.card * Sᶜ.card = 2 * (n - 2) := by omega
    have himg : (S ×ˢ Sᶜ).image (fun q => s(q.1, q.2)) = lengthEdges X D :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; omega)
    have h2 : S.card = 2 ∨ Sᶜ.card = 2 := by
      obtain ⟨s', hs'⟩ : ∃ s', S.card = s' + 2 := ⟨S.card - 2, by omega⟩
      obtain ⟨t', ht'⟩ : ∃ t', Sᶜ.card = t' + 2 := ⟨Sᶜ.card - 2, by omega⟩
      rw [hs', ht'] at hst ⊢
      have : n - 2 = s' + t' + 2 := by omega
      rw [this] at hst
      have : s' * t' = 0 := by nlinarith
      rcases Nat.mul_eq_zero.mp this with h | h
      · left; omega
      · right; omega
    refine ⟨?_, by rw [hsd, hEa']⟩
    have hS : ∀ x y : X, (diametricalGraph X).Adj x y ↔ (x ∈ S ↔ y ∉ S) := fun x y => by
      rw [diam_adj_iff hDC hdiam, ← himg, mem_image_pairs]
    rcases h2 with h2 | h2
    · exact ⟨S, h2, hS⟩
    · refine ⟨Sᶜ, h2, fun x y => ?_⟩
      rw [hS, Finset.mem_compl, Finset.mem_compl]
      tauto
  · have himg : (A ×ˢ Aᶜ).image (fun q => s(q.1, q.2)) = lengthEdges X D := by
      ext e
      induction e using Sym2.ind with
      | h x y => rw [mem_image_pairs, ← diam_adj_iff hDC hdiam, hadj]
    have hAc : Aᶜ.card = n - 2 := by rw [Finset.card_compl, hX, hA]
    have hD2 : (lengthEdges X D).card = 2 * (n - 2) := by
      rw [← himg, image_pairs_card, hA, hAc]
    rw [hsd] at hcnt
    omega

end General

/-! ### The attaining ultrametric -/

section Tree

variable (n : ℕ)

/-- The part of a point: `0` for the pair `{0, 1}`, `1` otherwise. -/
private def part (i : ℕ) : ℕ := if i < 2 then 0 else 1

/-- The component of a point: the pair `{0, 1}`, the pairs `{2k, 2k+1}`, and for odd `n` the
triple `{n-3, n-2, n-1}`. -/
private def comp (i : ℕ) : ℕ :=
  if i < 2 then 0 else if n % 2 = 1 ∧ n - 3 ≤ i then n else (i - 2) / 2 + 1

/-- The position inside a component; in the triple, `n - 3` is designated. -/
private def pos (i : ℕ) : ℕ :=
  if n % 2 = 1 ∧ n - 3 ≤ i ∧ 2 ≤ i then (if i = n - 3 then 0 else 1) else i % 2

/-- The four-level distance: `2` across parts, `3/2` across components, `1` across positions,
`1/2` inside the triple's undesignated pair. -/
private def td (x y : Fin n) : ℝ :=
  if x = y then 0
  else if part x.1 ≠ part y.1 then 2
  else if comp n x.1 ≠ comp n y.1 then 3 / 2
  else if pos n x.1 ≠ pos n y.1 then 1
  else 1 / 2

private lemma td_self (x : Fin n) : td n x x = 0 := by unfold td; simp only [↓reduceIte]

private lemma td_comm (x y : Fin n) : td n x y = td n y x := by
  unfold td
  by_cases h : x = y
  · subst h; rfl
  · simp only [h, Ne.symm h, ↓reduceIte, ne_comm]

private lemma td_pos {x y : Fin n} (h : x ≠ y) : 1 / 2 ≤ td n x y ∧ td n x y ≤ 2 := by
  unfold td
  simp only [h, ↓reduceIte]
  split_ifs <;> norm_num

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
  split_ifs <;> first | (exfalso; omega) | norm_num

private lemma td_nonneg (x y : Fin n) : 0 ≤ td n x y := by
  by_cases h : x = y
  · rw [h, td_self]
  · exact le_trans (by norm_num) (td_pos n h).1

private lemma td_triangle (x y z : Fin n) : td n x z ≤ td n x y + td n y z :=
  (td_ultra n x y z).trans (max_le_add_of_nonneg (td_nonneg n x y) (td_nonneg n y z))

private lemma td_eq_two {x y : Fin n} (h : part x.1 ≠ part y.1) : td n x y = 2 := by
  have hxy : x ≠ y := by rintro rfl; exact h rfl
  unfold td; simp only [hxy, h, ↓reduceIte, ne_eq, not_false_eq_true]

private lemma td_eq_one {x y : Fin n} (hxy : x ≠ y) (hp : part x.1 = part y.1)
    (hc : comp n x.1 = comp n y.1) (hq : pos n x.1 ≠ pos n y.1) : td n x y = 1 := by
  unfold td; simp only [hxy, hp, hc, hq, ↓reduceIte, ne_eq, not_true_eq_false,
    not_false_eq_true]

/-- Distinct points at distance `1` or `2` lie in different parts, or in one component at
different positions. -/
private lemma td_central {x y : Fin n} (hxy : x ≠ y)
    (h : td n x y = 0 ∨ td n x y = 1 ∨ td n x y = 2) :
    part x.1 ≠ part y.1 ∨
      (part x.1 = part y.1 ∧ comp n x.1 = comp n y.1 ∧ pos n x.1 ≠ pos n y.1) := by
  by_cases hp : part x.1 = part y.1
  · right
    by_cases hc : comp n x.1 = comp n y.1
    · by_cases hq : pos n x.1 = pos n y.1
      · exfalso
        unfold td at h
        simp only [hxy, hp, hc, hq, ↓reduceIte, ne_eq, not_true_eq_false] at h
        norm_num at h
      · exact ⟨hp, hc, hq⟩
    · exfalso
      unfold td at h
      simp only [hxy, hp, hc, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true] at h
      norm_num at h
  · exact Or.inl hp

/-- The distances from the point `0` are `0`, `1` and `2`. -/
private lemma td_row_zero (hn : 4 ≤ n) (y : Fin n) :
    td n y ⟨0, by omega⟩ = 0 ∨ td n y ⟨0, by omega⟩ = 1 ∨ td n y ⟨0, by omega⟩ = 2 := by
  obtain ⟨i, hi⟩ := y
  by_cases h0 : i = 0
  · subst h0; left; exact td_self n _
  by_cases h1 : i = 1
  · subst h1
    right; left
    apply td_eq_one n (by simp)
    · simp [part]
    · simp [comp]
    · simp only [pos]; split_ifs <;> omega
  · right; right
    apply td_eq_two n
    simp only [part]; split_ifs <;> omega

/-- The points of `Fin n` with the four-level ultrametric. -/
def Tree : Type := Fin n

instance : Fintype (Tree n) := inferInstanceAs (Fintype (Fin n))

noncomputable instance : MetricSpace (Tree n) where
  dist x y := td n x y
  dist_self x := td_self n x
  dist_comm x y := td_comm n x y
  dist_triangle x y z := td_triangle n x y z
  eq_of_dist_eq_zero {x y} h := by
    by_contra hne
    have := (td_pos n hne).1
    change td n x y = 0 at h
    linarith

instance : IsUltrametricDist (Tree n) := ⟨fun x y z => td_ultra n x y z⟩

private lemma tree_center (hn : 4 ≤ n) : center (Tree n) = {0, 1, 2} := by
  ext t
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, ht⟩
    obtain ⟨y, hy⟩ := ht (⟨0, by omega⟩ : Fin n)
    change td n y ⟨0, by omega⟩ = t at hy
    rw [← hy]
    exact td_row_zero n hn y
  · rintro (rfl | rfl | rfl)
    · exact ⟨le_rfl, fun p => ⟨p, dist_self p⟩⟩
    · refine ⟨by norm_num, fun p => ?_⟩
      obtain ⟨i, hi⟩ := p
      have key : ∃ j, ∃ hj : j < n, td n ⟨j, hj⟩ ⟨i, hi⟩ = 1 := by
        by_cases htri : n % 2 = 1 ∧ n - 3 ≤ i ∧ 2 ≤ i
        · by_cases hd : i = n - 3
          · refine ⟨n - 2, by omega, td_eq_one n (by simp; omega) ?_ ?_ ?_⟩ <;>
              simp only [part, comp, pos] <;> split_ifs <;> omega
          · refine ⟨n - 3, by omega, td_eq_one n (by simp; omega) ?_ ?_ ?_⟩ <;>
              simp only [part, comp, pos] <;> split_ifs <;> omega
        · by_cases he : i % 2 = 0
          · refine ⟨i + 1, ?_, td_eq_one n (by simp [Fin.ext_iff]) ?_ ?_ ?_⟩
            · by_contra hlt
              apply htri
              have : n % 2 = 1 := by omega
              exact ⟨this, by omega, by omega⟩
            all_goals simp only [part, comp, pos]; split_ifs <;> omega
          · refine ⟨i - 1, by omega, td_eq_one n (by simp; omega) ?_ ?_ ?_⟩ <;>
              simp only [part, comp, pos] <;> split_ifs <;> omega
      obtain ⟨j, hj, h⟩ := key
      exact ⟨(⟨j, hj⟩ : Fin n), h⟩
    · refine ⟨by norm_num, fun p => ?_⟩
      obtain ⟨i, hi⟩ := p
      refine ⟨(⟨if i < 2 then 2 else 0, by split_ifs <;> omega⟩ : Fin n), ?_⟩
      change td n _ ⟨i, hi⟩ = 2
      apply td_eq_two n
      simp only [part]
      split_ifs <;> omega

private lemma tree_center_card (hn : 4 ≤ n) : Nat.card (center (Tree n)) = 3 := by
  rw [tree_center n hn, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem (by norm_num),
    Set.ncard_pair (by norm_num)]

/-- The `t`-th distance-one edge. -/
private def oneEdge (t : ℕ) : Sym2 ℕ :=
  if n % 2 = 1 ∧ n - 3 ≤ 2 * t then
    (if 2 * t = n - 3 then s(n - 3, n - 2) else s(n - 3, n - 1))
  else s(2 * t, 2 * t + 1)

/-- A pair `i < j` in one component at different positions is a distance-one edge. -/
private lemma one_hit (hn : 4 ≤ n) (i j : ℕ) (hij : i < j) (hj : j < n)
    (hc : comp n i = comp n j) (hq : pos n i ≠ pos n j) :
    ∃ t < (n + 1) / 2, oneEdge n t = s(i, j) := by
  have key : j < 2 ∨ (n % 2 = 1 ∧ n - 3 ≤ i ∧ 2 ≤ i) ∨
      (2 ≤ i ∧ j = i + 1 ∧ i % 2 = 0 ∧ ¬ (n % 2 = 1 ∧ n - 3 ≤ j)) := by
    unfold comp at hc
    split_ifs at hc <;> omega
  rcases key with h2 | htri | ⟨hi2, rfl, he, hnt⟩
  · refine ⟨0, by omega, ?_⟩
    unfold oneEdge
    split_ifs <;> simp only [Sym2.eq_iff] <;> omega
  · have hi : i = n - 3 := by
      unfold pos at hq
      split_ifs at hq <;> omega
    refine ⟨j / 2, by omega, ?_⟩
    unfold oneEdge
    split_ifs <;> simp only [Sym2.eq_iff] <;> omega
  · refine ⟨i / 2, by omega, ?_⟩
    unfold oneEdge
    split_ifs <;> simp only [Sym2.eq_iff] <;> omega

open Classical in
private lemma tree_edges_le (hn : 4 ≤ n) :
    (centralGraph (Tree n)).edgeFinset.card ≤ 2 * n - 4 + (n + 1) / 2 := by
  have hinj : Function.Injective (Sym2.map (fun x : Tree n => (x : Fin n).1)) :=
    Sym2.map.injective Fin.val_injective
  rw [← Finset.card_image_of_injective _ hinj]
  have hsub : (centralGraph (Tree n)).edgeFinset.image
      (Sym2.map (fun x : Tree n => (x : Fin n).1)) ⊆
      ((Finset.range 2 ×ˢ Finset.range (n - 2)).image (fun q => s(q.1, q.2 + 2))) ∪
      ((Finset.range ((n + 1) / 2)).image (oneEdge n)) := by
    intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    induction e' using Sym2.ind with
    | h x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he'
      rw [Sym2.map_mk]
      have hxy : x ≠ y := he'.ne
      have hmem : td n x y ∈ center (Tree n) := by
        simp only [centralGraph, SimpleGraph.fromRel_adj] at he'
        rcases he'.2 with h | h
        · exact h
        · rwa [dist_comm] at h
      rw [tree_center n hn] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      obtain ⟨i, hi⟩ := x
      obtain ⟨j, hj⟩ := y
      have hij : i ≠ j := fun e => hxy (Fin.ext e)
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_range,
        Prod.exists]
      rcases td_central n hxy hmem with hp | ⟨hp, hc, hq⟩
      · left
        simp only [part] at hp
        by_cases hi2 : i < 2
        · exact ⟨i, j - 2, ⟨hi2, by split_ifs at hp <;> omega⟩, by
            rw [show j - 2 + 2 = j by split_ifs at hp <;> omega]⟩
        · refine ⟨j, i - 2, ⟨by split_ifs at hp <;> omega, by omega⟩, ?_⟩
          rw [show i - 2 + 2 = i by omega, Sym2.eq_swap]
      · right
        rcases lt_or_gt_of_ne hij with hlt | hlt
        · exact one_hit n hn i j hlt hj hc hq
        · obtain ⟨t, ht, he⟩ := one_hit n hn j i hlt hi hc.symm (Ne.symm hq)
          exact ⟨t, ht, by rw [he, Sym2.eq_swap]⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ (Finset.range 2 ×ˢ Finset.range (n - 2)).card + (Finset.range ((n + 1) / 2)).card :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * n - 4 + (n + 1) / 2 := by
        rw [Finset.card_product, Finset.card_range, Finset.card_range, Finset.card_range]
        omega

end Tree

open Classical in
/-- For `n ≥ 4`, every three-central ultrametric on `n` points has at least `2n - 4 + ⌈n/2⌉`
central edges, with equality exactly when its diametrical graph is complete bipartite with a
part of two points and its non-diametrical central edges number `⌈n/2⌉`; a four-level
hierarchical ultrametric attains the bound. -/
theorem ultra_three_central_minimum (n : ℕ) (hn : 4 ≤ n) :
    (∀ (X : Type) [Fintype X] [MetricSpace X] [IsUltrametricDist X], Fintype.card X = n →
      Nat.card (center X) = 3 →
      2 * n - 4 + (n + 1) / 2 ≤ (centralGraph X).edgeFinset.card ∧
      ((centralGraph X).edgeFinset.card = 2 * n - 4 + (n + 1) / 2 ↔
        (∃ A : Finset X, A.card = 2 ∧
          ∀ x y : X, (diametricalGraph X).Adj x y ↔ (x ∈ A ↔ y ∉ A)) ∧
        (centralGraph X \ diametricalGraph X).edgeFinset.card = (n + 1) / 2)) ∧
    ∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X) (_ : IsUltrametricDist X),
      Fintype.card X = n ∧ Nat.card (center X) = 3 ∧
      (centralGraph X).edgeFinset.card = 2 * n - 4 + (n + 1) / 2 := by
  have hcard : Fintype.card (Tree n) = n := Fintype.card_fin n
  refine ⟨fun X _ _ _ hX hk => general n hn hX hk, Tree n, inferInstance, inferInstance,
    inferInstance, hcard, tree_center_card n hn, ?_⟩
  exact le_antisymm (tree_edges_le n hn)
    (general (X := Tree n) n hn hcard (tree_center_card n hn)).1

end

end D5.S3.Combinatorics.Geometry.UltrametricThreeCentralMinimum
