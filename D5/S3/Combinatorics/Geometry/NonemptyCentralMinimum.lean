/- GID: D5/S3/Combinatorics/Geometry/NonemptyCentralMinimum
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/NonemptyCentralMinimum
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Nonempty central graphs on n points have at least ⌈n/2⌉ edges; equality graphs. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#324)
escape_witness: equality_shape (a nonempty central graph with ⌈n/2⌉ edges is bicentral, and the
  handshake sum with every degree at least one forces all degrees one, or one degree two for odd
  n), with nonempty_facts (one central edge gives every point a central neighbour and a second
  central value).
proof_shape:
  EqualityDegrees, adjLab: definitions; consumers: nonempty_minimum, realize.
  nonempty_facts: content; consumers: equality_shape, nonempty_minimum.
  equality_shape: content; consumer: nonempty_minimum.
  plab_adjLab: bind-only helper; consumer: realize.
  realize: bind-only helper (band_adj at the adjacency labelling, with the degree hypothesis
    giving the cover); consumer: nonempty_minimum.
  nonempty_minimum: content via equality_shape; its attainment and zero-minimum parts read
    all_center_sizes at k = 2 and k = 1.
Direct frozen dependencies: D5/S3/Combinatorics/Geometry/CentralEdgeCover (edge_cover_bound),
  D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges (center, centralGraph),
  D5/S3/Combinatorics/Geometry/CompleteCentralParity (Band, plab, band_adj) and
  D5/S3/Combinatorics/Geometry/CentralSizeEdgeMinima (Feasible, all_center_sizes), the last two
  frozen by the-omega-institute/trureturing#31926.
Search record (§3.1): Mathlib's SimpleGraph.sum_degrees_eq_twice_card_edges,
  degree_pos_iff_exists_adj and Fin.exists_ne_and_ne_of_two_lt are reused; no frozen module
  classifies the equality graphs of the central-edge bound.
-/

import D5.S3.Combinatorics.Geometry.CentralSizeEdgeMinima

/-! # Minimum nonempty central graphs and their equality graphs

For `n ≥ 2` a nonempty central graph on `n` points has at least `⌈n / 2⌉` edges. At equality the
space is bicentral and every point has degree one, except for one point of degree two when `n`
is odd; that is, the graph is `(n/2) P₂` or `P₃ ∪ ((n-3)/2) P₂`. Conversely every graph on
`Fin n` with these degrees is a central graph. Without the nonemptiness condition the minimum is
zero for `n ≥ 3`.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Geometry.NonemptyCentralMinimum

open D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges
open D5.S3.Combinatorics.Geometry.CentralEdgeCover
open D5.S3.Combinatorics.Geometry.CompleteCentralParity
open D5.S3.Combinatorics.Geometry.CentralSizeEdgeMinima

noncomputable section

/-- The degree pattern of the equality graphs on `n` points: all degrees one for even `n`, and
one point of degree two with all other degrees one for odd `n`. -/
def EqualityDegrees {V : Type} [Fintype V] (n : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] :
    Prop :=
  (Even n ∧ ∀ x, G.degree x = 1) ∨ (Odd n ∧ ∃ w, G.degree w = 2 ∧ ∀ x, x ≠ w → G.degree x = 1)

open Classical in
/-- In a space with a central edge, every point has a central neighbour and there are at least
two central values. -/
private lemma nonempty_facts (X : Type) [Fintype X] [MetricSpace X]
    (h : 0 < (centralGraph X).edgeFinset.card) :
    (∀ x, 1 ≤ (centralGraph X).degree x) ∧ 2 ≤ Nat.card (center X) := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp h
  induction e using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    have hab : a ≠ b := he.ne
    have ht : dist a b ∈ center X := by
      simp only [centralGraph, SimpleGraph.fromRel_adj] at he
      rcases he.2 with h' | h'
      · exact h'
      · rwa [dist_comm] at h'
    have hpos : 0 < dist a b := dist_pos.mpr hab
    refine ⟨fun x => ?_, ?_⟩
    · obtain ⟨y, hy⟩ := ht.2 x
      have hyx : y ≠ x := by rintro rfl; rw [dist_self] at hy; linarith
      apply ((centralGraph X).degree_pos_iff_exists_adj x).mpr
      refine ⟨y, ?_⟩
      simp only [centralGraph, SimpleGraph.fromRel_adj]
      exact ⟨Ne.symm hyx, Or.inr (hy ▸ ht)⟩
    · have hfin : (center X).Finite :=
        (Set.finite_range fun y => dist y a).subset (fun t ht => ht.2 a)
      have h0 : (0 : ℝ) ∈ center X := ⟨le_rfl, fun x => ⟨x, dist_self x⟩⟩
      rw [Nat.card_coe_set_eq, ← Set.ncard_pair hpos.ne]
      exact Set.ncard_le_ncard (Set.insert_subset h0 (Set.singleton_subset_iff.mpr ht)) hfin

open Classical in
/-- At the minimum `⌈n / 2⌉`, a nonempty central graph is bicentral with the equality degrees. -/
private lemma equality_shape (X : Type) [Fintype X] [MetricSpace X]
    (h : 0 < (centralGraph X).edgeFinset.card)
    (heq : (centralGraph X).edgeFinset.card = (Fintype.card X + 1) / 2) :
    Nat.card (center X) = 2 ∧ EqualityDegrees (Fintype.card X) (centralGraph X) := by
  obtain ⟨hdeg, hk⟩ := nonempty_facts X h
  have hb := edge_cover_bound X
  rw [heq] at hb
  have hhalf : 0 < (Fintype.card X + 1) / 2 := heq ▸ h
  have hk2 : Nat.card (center X) = 2 := by
    have : (Nat.card (center X) - 1) * ((Fintype.card X + 1) / 2) ≤
        1 * ((Fintype.card X + 1) / 2) := by rwa [one_mul]
    have := Nat.le_of_mul_le_mul_right this hhalf
    omega
  refine ⟨hk2, ?_⟩
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges (centralGraph X)
  rw [heq] at hsum
  set G := centralGraph X
  rcases Nat.even_or_odd (Fintype.card X) with he | ho
  · left
    refine ⟨he, ?_⟩
    have h2 : 2 * ((Fintype.card X + 1) / 2) = ∑ _x : X, 1 := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
      obtain ⟨j, hj⟩ := he
      omega
    rw [h2] at hsum
    have := (Finset.sum_eq_sum_iff_of_le (fun x _ => hdeg x)).mp hsum.symm
    exact fun x => (this x (Finset.mem_univ x)).symm
  · right
    refine ⟨ho, ?_⟩
    have hn1 : 2 * ((Fintype.card X + 1) / 2) = Fintype.card X + 1 := by
      obtain ⟨j, hj⟩ := ho
      omega
    rw [hn1] at hsum
    obtain ⟨w, hw⟩ : ∃ w, 2 ≤ G.degree w := by
      by_contra hcon
      push Not at hcon
      have : ∑ x, G.degree x ≤ ∑ _x : X, 1 :=
        Finset.sum_le_sum fun x _ => by have := hcon x; omega
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at this
      omega
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ w)] at hsum
    have hlow := Finset.card_nsmul_le_sum (Finset.univ.erase w) (fun x => G.degree x) 1
      (fun x _ => hdeg x)
    rw [Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ, smul_eq_mul,
      mul_one] at hlow
    have hw2 : G.degree w = 2 := by omega
    refine ⟨w, hw2, fun x hx => ?_⟩
    have hrest' : ∑ x ∈ Finset.univ.erase w, G.degree x = ∑ _x ∈ Finset.univ.erase w, 1 := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ w),
        Finset.card_univ, smul_eq_mul, mul_one]
      omega
    exact ((Finset.sum_eq_sum_iff_of_le (fun x _ => hdeg x)).mp hrest'.symm x
      (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩)).symm

/-- The label of a graph on `Fin n`: `0` on edges and `1` elsewhere. -/
private def adjLab (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i j : ℕ) : ℕ :=
  if h : i < n ∧ j < n then (if G.Adj ⟨i, h.1⟩ ⟨j, h.2⟩ then 0 else 1) else 1

private lemma plab_adjLab (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x y : Fin n) :
    plab n (adjLab n G) x y = if G.Adj x y then 0 else 1 := by
  unfold plab adjLab
  rw [dite_eq_left_of_eq_true (eq_true ⟨lt_of_le_of_lt (min_le_left _ _) x.2, max_lt x.2 y.2⟩)]
  rcases le_total x.1 y.1 with h | h
  · simp only [min_eq_left h, max_eq_right h, Fin.eta]
  · simp only [min_eq_right h, max_eq_left h, Fin.eta, G.adj_comm]

/-- Every graph on `Fin n`, `n ≥ 2`, with the equality degrees is the central graph of the band
whose central pairs are its edges. -/
private lemma realize (n : ℕ) (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : EqualityDegrees n G) (x y : Fin n) :
    (centralGraph (Band n 1 (adjLab n G))).Adj x y ↔ G.Adj x y := by
  have hdeg : ∀ x, 1 ≤ G.degree x := by
    rcases hG with ⟨_, h⟩ | ⟨_, w, hw, h⟩
    · exact fun x => (h x).ge
    · intro x
      by_cases hx : x = w
      · rw [hx, hw]; omega
      · rw [h x hx]
  have hcov : ∀ x : Fin n, ∀ r < 1, ∃ y : Fin n, y ≠ x ∧ plab n (adjLab n G) x y = r := by
    intro x r hr
    obtain ⟨y, hy⟩ := (G.degree_pos_iff_exists_adj x).mp (hdeg x)
    refine ⟨y, hy.ne.symm, ?_⟩
    rw [plab_adjLab]
    simp only [hy, ↓reduceIte]
    omega
  have h3 : ∀ x y : Fin n, x ≠ y → 1 ≤ plab n (adjLab n G) x y →
      ∃ z : Fin n, z ≠ x ∧ z ≠ y := by
    intro x y hxy hl
    by_cases h3n : 2 < n
    · exact Fin.exists_ne_and_ne_of_two_lt x y h3n
    · exfalso
      obtain ⟨z, hz⟩ := (G.degree_pos_iff_exists_adj x).mp (hdeg x)
      have hzy : z = y := by
        have := hz.ne
        apply Fin.ext
        have h1 : x.1 ≠ z.1 := fun e => this (Fin.ext e)
        have h2 : x.1 ≠ y.1 := fun e => hxy (Fin.ext e)
        have := z.2; have := y.2
        omega
      rw [plab_adjLab] at hl
      simp only [hzy ▸ hz, ↓reduceIte] at hl
      omega
  have hiff : ∀ x y : Fin n, (x ≠ y ∧ plab n (adjLab n G) x y < 1) ↔ G.Adj x y := by
    intro x y
    rw [plab_adjLab]
    constructor
    · rintro ⟨_, h⟩
      by_contra hna
      simp only [hna, ↓reduceIte] at h
      omega
    · intro h
      exact ⟨h.ne, by simp only [h, ↓reduceIte]; omega⟩
  exact (band_adj n 1 _ (by omega) hcov h3 x y).trans (hiff x y)

open Classical in
/-- For `n ≥ 2`, the least edge count of a nonempty central graph on `n` points is `⌈n / 2⌉`.
A nonempty central graph attaining it is bicentral and has the equality degrees (it is
`(n/2) P₂` for even `n` and `P₃ ∪ ((n-3)/2) P₂` for odd `n`), and every graph on `Fin n` with
the equality degrees is a central graph. For `n ≥ 3` the least edge count of all central graphs
on `n` points is zero. -/
theorem nonempty_minimum (n : ℕ) (hn : 2 ≤ n) :
    IsLeast {e : ℕ | ∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X), Fintype.card X = n ∧
        0 < (centralGraph X).edgeFinset.card ∧ (centralGraph X).edgeFinset.card = e}
      ((n + 1) / 2) ∧
    (∀ (X : Type) [Fintype X] [MetricSpace X], Fintype.card X = n →
      0 < (centralGraph X).edgeFinset.card →
      (centralGraph X).edgeFinset.card = (n + 1) / 2 →
      Nat.card (center X) = 2 ∧ EqualityDegrees n (centralGraph X)) ∧
    (∀ G : SimpleGraph (Fin n), EqualityDegrees n G →
      ∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X) (e : X ≃ Fin n),
        ∀ x y, (centralGraph X).Adj x y ↔ G.Adj (e x) (e y)) ∧
    (3 ≤ n → IsLeast {e : ℕ | ∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X),
        Fintype.card X = n ∧ (centralGraph X).edgeFinset.card = e} 0) := by
  have hf2 : Feasible n 2 := by
    unfold Feasible
    split_ifs <;> omega
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨X, hF, hM, hX, -, hE⟩ := ((all_center_sizes n 2 (by omega)).2 hf2).1
    refine ⟨X, hF, hM, hX, ?_, ?_⟩
    · rw [hE]; omega
    · rw [hE]; norm_num
  · rintro e ⟨X, _, _, rfl, hpos, rfl⟩
    have hk := (nonempty_facts X hpos).2
    have hb := edge_cover_bound X
    calc (Fintype.card X + 1) / 2 ≤ (Nat.card (center X) - 1) * ((Fintype.card X + 1) / 2) :=
          Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ _ := hb
  · intro X _ _ hX hpos heq
    subst hX
    exact equality_shape X hpos heq
  · intro G hG
    exact ⟨Band n 1 (adjLab n G), inferInstance, inferInstance, Equiv.refl _,
      realize n hn G hG⟩
  · intro h3
    have hf1 : Feasible n 1 := by
      unfold Feasible
      split_ifs <;> omega
    refine ⟨?_, fun e _ => Nat.zero_le e⟩
    obtain ⟨X, hF, hM, hX, -, hE⟩ := ((all_center_sizes n 1 (by omega)).2 hf1).1
    exact ⟨X, hF, hM, hX, by rw [hE]; simp⟩

end

end D5.S3.Combinatorics.Geometry.NonemptyCentralMinimum
