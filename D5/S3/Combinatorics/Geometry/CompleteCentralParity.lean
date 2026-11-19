/- GID: D5/S3/Combinatorics/Geometry/CompleteCentralParity
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/CompleteCentralParity
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: An n-point metric space with complete n-central graph exists iff n = 1 or n is even. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#321; delivered with
  MinimumCentralOrder for #322 and CentralSizeEdgeMinima for #323, all first frozen together)
escape_witness: band_center_iff and band_center_card (a labelled narrow-band space whose labels
  below c meet every point has exactly the c+1 central values 0 and 1 + r/(2(n+c))), with
  cls_cover (every round-robin class is a perfect matching of Fin (2m+2)).
proof_shape:
  cls, plab, code, bd, Band, Space: definitions; consumers: the lemmas below, MinimumCentralOrder
    and CentralSizeEdgeMinima.
  cls_cover, band_center_iff, band_center_card, band_adj: content; consumers:
    complete_central_iff, MinimumCentralOrder.minimum_order,
    CentralSizeEdgeMinima.all_center_sizes.
  band_edges: bind-only helper (band_adj with Finset.card_image_le); consumer:
    CentralSizeEdgeMinima.all_center_sizes.
  cls_comm, cls_lt, plab_comm, code_comm, code_lt, code_inj, lo_bounds, hi_bounds, bd_lo, bd_hi,
    bd_bounds, bd_comm, bd_self, bd_triangle, bd_eq_zero, band_card, third_point, space_cov,
    space_h3, center_card, complete: bind-only helpers; consumers: the metric instance, the band
    lemmas, complete_central_iff, minimum_order and all_center_sizes.
  complete_central_iff: content via the band construction; the odd case is a bind-only
    combination of edge_cover_bound and SimpleGraph.card_edgeFinset_le_card_choose_two.
Direct frozen dependencies: D5/S3/Combinatorics/Geometry/CentralEdgeCover (edge_cover_bound;
  frozen by the parent PR for #318), D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges
  (center, centralGraph).
Search record (§3.1): the frozen private GlobalZZGateTimeBound.cyclicColor (with
  cyclicColor_proper) colours Option (ZMod q) by injectivity at each vertex, inside a Quantum
  module; OddPrimePerfectOneFactorization needs a prime modulus. Neither states the covering
  property on Fin (2m+2) used here, so cls_cover is proved directly. No frozen module builds a
  metric space with a prescribed set of central values; the band is the single construction
  shared by the three deliveries.
-/

import D5.S3.Combinatorics.Geometry.CentralEdgeCover

/-! # Parity of complete `n`-central metric graphs

For `n ≥ 1`, some metric space on `n` points has exactly `n` central distances and a complete
central graph if and only if `n = 1` or `n` is even. For odd `n ≥ 3` the edge-cover bound would
need more than `n (n - 1) / 2` edges; for even `n` a round-robin one-factorization of the
complete graph, with one distance per perfect matching, realizes it.

The construction is the labelled narrow-band space `Band n c lab`, which also serves the
minimum orders (`MinimumCentralOrder`) and the feasible center sizes (`CentralSizeEdgeMinima`).
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Geometry.CompleteCentralParity

open D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges
open D5.S3.Combinatorics.Geometry.CentralEdgeCover

noncomputable section

variable (m : ℕ)

/-- The round-robin class of a pair of distinct points of `Fin (2m+2)`: with `M = 2m+1` and the
point `M` playing the role of `∞`, the pair `{i, j}` gets `(i + j) mod M` and `{i, ∞}` gets
`2i mod M`. -/
def cls (i j : ℕ) : ℕ :=
  if i = 2 * m + 1 then (2 * j) % (2 * m + 1)
  else if j = 2 * m + 1 then (2 * i) % (2 * m + 1)
  else (i + j) % (2 * m + 1)

lemma cls_comm (i j : ℕ) : cls m i j = cls m j i := by
  unfold cls
  split_ifs <;> first | rfl | (subst_vars; rfl) | (rw [add_comm])

lemma cls_lt (i j : ℕ) : cls m i j < 2 * m + 1 := by
  unfold cls
  split_ifs <;> exact Nat.mod_lt _ (by omega)

/-- Each class is a perfect matching: every point has a partner in every class. -/
lemma cls_cover (x : Fin (2 * m + 2)) (r : ℕ) (hr : r < 2 * m + 1) :
    ∃ y : Fin (2 * m + 2), y ≠ x ∧ cls m x.1 y.1 = r := by
  obtain ⟨i, hi⟩ := x
  by_cases hinf : i = 2 * m + 1
  · subst hinf
    have hlt : (r * (m + 1)) % (2 * m + 1) < 2 * m + 1 := Nat.mod_lt _ (by omega)
    refine ⟨⟨(r * (m + 1)) % (2 * m + 1), by omega⟩, ?_, ?_⟩
    · intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    · unfold cls
      simp only [↓reduceIte]
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      rw [show 2 * (r * (m + 1)) = r + r * (2 * m + 1) by ring, Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt hr
  · by_cases h2 : (2 * i) % (2 * m + 1) = r
    · refine ⟨⟨2 * m + 1, by omega⟩, ?_, ?_⟩
      · simp only [ne_eq, Fin.mk.injEq]; omega
      · unfold cls; simp only [hinf, ↓reduceIte]; exact h2
    · have hy : (r + (2 * m + 1) - i) % (2 * m + 1) < 2 * m + 1 := Nat.mod_lt _ (by omega)
      refine ⟨⟨(r + (2 * m + 1) - i) % (2 * m + 1), by omega⟩, ?_, ?_⟩
      · intro h
        have h' := congrArg Fin.val h
        simp only at h'
        apply h2
        calc (2 * i) % (2 * m + 1) = (i + (r + (2 * m + 1) - i) % (2 * m + 1)) % (2 * m + 1) := by
              rw [h', two_mul]
          _ = r := by
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
                show i + (r + (2 * m + 1) - i) = r + (2 * m + 1) by omega, Nat.add_mod_right]
              exact Nat.mod_eq_of_lt hr
      · unfold cls
        simp only [hinf, show (r + (2 * m + 1) - i) % (2 * m + 1) ≠ 2 * m + 1 by omega,
          ↓reduceIte]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
          show i + (r + (2 * m + 1) - i) = r + (2 * m + 1) by omega, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt hr

/-! ### Labelled narrow-band spaces

A label function `lab` assigns a natural number to each pair `i < j` of points of `Fin n`.
Pairs with label `r < c` are put at distance `1 + r / (2 (n + c))`; every other pair gets its
own distance `3/2 + code / (2 n²)`, where `code = i n + j` determines the pair. All distances
of distinct points lie in `[1, 2)`, so the triangle inequality holds. -/

section Band

variable (n c : ℕ) (lab : ℕ → ℕ → ℕ)

/-- The label of an unordered pair of points. -/
def plab (x y : Fin n) : ℕ := lab (min x.1 y.1) (max x.1 y.1)

lemma plab_comm (x y : Fin n) : plab n lab x y = plab n lab y x := by
  unfold plab; rw [min_comm, max_comm]

/-- A code of an unordered pair of points that determines the pair. -/
private def code (x y : Fin n) : ℕ := min x.1 y.1 * n + max x.1 y.1

private lemma code_comm (x y : Fin n) : code n x y = code n y x := by
  unfold code; rw [min_comm, max_comm]

private lemma code_lt (x y : Fin n) : code n x y < n ^ 2 := by
  unfold code
  have h1 : min x.1 y.1 + 1 ≤ n := lt_of_le_of_lt (min_le_left _ _) x.2
  have h2 : max x.1 y.1 < n := max_lt x.2 y.2
  have : (min x.1 y.1 + 1) * n ≤ n * n := Nat.mul_le_mul_right n h1
  nlinarith

private lemma code_inj {x y w z : Fin n} (h : code n w z = code n x y) :
    z.1 = x.1 ∨ z.1 = y.1 := by
  unfold code at h
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) x.2
  have key : ∀ a b : ℕ, b < n → (a * n + b) / n = a ∧ (a * n + b) % n = b := fun a b hb =>
    ⟨by rw [add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, zero_add],
      by rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]⟩
  obtain ⟨h1, h2⟩ := key (min w.1 z.1) (max w.1 z.1) (max_lt w.2 z.2)
  obtain ⟨h3, h4⟩ := key (min x.1 y.1) (max x.1 y.1) (max_lt x.2 y.2)
  rw [h] at h1 h2
  omega

/-- The labelled narrow-band distance. -/
private def bd (x y : Fin n) : ℝ :=
  if x = y then 0
  else if plab n lab x y < c then 1 + (plab n lab x y : ℝ) / (2 * (n + c))
  else 3 / 2 + (code n x y : ℝ) / (2 * n ^ 2)

private lemma lo_bounds (r : ℕ) (hr : r < c) :
    0 ≤ (r : ℝ) / (2 * (n + c)) ∧ (r : ℝ) / (2 * (n + c)) < 1 / 2 := by
  have hpos : (0 : ℝ) < 2 * (n + c) := by
    have : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
    positivity
  refine ⟨by positivity, ?_⟩
  rw [div_lt_iff₀ hpos]
  have : (r : ℝ) < c := by exact_mod_cast hr
  have : (0 : ℝ) ≤ n := by positivity
  linarith

private lemma hi_bounds (x y : Fin n) :
    0 ≤ (code n x y : ℝ) / (2 * n ^ 2) ∧ (code n x y : ℝ) / (2 * n ^ 2) < 1 / 2 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) x.2)
  have hpos : (0 : ℝ) < 2 * n ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_lt_iff₀ hpos]
  have : (code n x y : ℝ) < n ^ 2 := by exact_mod_cast code_lt n x y
  linarith

private lemma bd_lo {x y : Fin n} (h : x ≠ y) (hl : plab n lab x y < c) :
    bd n c lab x y = 1 + (plab n lab x y : ℝ) / (2 * (n + c)) := by
  unfold bd; simp only [h, hl, ↓reduceIte]

private lemma bd_hi {x y : Fin n} (h : x ≠ y) (hl : ¬ plab n lab x y < c) :
    bd n c lab x y = 3 / 2 + (code n x y : ℝ) / (2 * n ^ 2) := by
  unfold bd; simp only [h, hl, ↓reduceIte]

private lemma bd_bounds {x y : Fin n} (h : x ≠ y) : 1 ≤ bd n c lab x y ∧ bd n c lab x y < 2 := by
  by_cases hl : plab n lab x y < c
  · rw [bd_lo n c lab h hl]
    have := lo_bounds n c _ hl
    constructor <;> linarith
  · rw [bd_hi n c lab h hl]
    have := hi_bounds n x y
    constructor <;> linarith

private lemma bd_comm (x y : Fin n) : bd n c lab x y = bd n c lab y x := by
  unfold bd
  rw [plab_comm n lab x y, code_comm n x y]
  by_cases h : x = y
  · subst h; rfl
  · simp only [h, Ne.symm h, ↓reduceIte]

/-- The points of `Fin n` with the labelled narrow-band metric. -/
@[nolint unusedArguments]
def Band (n _c : ℕ) (_lab : ℕ → ℕ → ℕ) : Type := Fin n

instance : Fintype (Band n c lab) := inferInstanceAs (Fintype (Fin n))

lemma band_card : Fintype.card (Band n c lab) = n := Fintype.card_fin n

private lemma bd_self (x : Fin n) : bd n c lab x x = 0 := by
  unfold bd; simp only [↓reduceIte]

private lemma bd_triangle (x y z : Fin n) : bd n c lab x z ≤ bd n c lab x y + bd n c lab y z := by
  by_cases hxz : x = z
  · subst hxz
    rw [bd_self]
    by_cases hxy : x = y
    · subst hxy; rw [bd_self]; norm_num
    · have := (bd_bounds n c lab hxy).1; have := (bd_bounds n c lab (Ne.symm hxy)).1; linarith
  · have h1 := (bd_bounds n c lab hxz).2
    by_cases hxy : x = y
    · subst hxy; rw [bd_self, zero_add]
    · by_cases hyz : y = z
      · subst hyz; rw [bd_self, add_zero]
      · have := (bd_bounds n c lab hxy).1; have := (bd_bounds n c lab hyz).1; linarith

private lemma bd_eq_zero {x y : Fin n} (h : bd n c lab x y = 0) : x = y := by
  by_contra hne
  have := (bd_bounds n c lab hne).1
  linarith

noncomputable instance : MetricSpace (Band n c lab) where
  dist x y := bd n c lab x y
  dist_self x := bd_self n c lab x
  dist_comm x y := bd_comm n c lab x y
  dist_triangle x y z := bd_triangle n c lab x y z
  eq_of_dist_eq_zero h := bd_eq_zero n c lab h

/-- Every label below `c` occurs at every point, and a pair whose label is not below `c` leaves
a third point. Then the central values are `0` and `1 + r / (2 (n + c))` for `r < c`. -/
lemma band_center_iff (hn : 0 < n)
    (hcov : ∀ x : Fin n, ∀ r < c, ∃ y : Fin n, y ≠ x ∧ plab n lab x y = r)
    (h3 : ∀ x y : Fin n, x ≠ y → c ≤ plab n lab x y → ∃ z : Fin n, z ≠ x ∧ z ≠ y) (t : ℝ) :
    t ∈ center (Band n c lab) ↔ t = 0 ∨ ∃ r < c, t = 1 + (r : ℝ) / (2 * (n + c)) := by
  constructor
  · rintro ⟨_, ht⟩
    by_cases ht0 : t = 0
    · exact Or.inl ht0
    right
    obtain ⟨y, hy⟩ := ht (⟨0, hn⟩ : Fin n)
    change bd n c lab y ⟨0, hn⟩ = t at hy
    have hyp : (y : Fin n) ≠ ⟨0, hn⟩ := by
      intro e; apply ht0; rw [← hy, e, bd_self]
    by_cases hl : plab n lab y ⟨0, hn⟩ < c
    · exact ⟨_, hl, by rw [← hy, bd_lo n c lab hyp hl]⟩
    · exfalso
      rw [bd_hi n c lab hyp hl] at hy
      obtain ⟨z, hzy, hzp⟩ := h3 y ⟨0, hn⟩ hyp (not_lt.mp hl)
      obtain ⟨w, hw⟩ := ht z
      change bd n c lab w z = t at hw
      have hwz : (w : Fin n) ≠ z := by
        intro e; apply ht0; rw [← hw, e, bd_self]
      by_cases hl' : plab n lab w z < c
      · rw [bd_lo n c lab hwz hl'] at hw
        have := (lo_bounds n c _ hl').2
        have := (hi_bounds n y ⟨0, hn⟩).1
        linarith
      · rw [bd_hi n c lab hwz hl', ← hy] at hw
        have hpos : (0 : ℝ) < 2 * n ^ 2 := by
          have : (0 : ℝ) < n := by exact_mod_cast hn
          positivity
        have hc : (code n w z : ℝ) = code n y ⟨0, hn⟩ := by
          have h' := add_left_cancel hw
          rwa [div_left_inj' hpos.ne'] at h'
        rcases code_inj n (by exact_mod_cast hc) with h | h
        · exact hzy (Fin.ext h)
        · exact hzp (Fin.ext h)
  · rintro (rfl | ⟨r, hr, rfl⟩)
    · exact ⟨le_rfl, fun p => ⟨p, dist_self p⟩⟩
    · refine ⟨by linarith [(lo_bounds n c r hr).1], fun p => ?_⟩
      obtain ⟨y, hne, hy⟩ := hcov p r hr
      refine ⟨(y : Band n c lab), ?_⟩
      change bd n c lab y p = _
      have hy' : plab n lab y p = r := (plab_comm n lab y p).trans hy
      exact (bd_lo n c lab hne (hy' ▸ hr)).trans (by rw [hy'])

/-- Under the hypotheses of `band_center_iff`, the space has exactly `c + 1` central values. -/
lemma band_center_card (hn : 0 < n)
    (hcov : ∀ x : Fin n, ∀ r < c, ∃ y : Fin n, y ≠ x ∧ plab n lab x y = r)
    (h3 : ∀ x y : Fin n, x ≠ y → c ≤ plab n lab x y → ∃ z : Fin n, z ≠ x ∧ z ≠ y) :
    Nat.card (center (Band n c lab)) = c + 1 := by
  let g : ℕ → ℝ := fun r => 1 + (r : ℝ) / (2 * (n + c))
  have hinj : Set.InjOn g (Finset.range c : Set ℕ) := by
    intro a ha b _ h
    have hc : (0 : ℝ) < c := by
      have : a < c := by simpa using ha
      exact_mod_cast (show 0 < c by omega)
    have hpos : (0 : ℝ) < 2 * (n + c) := by positivity
    have : (a : ℝ) = b := by
      simp only [g, add_right_inj] at h
      field_simp at h
      exact h
    exact_mod_cast this
  have h0 : (0 : ℝ) ∉ (Finset.range c).image g := by
    intro h
    obtain ⟨r, hr, hr0⟩ := Finset.mem_image.mp h
    have := (lo_bounds n c r (by simpa using hr)).1
    simp only [g] at hr0
    linarith
  have hC : center (Band n c lab) = ↑(insert 0 ((Finset.range c).image g)) := by
    ext t
    rw [band_center_iff n c lab hn hcov h3]
    simp only [Finset.coe_insert, Finset.coe_image, Finset.coe_range, Set.mem_insert_iff,
      Set.mem_image, Set.mem_Iio, g]
    constructor
    · rintro (h | ⟨r, hr, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨r, hr, h.symm⟩
    · rintro (h | ⟨r, hr, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨r, hr, h.symm⟩
  rw [hC, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_insert_of_notMem h0,
    Finset.card_image_of_injOn hinj, Finset.card_range]

/-- Under the hypotheses of `band_center_iff`, distinct points are central neighbours exactly
when their label is below `c`. -/
lemma band_adj (hn : 0 < n)
    (hcov : ∀ x : Fin n, ∀ r < c, ∃ y : Fin n, y ≠ x ∧ plab n lab x y = r)
    (h3 : ∀ x y : Fin n, x ≠ y → c ≤ plab n lab x y → ∃ z : Fin n, z ≠ x ∧ z ≠ y)
    (x y : Band n c lab) :
    (centralGraph (Band n c lab)).Adj x y ↔ x ≠ y ∧ plab n lab x y < c := by
  have key : ∀ x y : Fin n, x ≠ y →
      (bd n c lab x y ∈ center (Band n c lab) ↔ plab n lab x y < c) := by
    intro x y hxy
    rw [band_center_iff n c lab hn hcov h3]
    constructor
    · rintro (h | ⟨r, hr, h⟩)
      · have := (bd_bounds n c lab hxy).1; linarith
      · by_contra hl
        rw [bd_hi n c lab hxy hl] at h
        have := (lo_bounds n c r hr).2
        have := (hi_bounds n x y).1
        linarith
    · intro hl
      exact Or.inr ⟨_, hl, bd_lo n c lab hxy hl⟩
  simp only [centralGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hxy, h | h⟩
    · exact ⟨hxy, (key x y hxy).mp h⟩
    · exact ⟨hxy, lt_of_eq_of_lt (plab_comm n lab x y) ((key y x (Ne.symm hxy)).mp h)⟩
  · rintro ⟨hxy, hl⟩
    exact ⟨hxy, Or.inl ((key x y hxy).mpr hl)⟩

open Classical in
/-- If every central pair is hit by a map from `c` classes times `q` slots, the central graph
has at most `c q` edges. -/
lemma band_edges (hn : 0 < n)
    (hcov : ∀ x : Fin n, ∀ r < c, ∃ y : Fin n, y ≠ x ∧ plab n lab x y = r)
    (h3 : ∀ x y : Fin n, x ≠ y → c ≤ plab n lab x y → ∃ z : Fin n, z ≠ x ∧ z ≠ y)
    (q : ℕ) (G : ℕ → ℕ → Sym2 ℕ)
    (hG : ∀ x y : Fin n, x ≠ y → plab n lab x y < c → ∃ r < c, ∃ t < q, G r t = s(x.1, y.1)) :
    (centralGraph (Band n c lab)).edgeFinset.card ≤ c * q := by
  have hinj : Function.Injective (Sym2.map (fun x : Band n c lab => (x : Fin n).1)) :=
    Sym2.map.injective Fin.val_injective
  rw [← Finset.card_image_of_injective _ hinj]
  have hsub : (centralGraph (Band n c lab)).edgeFinset.image
      (Sym2.map (fun x : Band n c lab => (x : Fin n).1)) ⊆
      (Finset.range c ×ˢ Finset.range q).image (fun p => G p.1 p.2) := by
    intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    induction e' using Sym2.ind with
    | h x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        band_adj n c lab hn hcov h3] at he'
      obtain ⟨r, hr, t, ht, hG'⟩ := hG x y he'.1 he'.2
      rw [Sym2.map_mk]
      exact Finset.mem_image.mpr ⟨(r, t), by simp [hr, ht], hG'⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.range c ×ˢ Finset.range q).card := Finset.card_image_le
    _ = c * q := by rw [Finset.card_product, Finset.card_range, Finset.card_range]

/-- Any three points leave room for a point off a given pair. -/
lemma third_point (h : 3 ≤ n) (x y : Fin n) : ∃ z : Fin n, z ≠ x ∧ z ≠ y := by
  by_cases h0 : (0 : ℕ) ≠ x.1 ∧ (0 : ℕ) ≠ y.1
  · exact ⟨⟨0, by omega⟩, fun e => h0.1 (congrArg Fin.val e), fun e => h0.2 (congrArg Fin.val e)⟩
  by_cases h1 : (1 : ℕ) ≠ x.1 ∧ (1 : ℕ) ≠ y.1
  · exact ⟨⟨1, by omega⟩, fun e => h1.1 (congrArg Fin.val e), fun e => h1.2 (congrArg Fin.val e)⟩
  refine ⟨⟨2, by omega⟩, fun e => ?_, fun e => ?_⟩ <;>
    · have := congrArg Fin.val e; simp only at this; omega

end Band

/-- The round-robin space: every pair of distinct points of `Fin (2m+2)` is central, at a
distance determined by its round-robin class. -/
abbrev Space : Type := Band (2 * m + 2) (2 * m + 1) (cls m)

/-- Every round-robin class meets every point. -/
lemma space_cov (x : Fin (2 * m + 2)) (r : ℕ) (hr : r < 2 * m + 1) :
    ∃ y : Fin (2 * m + 2), y ≠ x ∧ plab (2 * m + 2) (cls m) x y = r := by
  obtain ⟨y, hne, hy⟩ := cls_cover m x r hr
  refine ⟨y, hne, ?_⟩
  unfold plab
  rcases le_total x.1 y.1 with h | h
  · rw [min_eq_left h, max_eq_right h, hy]
  · rw [min_eq_right h, max_eq_left h, cls_comm, hy]

private lemma space_h3 (x y : Fin (2 * m + 2)) (_ : x ≠ y)
    (h : 2 * m + 1 ≤ plab (2 * m + 2) (cls m) x y) : ∃ z : Fin (2 * m + 2), z ≠ x ∧ z ≠ y :=
  absurd (cls_lt m _ _) (not_lt.mpr h)

private lemma center_card : Nat.card (center (Space m)) = 2 * m + 2 :=
  band_center_card _ _ _ (by omega) (space_cov m) (space_h3 m)

private lemma complete : centralGraph (Space m) = ⊤ := by
  ext x y
  rw [band_adj _ _ _ (by omega) (space_cov m) (space_h3 m)]
  simp only [SimpleGraph.top_adj]
  exact ⟨fun h => h.1, fun h => ⟨h, cls_lt m _ _⟩⟩

/-- For `n ≥ 1`, a metric space on `n` points with exactly `n` central distances and a complete
central graph exists if and only if `n = 1` or `n` is even. -/
theorem complete_central_iff (n : ℕ) (hn : 1 ≤ n) :
    (∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X), Fintype.card X = n ∧
      Nat.card (center X) = n ∧ centralGraph X = ⊤) ↔ n = 1 ∨ Even n := by
  classical
  constructor
  · rintro ⟨X, _, _, hX, hk, htop⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hn1, hodd⟩ := hcon
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := by
      rcases Nat.even_or_odd n with h | ⟨k, hk'⟩
      · exact absurd h hodd
      · exact ⟨k, hk'⟩
    have hb := edge_cover_bound X
    rw [hk, hX] at hb
    have hc := SimpleGraph.card_edgeFinset_le_card_choose_two (G := centralGraph X)
    rw [hX, Nat.choose_two_right] at hc
    have hk1 : 1 ≤ k := by omega
    have h1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have h2 : (2 * k + 1) * (2 * k + 1 - 1) / 2 = (2 * k + 1) * k := by
      rw [show 2 * k + 1 - 1 = 2 * k by omega, show (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k)
        by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [h1] at hb
    rw [h2] at hc
    have := hb.trans hc
    rw [show 2 * k + 1 - 1 = 2 * k by omega] at this
    nlinarith
  · rintro (rfl | ⟨m', rfl⟩)
    · refine ⟨Unit, inferInstance, inferInstance, rfl, ?_, ?_⟩
      · have : center Unit = {0} := by
          ext t
          simp only [center, Set.mem_ofPred_eq, Set.mem_singleton_iff]
          constructor
          · rintro ⟨_, ht⟩
            obtain ⟨y, hy⟩ := ht ()
            rw [Subsingleton.elim y (), dist_self] at hy
            exact hy.symm
          · rintro rfl
            exact ⟨le_rfl, fun p => ⟨p, dist_self p⟩⟩
        rw [this, Nat.card_coe_set_eq, Set.ncard_singleton]
      · ext x y
        simp only [SimpleGraph.top_adj, centralGraph, SimpleGraph.fromRel_adj]
        exact ⟨fun h => h.1, fun h => absurd (Subsingleton.elim x y) h⟩
    · obtain ⟨m, rfl⟩ : ∃ m, m' = m + 1 := ⟨m' - 1, by omega⟩
      refine ⟨Space m, inferInstance, inferInstance, ?_, ?_, complete m⟩
      · exact (band_card _ _ _).trans (by ring)
      · rw [center_card]; ring

end

end D5.S3.Combinatorics.Geometry.CompleteCentralParity
