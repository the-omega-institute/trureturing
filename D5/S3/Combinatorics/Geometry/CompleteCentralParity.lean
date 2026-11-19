/- GID: D5/S3/Combinatorics/Geometry/CompleteCentralParity
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/CompleteCentralParity
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: An n-point metric space with complete n-central graph exists iff n = 1 or n is even. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#321)
escape_witness: cls_cover (every point has a partner in every round-robin class), with
  center_iff and center_card (the round-robin space has exactly 2m+2 central values)
proof_shape:
  cls, d, Space: definitions; consumers: the lemmas below.
  cls_cover, center_iff, center_card, complete: content; consumer: complete_central_iff.
  cls_comm, cls_lt, d_self, d_ne, frac_bounds, d_bounds, d_comm: bind-only helpers; consumers:
    the metric instance, center_iff, center_card, complete.
  complete_central_iff: content via the round-robin construction; the odd case is a bind-only
    combination of edge_cover_bound and SimpleGraph.card_edgeFinset_le_card_choose_two.
Direct frozen dependencies: D5/S3/Combinatorics/Geometry/CentralEdgeCover (edge_cover_bound),
  D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges (center, centralGraph).
Search record (§3.1): the frozen private GlobalZZGateTimeBound.cyclicColor (with
  cyclicColor_proper) colours Option (ZMod q) by injectivity at each vertex, inside a Quantum
  module; OddPrimePerfectOneFactorization needs a prime modulus. Neither states the covering
  property on Fin (2m+2) used here, so cls_cover is proved directly.
-/

import D5.S3.Combinatorics.Geometry.CentralEdgeCover

/-! # Parity of complete `n`-central metric graphs

For `n ≥ 1`, some metric space on `n` points has exactly `n` central distances and a complete
central graph if and only if `n = 1` or `n` is even. For odd `n ≥ 3` the edge-cover bound would
need more than `n (n - 1) / 2` edges; for even `n` a round-robin one-factorization of the
complete graph, with one distance per perfect matching, realizes it.
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
private def cls (i j : ℕ) : ℕ :=
  if i = 2 * m + 1 then (2 * j) % (2 * m + 1)
  else if j = 2 * m + 1 then (2 * i) % (2 * m + 1)
  else (i + j) % (2 * m + 1)

private lemma cls_comm (i j : ℕ) : cls m i j = cls m j i := by
  unfold cls
  split_ifs <;> first | rfl | (subst_vars; rfl) | (rw [add_comm])

private lemma cls_lt (i j : ℕ) : cls m i j < 2 * m + 1 := by
  unfold cls
  split_ifs <;> exact Nat.mod_lt _ (by omega)

/-- Each class is a perfect matching: every point has a partner in every class. -/
private lemma cls_cover (x : Fin (2 * m + 2)) (r : ℕ) (hr : r < 2 * m + 1) :
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

/-- Distinct points are at distance `1 + r / (2m+2)`, where `r` is their round-robin class. -/
private def d (x y : Fin (2 * m + 2)) : ℝ :=
  if x = y then 0 else 1 + (cls m x.1 y.1 : ℝ) / (2 * m + 2)

private lemma d_self (x : Fin (2 * m + 2)) : d m x x = 0 := by
  unfold d; simp only [↓reduceIte]

private lemma d_ne {x y : Fin (2 * m + 2)} (h : x ≠ y) :
    d m x y = 1 + (cls m x.1 y.1 : ℝ) / (2 * m + 2) := by
  unfold d; simp only [h, ↓reduceIte]

private lemma frac_bounds (r : ℕ) (hr : r < 2 * m + 1) :
    0 ≤ (r : ℝ) / (2 * m + 2) ∧ (r : ℝ) / (2 * m + 2) < 1 := by
  have hpos : (0 : ℝ) < 2 * m + 2 := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hpos]
  have : (r : ℝ) < 2 * m + 1 := by exact_mod_cast hr
  linarith

private lemma d_bounds {x y : Fin (2 * m + 2)} (h : x ≠ y) : 1 ≤ d m x y ∧ d m x y < 2 := by
  rw [d_ne m h]
  have := frac_bounds m _ (cls_lt m x.1 y.1)
  constructor <;> linarith

private lemma d_comm (x y : Fin (2 * m + 2)) : d m x y = d m y x := by
  by_cases h : x = y
  · subst h; rfl
  · rw [d_ne m h, d_ne m (Ne.symm h), cls_comm]

/-- The points of `Fin (2m+2)` with the round-robin metric. -/
def Space : Type := Fin (2 * m + 2)

instance : Fintype (Space m) := inferInstanceAs (Fintype (Fin (2 * m + 2)))

noncomputable instance : MetricSpace (Space m) where
  dist x y := d m x y
  dist_self x := d_self m x
  dist_comm x y := d_comm m x y
  dist_triangle x y z := by
    show d m x z ≤ d m x y + d m y z
    by_cases hxz : x = z
    · subst hxz
      have h0 : d m x x = 0 := d_self m x
      rw [h0]
      by_cases hxy : x = y
      · subst hxy; rw [h0]; norm_num
      · have := (d_bounds m hxy).1; have := (d_bounds m (Ne.symm hxy)).1; linarith
    · have h1 := (d_bounds m hxz).2
      by_cases hxy : x = y
      · subst hxy; rw [show d m x x = 0 from d_self m x, zero_add]
      · by_cases hyz : y = z
        · subst hyz; rw [show d m y y = 0 from d_self m y, add_zero]
        · have := (d_bounds m hxy).1; have := (d_bounds m hyz).1; linarith
  eq_of_dist_eq_zero {x y} h := by
    by_contra hne
    have := (d_bounds m hne).1
    change d m x y = 0 at h
    linarith

private lemma center_iff (t : ℝ) :
    t ∈ center (Space m) ↔ t = 0 ∨ ∃ r < 2 * m + 1, t = 1 + (r : ℝ) / (2 * m + 2) := by
  constructor
  · rintro ⟨_, ht⟩
    obtain ⟨y, hy⟩ := ht (⟨0, by omega⟩ : Fin (2 * m + 2))
    change d m y ⟨0, by omega⟩ = t at hy
    by_cases h : y = (⟨0, by omega⟩ : Fin (2 * m + 2))
    · left; rw [h, d_self] at hy; exact hy.symm
    · right; rw [d_ne m h] at hy
      exact ⟨_, cls_lt m _ _, hy.symm⟩
  · rintro (rfl | ⟨r, hr, rfl⟩)
    · exact ⟨le_rfl, fun p => ⟨p, dist_self p⟩⟩
    · refine ⟨by linarith [(frac_bounds m r hr).1], fun p => ?_⟩
      obtain ⟨y, hne, hy⟩ := cls_cover m p r hr
      refine ⟨(y : Space m), ?_⟩
      change d m y p = _
      rw [d_ne m hne, cls_comm, hy]

private lemma center_card : Nat.card (center (Space m)) = 2 * m + 2 := by
  let g : ℕ → ℝ := fun r => 1 + (r : ℝ) / (2 * m + 2)
  have hinj : Set.InjOn g (Finset.range (2 * m + 1) : Set ℕ) := by
    intro a _ b _ h
    have hpos : (0 : ℝ) < 2 * m + 2 := by positivity
    have : (a : ℝ) = b := by
      simp only [g, add_right_inj] at h
      field_simp at h
      exact h
    exact_mod_cast this
  have h0 : (0 : ℝ) ∉ (Finset.range (2 * m + 1)).image g := by
    intro h
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp h
    have := (frac_bounds m r (by simpa using ‹r ∈ Finset.range (2 * m + 1)›)).1
    simp only [g] at hr
    linarith
  have hC : center (Space m) = ↑(insert 0 ((Finset.range (2 * m + 1)).image g)) := by
    ext t
    rw [center_iff]
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

private lemma complete : centralGraph (Space m) = ⊤ := by
  ext x y
  simp only [centralGraph, SimpleGraph.fromRel_adj, SimpleGraph.top_adj]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, Or.inl ?_⟩
    rw [center_iff]
    right
    change ∃ r < 2 * m + 1, d m x y = _
    exact ⟨_, cls_lt m _ _, d_ne m h⟩

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
      · exact (Fintype.card_fin (2 * m + 2)).trans (by ring)
      · rw [center_card]; ring

end

end D5.S3.Combinatorics.Geometry.CompleteCentralParity
