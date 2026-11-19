/- GID: D5/S3/Combinatorics/Geometry/MinimumCentralOrder
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/MinimumCentralOrder
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: The least order of a k-central metric space is 1, k or k+1 by the parity of k. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#322)
escape_witness: center_card_le (central values never outnumber points, and equality makes the
  central graph complete) with center_card (the capped round-robin space has c+2 central values)
proof_shape:
  d, Capped: definitions; consumers: the lemmas below and minimum_order.
  center_card_le, center_iff, center_card: content; consumer: minimum_order.
  center_sub_range, d_self, d_ne, d_bounds, d_comm: bind-only helpers; consumers: the metric
    instance, center_card_le, center_iff, center_card.
  minimum_order: content; the odd lower bound reads the forward direction of
    complete_central_iff at the equality case of center_card_le.
Direct frozen dependencies: D5/S3/Combinatorics/Geometry/CompleteCentralParity (cls, cls_lt,
  cls_comm, cls_cover, frac_bounds, complete_central_iff),
  D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges (center, centralGraph).
Search record (§3.1): CompleteCentralParity.Space is the uncapped case c = 2m and only gives
  even orders; no frozen module bounds the number of central values by the order or builds a
  space with a prescribed number of central values below the order.
-/

import D5.S3.Combinatorics.Geometry.CompleteCentralParity

/-! # Minimum order of a `k`-central metric space

The least number of points of a nonempty finite metric space with exactly `k ≥ 1` central
values (zero included) is `1` for `k = 1`, `k` for even `k`, and `k + 1` for odd `k ≥ 3`.
A space never has more central values than points; when the two counts agree every distance is
central, so the central graph is complete and the parity classification excludes odd orders
above one. A round-robin space with the class index capped at `k - 2` attains every bound.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Geometry.MinimumCentralOrder

open D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges
open D5.S3.Combinatorics.Geometry.CompleteCentralParity

noncomputable section

/-- The central values are the distances to a fixed point that every point realizes. -/
private lemma center_sub_range (X : Type) [MetricSpace X] (p : X) :
    center X ⊆ Set.range fun y => dist y p := fun _ ht => ht.2 p

/-- A finite metric space has at most as many central values as points, and if the counts
agree, every distance is central. -/
private lemma center_card_le (X : Type) [Fintype X] [MetricSpace X] [Nonempty X] :
    Nat.card (center X) ≤ Fintype.card X ∧
      (Nat.card (center X) = Fintype.card X → centralGraph X = ⊤) := by
  have hrange : ∀ p : X, (Set.range fun y => dist y p).ncard ≤ Fintype.card X := fun p => by
    rw [← Set.image_univ, ← Nat.card_eq_fintype_card, ← Set.ncard_univ]
    exact Set.ncard_image_le (Set.toFinite _)
  have hle : ∀ p : X, Nat.card (center X) ≤ Fintype.card X := fun p => by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_le_ncard (center_sub_range X p) (Set.toFinite _)).trans (hrange p)
  obtain ⟨p⟩ := ‹Nonempty X›
  refine ⟨hle p, fun heq => ?_⟩
  have hfull : ∀ q : X, center X = Set.range fun y => dist y q := fun q =>
    Set.eq_of_subset_of_ncard_le (center_sub_range X q)
      ((hrange q).trans (by rw [← heq, Nat.card_coe_set_eq])) (Set.toFinite _)
  ext x y
  simp only [centralGraph, SimpleGraph.fromRel_adj, SimpleGraph.top_adj]
  refine ⟨fun h => h.1, fun h => ⟨h, Or.inl ?_⟩⟩
  rw [hfull y]
  exact ⟨x, rfl⟩

variable (m c : ℕ)

/-- Distinct points are at distance `1 + min(r, c) / (2m+2)`, where `r` is their round-robin
class. -/
private def d (x y : Fin (2 * m + 2)) : ℝ :=
  if x = y then 0 else 1 + (min (cls m x.1 y.1) c : ℝ) / (2 * m + 2)

private lemma d_self (x : Fin (2 * m + 2)) : d m c x x = 0 := by
  unfold d; simp only [↓reduceIte]

private lemma d_ne {x y : Fin (2 * m + 2)} (h : x ≠ y) :
    d m c x y = 1 + (min (cls m x.1 y.1) c : ℝ) / (2 * m + 2) := by
  unfold d; simp only [h, ↓reduceIte]

private lemma d_bounds {x y : Fin (2 * m + 2)} (h : x ≠ y) :
    1 ≤ d m c x y ∧ d m c x y < 2 := by
  rw [d_ne m c h]
  have := frac_bounds m (min (cls m x.1 y.1) c)
    (lt_of_le_of_lt (min_le_left _ _) (cls_lt m x.1 y.1))
  push_cast at this
  constructor <;> linarith

private lemma d_comm (x y : Fin (2 * m + 2)) : d m c x y = d m c y x := by
  by_cases h : x = y
  · subst h; rfl
  · rw [d_ne m c h, d_ne m c (Ne.symm h), cls_comm]

/-- The points of `Fin (2m+2)` with the round-robin metric capped at class `c`. -/
def Capped (m _c : ℕ) : Type := Fin (2 * m + 2)

instance : Fintype (Capped m c) := inferInstanceAs (Fintype (Fin (2 * m + 2)))

instance : Nonempty (Capped m c) := inferInstanceAs (Nonempty (Fin (2 * m + 2)))

noncomputable instance : MetricSpace (Capped m c) where
  dist x y := d m c x y
  dist_self x := d_self m c x
  dist_comm x y := d_comm m c x y
  dist_triangle x y z := by
    show d m c x z ≤ d m c x y + d m c y z
    by_cases hxz : x = z
    · subst hxz
      have h0 : d m c x x = 0 := d_self m c x
      rw [h0]
      by_cases hxy : x = y
      · subst hxy; rw [h0]; norm_num
      · have := (d_bounds m c hxy).1; have := (d_bounds m c (Ne.symm hxy)).1; linarith
    · have h1 := (d_bounds m c hxz).2
      by_cases hxy : x = y
      · subst hxy; rw [show d m c x x = 0 from d_self m c x, zero_add]
      · by_cases hyz : y = z
        · subst hyz; rw [show d m c y y = 0 from d_self m c y, add_zero]
        · have := (d_bounds m c hxy).1; have := (d_bounds m c hyz).1; linarith
  eq_of_dist_eq_zero {x y} h := by
    by_contra hne
    have := (d_bounds m c hne).1
    change d m c x y = 0 at h
    linarith

private lemma center_iff (hc : c < 2 * m + 1) (t : ℝ) :
    t ∈ center (Capped m c) ↔ t = 0 ∨ ∃ r ≤ c, t = 1 + (r : ℝ) / (2 * m + 2) := by
  constructor
  · rintro ⟨_, ht⟩
    obtain ⟨y, hy⟩ := ht (⟨0, by omega⟩ : Fin (2 * m + 2))
    change d m c y ⟨0, by omega⟩ = t at hy
    by_cases h : y = (⟨0, by omega⟩ : Fin (2 * m + 2))
    · left; rw [h, d_self] at hy; exact hy.symm
    · right; rw [d_ne m c h] at hy
      exact ⟨_, min_le_right _ _, by rw [← hy]; push_cast; rfl⟩
  · rintro (rfl | ⟨r, hr, rfl⟩)
    · exact ⟨le_rfl, fun p => ⟨p, dist_self p⟩⟩
    · refine ⟨by linarith [(frac_bounds m r (by omega)).1], fun p => ?_⟩
      obtain ⟨y, hne, hy⟩ := cls_cover m p r (by omega)
      refine ⟨(y : Capped m c), ?_⟩
      change d m c y p = _
      rw [d_ne m c hne, cls_comm, hy, min_eq_left (by exact_mod_cast hr)]

private lemma center_card (hc : c < 2 * m + 1) : Nat.card (center (Capped m c)) = c + 2 := by
  let g : ℕ → ℝ := fun r => 1 + (r : ℝ) / (2 * m + 2)
  have hinj : Set.InjOn g (Finset.range (c + 1) : Set ℕ) := by
    intro a _ b _ h
    have hpos : (0 : ℝ) < 2 * m + 2 := by positivity
    have : (a : ℝ) = b := by
      simp only [g, add_right_inj] at h
      field_simp at h
      exact h
    exact_mod_cast this
  have h0 : (0 : ℝ) ∉ (Finset.range (c + 1)).image g := by
    intro h
    obtain ⟨r, hr, hr0⟩ := Finset.mem_image.mp h
    have := (frac_bounds m r (by simp at hr; omega)).1
    simp only [g] at hr0
    linarith
  have hC : center (Capped m c) = ↑(insert 0 ((Finset.range (c + 1)).image g)) := by
    ext t
    rw [center_iff m c hc]
    simp only [Finset.coe_insert, Finset.coe_image, Finset.coe_range, Set.mem_insert_iff,
      Set.mem_image, Set.mem_Iio, g, Nat.lt_succ_iff]
    constructor
    · rintro (h | ⟨r, hr, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨r, hr, h.symm⟩
    · rintro (h | ⟨r, hr, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨r, hr, h.symm⟩
  rw [hC, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_insert_of_notMem h0,
    Finset.card_image_of_injOn hinj, Finset.card_range]

/-- For `k ≥ 1`, the least order of a nonempty finite metric space with exactly `k` central
values is `1` when `k = 1`, `k` when `k` is even, and `k + 1` when `k ≥ 3` is odd. -/
theorem minimum_order (k : ℕ) (hk : 1 ≤ k) :
    IsLeast {n : ℕ | ∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X), Nonempty X ∧
        Fintype.card X = n ∧ Nat.card (center X) = k}
      (if k = 1 then 1 else if Even k then k else k + 1) := by
  constructor
  · by_cases hk1 : k = 1
    · subst hk1
      simp only [↓reduceIte]
      obtain ⟨X, hF, hM, hX, hc, -⟩ :=
        (complete_central_iff 1 le_rfl).mpr (Or.inl rfl)
      exact ⟨X, hF, hM, Fintype.card_pos_iff.mp (by omega), hX, hc⟩
    · simp only [hk1, ↓reduceIte]
      refine ⟨Capped ((k - 1) / 2) (k - 2), inferInstance, inferInstance, inferInstance, ?_, ?_⟩
      · change Fintype.card (Fin _) = _
        rw [Fintype.card_fin]
        split_ifs with he
        · obtain ⟨j, rfl⟩ := he; omega
        · rcases Nat.even_or_odd k with h | ⟨j, rfl⟩
          · exact absurd h he
          · omega
      · rw [center_card _ _ (by omega)]
        omega
  · rintro n ⟨X, _, _, _, rfl, hc⟩
    obtain ⟨hle, hall⟩ := center_card_le X
    rw [hc] at hle hall
    split_ifs with hk1 he
    · exact Fintype.card_pos
    · exact hle
    · by_contra hlt
      have heq : k = Fintype.card X := by omega
      have htop := hall heq
      rcases (complete_central_iff (Fintype.card X) (by omega)).mp
          ⟨X, inferInstance, inferInstance, rfl, by rw [hc, heq], htop⟩ with h | h
      · omega
      · exact he (heq ▸ h)

end

end D5.S3.Combinatorics.Geometry.MinimumCentralOrder
