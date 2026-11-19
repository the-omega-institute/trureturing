/- GID: D5/S3/Combinatorics/Geometry/MinimumCentralOrder
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/MinimumCentralOrder
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: The least order of a k-central metric space is 1, k or k+1 by the parity of k. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#322; delivered and
  first frozen together with CompleteCentralParity and CentralSizeEdgeMinima)
escape_witness: CompleteCentralParity.band_center_card at Band (2m+2) (k-1) (cls m), the space
  with 2m+2 points and k central values (same delivery, not previously frozen).
proof_shape:
  center_card_bound: bind-only helper (edge_cover_bound with
    SimpleGraph.card_edgeFinset_le_card_choose_two and arithmetic); consumers: minimum_order,
    CentralSizeEdgeMinima.all_center_sizes.
  minimum_order: content; attainment runs through band_center_card on its live path.
Direct frozen dependencies: D5/S3/Combinatorics/Geometry/CentralEdgeCover (edge_cover_bound),
  D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges (center, centralGraph).
Same-delivery dependencies: D5/S3/Combinatorics/Geometry/CompleteCentralParity (Band, cls,
  space_cov, band_card, band_center_card, third_point, cls_lt).
Search record (§3.1): an earlier draft copied the round-robin metric with a cap; it now reuses
  the band of CompleteCentralParity. No frozen module bounds the number of central values.
-/

import D5.S3.Combinatorics.Geometry.CompleteCentralParity

/-! # Minimum order of a `k`-central metric space

The least number of points of a nonempty finite metric space with exactly `k ≥ 1` central
values (zero included) is `1` for `k = 1`, `k` for even `k`, and `k + 1` for odd `k ≥ 3`.
The edge-cover bound against the number of pairs gives `k ≤ n`, and `k ≤ n - 1` for odd
`n ≥ 3`. A round-robin band space with `k - 1` central classes attains every bound.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Geometry.MinimumCentralOrder

open D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges
open D5.S3.Combinatorics.Geometry.CentralEdgeCover
open D5.S3.Combinatorics.Geometry.CompleteCentralParity

noncomputable section

/-- A nonempty finite metric space has at most as many central values as points, and at most
one fewer when the order is odd and at least three. -/
lemma center_card_bound (X : Type) [Fintype X] [MetricSpace X] (hX : 1 ≤ Fintype.card X) :
    Nat.card (center X) ≤ Fintype.card X ∧
      (Odd (Fintype.card X) → 3 ≤ Fintype.card X → Nat.card (center X) < Fintype.card X) := by
  classical
  have hb := (edge_cover_bound X).trans
    (SimpleGraph.card_edgeFinset_le_card_choose_two (G := centralGraph X))
  rw [Nat.choose_two_right] at hb
  generalize Nat.card (center X) = k at hb ⊢
  generalize Fintype.card X = n at hb hX ⊢
  rcases Nat.even_or_odd' n with ⟨h, rfl | rfl⟩
  · obtain ⟨h, rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    have e1 : (2 * (h + 1) + 1) / 2 = h + 1 := by omega
    have e2 : 2 * (h + 1) * (2 * (h + 1) - 1) / 2 = (h + 1) * (2 * h + 1) := by
      rw [show 2 * (h + 1) * (2 * (h + 1) - 1) = 2 * ((h + 1) * (2 * h + 1)) by
        rw [show 2 * (h + 1) - 1 = 2 * h + 1 by omega]; ring,
        Nat.mul_div_cancel_left _ (by norm_num)]
    rw [e1, e2] at hb
    refine ⟨?_, fun ho => absurd ho (by rw [Nat.not_odd_iff_even]; exact ⟨h + 1, by ring⟩)⟩
    rw [mul_comm (h + 1)] at hb
    have : k - 1 ≤ 2 * h + 1 := Nat.le_of_mul_le_mul_right hb (Nat.succ_pos h)
    omega
  · have e1 : (2 * h + 1 + 1) / 2 = h + 1 := by omega
    have e2 : (2 * h + 1) * (2 * h + 1 - 1) / 2 = (2 * h + 1) * h := by
      rw [show 2 * h + 1 - 1 = 2 * h by omega, show (2 * h + 1) * (2 * h) = 2 * ((2 * h + 1) * h)
        by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [e1, e2] at hb
    have key : h = 0 ∨ k ≤ 2 * h := by
      rcases Nat.eq_zero_or_pos h with h0 | hpos
      · exact Or.inl h0
      · right
        by_contra hlt
        have : (2 * h) * (h + 1) ≤ (k - 1) * (h + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        nlinarith
    rcases key with h0 | hk
    · subst h0
      simp only [mul_zero, zero_add, mul_one, Nat.le_zero] at hb
      exact ⟨by omega, fun _ h3 => by omega⟩
    · exact ⟨by omega, fun _ _ => by omega⟩

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
      refine ⟨Band 1 0 (cls 0), inferInstance, inferInstance, ⟨(⟨0, by omega⟩ : Fin 1)⟩,
        band_card _ _ _, ?_⟩
      exact band_center_card _ _ _ (by omega) (fun _ r hr => absurd hr (by omega))
        (fun x y hxy _ => absurd (Subsingleton.elim x y) hxy)
    · simp only [hk1, ↓reduceIte]
      set m := (k - 1) / 2 with hm
      refine ⟨Band (2 * m + 2) (k - 1) (cls m), inferInstance, inferInstance,
        ⟨(⟨0, by omega⟩ : Fin (2 * m + 2))⟩, ?_, ?_⟩
      · rw [band_card]
        split_ifs with he
        · obtain ⟨j, rfl⟩ := he; omega
        · rcases Nat.even_or_odd k with h | ⟨j, rfl⟩
          · exact absurd h he
          · omega
      · rw [band_center_card _ _ _ (by omega)
          (fun x r hr => space_cov m x r (by omega)) (fun x y _ hc => ?_)]
        · omega
        · have := cls_lt m (min x.1 y.1) (max x.1 y.1)
          exact third_point _ (by unfold plab at hc; omega) x y
  · rintro n ⟨X, _, _, _, rfl, hc⟩
    obtain ⟨hle, hodd⟩ := center_card_bound X Fintype.card_pos
    rw [hc] at hle hodd
    split_ifs with hk1 he
    · exact Fintype.card_pos
    · exact hle
    · rcases Nat.even_or_odd (Fintype.card X) with h | h
      · rcases Nat.even_or_odd k with hk' | hk'
        · exact absurd hk' he
        · have : k ≠ Fintype.card X := fun e => (Nat.not_even_iff_odd.mpr hk') (e ▸ h)
          omega
      · have h3 : 3 ≤ Fintype.card X := by
          rcases Nat.even_or_odd k with hk' | ⟨j, hj⟩
          · exact absurd hk' he
          · omega
        have := hodd h h3
        omega

end

end D5.S3.Combinatorics.Geometry.MinimumCentralOrder
