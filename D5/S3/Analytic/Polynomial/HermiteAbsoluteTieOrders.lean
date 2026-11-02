/- GID: D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact exhaustive orders with two maximal absolute Hermite coefficients. -/

import D5.S3.Analytic.Polynomial.HermiteAbsoluteMode

/-! Two absolute maxima in the original physicists Hermite coefficient row. -/

namespace D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders

open HermiteSignedMode HermiteAbsoluteMode

/-- Absolute maximality over every exponent from zero through the order. -/
def IsAbsMax (k j : ℕ) : Prop :=
  j ≤ k ∧ ∀ i, i ≤ k →
    |(physicistsHermite k).coeff i| ≤ |(physicistsHermite k).coeff j|

/-- Exactly two distinct maximizing exponents in the complete coefficient row. -/
def HasExactlyTwo (k : ℕ) : Prop :=
  ∃ u v : ℕ, u < v ∧ ∀ j : ℕ, IsAbsMax k j ↔ j = u ∨ j = v

/-- The source formula, with a positive one-based natural index and integer arithmetic. -/
def a (n : ℕ) : ℤ :=
  2 * (n : ℤ) * ((n : ℤ) + 2) + ((n : ℤ) + 1) * (-1 : ℤ) ^ (n + 1)

/-- Positive, strictly increasing, and exhaustive one-based enumeration. -/
def claim : Prop :=
  (∀ n : ℕ, 1 ≤ n → 0 < a n) ∧
  (∀ n m : ℕ, 1 ≤ n → n < m → a n < a m) ∧
  ∀ k : ℕ, HasExactlyTwo k ↔ ∃! n : ℕ, 1 ≤ n ∧ (k : ℤ) = a n

private theorem max_iff_weight (k j : ℕ) :
    IsAbsMax k j ↔ ∃ r : ℕ, 2 * r ≤ k ∧ j = k - 2 * r ∧
      weight k r = weight k (mode k) := by
  have hm := (mode_rises k).1
  have hp := weight_pos k (mode k) hm
  constructor
  · intro h
    have htop := h.2 (k - 2 * mode k) (Nat.sub_le _ _)
    rw [polynomial_coeff k _ (Nat.sub_le _ _), polynomial_coeff k j h.1] at htop
    change weight k (mode k) ≤ |signedCoeff k j| at htop
    rcases coefficient_cases k j with hz | ⟨r, hr, hj, hw⟩
    · rw [hz] at htop
      linarith
    · exact ⟨r, hr, hj, le_antisymm (weight_le_mode k r hr) (hw ▸ htop)⟩
  · rintro ⟨r, hr, rfl, he⟩
    refine ⟨Nat.sub_le _ _, ?_⟩
    intro i hi
    rw [polynomial_coeff k i hi, polynomial_coeff k _ (Nat.sub_le _ _)]
    change |signedCoeff k i| ≤ weight k r
    rw [he]
    rcases coefficient_cases k i with hz | ⟨s, hs, hj, hw⟩
    · rw [hz]; exact hp.le
    · rw [hw]; exact weight_le_mode k s hs

private theorem strict_before (k r : ℕ) (hr : r + 1 < mode k) :
    weight k r < weight k (r + 1) := by
  have hm := mode_rises k
  have hdom : 2 * (r + 1) ≤ k := by omega
  have hcomp := second_mono (show k - 2 * mode k ≤ k - 2 * (r + 1) by omega)
  have ht : 4 * (r + 1) < second (k - 2 * (r + 1)) := by omega
  have htq : (4 * (r + 1) : ℚ) < second (k - 2 * (r + 1)) := by exact_mod_cast ht
  have hw := weight_pos k r (by omega)
  have he := adjacent k r hdom
  have hd : (0 : ℚ) < 4 * (r + 1) := by positivity
  nlinarith

private theorem equal_mode_indices (k r : ℕ) (hr : 2 * r ≤ k)
    (he : weight k r = weight k (mode k)) :
    r = mode k ∨ r + 1 = mode k := by
  have hle : r ≤ mode k := by
    by_contra h
    have := weight_lt_mode k r hr (by omega)
    linarith
  by_cases h : r + 1 < mode k
  · have hs := strict_before k r h
    have ht := weight_le_mode k (r + 1) (by have := (mode_rises k).1; omega)
    linarith
  · omega

private theorem adjacent_equal (k r : ℕ) (hr : 2 * (r + 1) ≤ k) :
    weight k r = weight k (r + 1) ↔
      second (k - 2 * (r + 1)) = 4 * (r + 1) := by
  have he := adjacent k r hr
  have hp := weight_pos k r (by omega)
  have hd : (0 : ℚ) < 4 * (r + 1) := by positivity
  constructor
  · intro hh
    rw [← hh] at he
    have : (second (k - 2 * (r + 1)) : ℚ) = 4 * (r + 1) := by nlinarith
    exact_mod_cast this
  · intro hh
    have : (second (k - 2 * (r + 1)) : ℚ) = 4 * (r + 1) := by exact_mod_cast hh
    rw [this] at he
    nlinarith

private theorem tie_is_mode (k r : ℕ) (hr : 1 ≤ r) (hk : 2 * r ≤ k)
    (he : second (k - 2 * r) = 4 * r) : r = mode k := by
  have hle : r ≤ mode k := le_mode ⟨hk, he.ge⟩
  have hm := mode_rises k
  have hc := second_mono (show k - 2 * mode k ≤ k - 2 * r by omega)
  omega

private theorem tie_characterization (k : ℕ) :
    HasExactlyTwo k ↔ ∃ r : ℕ, 1 ≤ r ∧ 2 * r ≤ k ∧
      second (k - 2 * r) = 4 * r := by
  constructor
  · rintro ⟨u, v, huv, h⟩
    obtain ⟨r, hr, hu, her⟩ := (max_iff_weight k u).mp ((h u).mpr (Or.inl rfl))
    obtain ⟨s, hs, hv, hes⟩ := (max_iff_weight k v).mp ((h v).mpr (Or.inr rfl))
    have hri := equal_mode_indices k r hr her
    have hsi := equal_mode_indices k s hs hes
    have hsr : s < r := by omega
    have hrr : r = mode k := by omega
    have hss : s + 1 = r := by omega
    refine ⟨r, by omega, hr, ?_⟩
    have heq : weight k s = weight k (s + 1) := by rw [hss, hrr]; exact hes
    have ht := (adjacent_equal k s (by omega)).mp heq
    simpa only [hss] using ht
  · rintro ⟨r, hr, hk, he⟩
    have hm := tie_is_mode k r hr hk he
    have heq : weight k (r - 1) = weight k r := by
      have hh : r - 1 + 1 = r := by omega
      simpa only [hh] using (adjacent_equal k (r - 1) (by omega)).mpr (by simpa only [hh] using he)
    refine ⟨k - 2 * r, k - 2 * (r - 1), by omega, ?_⟩
    intro j
    rw [max_iff_weight]
    constructor
    · rintro ⟨s, hs, hj, hes⟩
      have hi := equal_mode_indices k s hs hes
      rcases hi with hi | hi
      · left; omega
      · right; omega
    · rintro (rfl | rfl)
      · exact ⟨r, hk, rfl, by rw [← hm]⟩
      · exact ⟨r - 1, by omega, rfl, by rw [← hm]; exact heq⟩

end D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders
